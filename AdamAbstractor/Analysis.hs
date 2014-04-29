{-#LANGUAGE TupleSections, GADTs, RecordWildCards, NoMonomorphismRestriction #-}
module AdamAbstractor.Analysis (
    VarInfo(..),
    Abs2Return(..),
    Return(..),
    abstract,
    binExprToAST,
    equalityConst,
    TheVarType,
    TheVarType',
    ValType,
    getBits,
    passValTSL3
    ) where

import Prelude hiding (sequence)
import Control.Applicative hiding ((<**>))
import Data.Traversable
import Control.Monad.Error hiding (sequence) 
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List
import Data.Maybe
import Control.Arrow
import Data.Bits

import Safe
import Data.Tuple.All
import Debug.TraceUtils

import AdamAbstractor.AST as AST
import AdamAbstractor.Predicate
import AdamAbstractor.Backend as Backend

import Interface hiding (VarInfo, NonAbs)

--Utility functions
if' True  x y = x
if' False x y = y

listsIntersect :: (Eq a) => [a] -> [a] -> Bool
listsIntersect l r = any (`elem` r) l

disjoint :: (Eq a) => [a] -> Bool
disjoint (hd:rst) = notElem hd rst && disjoint rst
disjoint []       = True

--the abstractor

data VarInfo = VarInfo {
    name    :: String,
    typ     :: VarAbsType,
    sz      :: Int,
    section :: Section,
    slice   :: Slice
}
type ValType = Either VarInfo Int

type TheVarType' = BAVar (VarType EqPred) (VarType LabEqPred)
type TheVarType  = (TheVarType', Maybe String)

fromRight (Right x) = x

varEqOne2 :: TheVarType -> Leaf f TheVarType
varEqOne2 x = Backend.EqConst (Right x) 1

--conversion to AST
makePred :: ValType -> ValType -> Leaf f TheVarType
makePred x y = fromRight $ makePred' x y
    where
    makePred' (Left (VarInfo x Abs sz sect slice))
             (Right y) 
             = Right $ varEqOne2 $ eSectConstPred sect x slice y 

    makePred' (Left (VarInfo x NonAbs sz sect slice)) 
             (Right y) 
             = Right $ Backend.EqConst (Right (eSectVar sect x sz)) y

    makePred' (Right y) 
             (Left (VarInfo x Abs sz sect slice))
             = Right $ varEqOne2 $ eSectConstPred sect x slice y 

    makePred' (Right y) 
             (Left (VarInfo x NonAbs sz sect slice))  
             = Right $ Backend.EqConst (Right (eSectVar sect x sz)) y

    makePred' (Left (VarInfo x Abs sz1 sect1 slice1)) 
             (Left (VarInfo y Abs sz2 sect2 slice2)) 
             = Right $ varEqOne2 $ eSectVarPred sect1 sect2 x slice1 y slice2

    makePred' (Left (VarInfo x NonAbs sz1 sect1 slice1)) 
             (Left (VarInfo y NonAbs sz2 sect2 slice2)) 
             = Right $ Backend.EqVar (Right (eSectVar sect1 x sz1)) (eSectVar sect2 y sz2 )

    makePred' (Left _)  
             (Left _)  
             = Left "handleValPred: Attempted to compare pred var and non-pred var"

    makePred' (Right x) 
             (Right y) 
             = Right $ ConstLeaf $ if' (x==y) True False

(<**>) = liftA2 (<*>)
(<$$>) = fmap . fmap

absBOpToTSLBOp AST.And = Backend.And
absBOpToTSLBOp AST.Or  = Backend.Or

binExprToAST :: BinExpr (ASTEqPred ValType) -> AST v c (Leaf f TheVarType)
binExprToAST TrueE                  = T
binExprToAST FalseE                 = F
binExprToAST (AST.Not x)            = Backend.Not $ binExprToAST x
binExprToAST (Bin op x y)           = absBOpToTSLBOp op (binExprToAST x) (binExprToAST y)
binExprToAST (AST.Pred (ASTEqPred AST.Eq x y))  = handleValPred x y
binExprToAST (AST.Pred (ASTEqPred AST.Neq x y)) = Backend.Not $ handleValPred x y

valExprToAST :: ValExpr (ASTEqPred ValType) ValType -> AST v c (Either (Leaf f TheVarType) ValType)
valExprToAST (Lit l)       = Leaf (Right l)
valExprToAST (CaseV cases) = Case $ zip conds recs
    where
    conds = map (fmap Left . binExprToAST . fst) cases
    recs  = map (valExprToAST . snd)             cases

handleValPred :: ValExpr (ASTEqPred ValType) ValType -> ValExpr (ASTEqPred ValType) ValType -> AST v c (Leaf f TheVarType)
handleValPred x y = fmap (either id id) $ makePred <$$> valExprToAST x <**> valExprToAST y

sliceValType :: Maybe(Int, Int) -> ValType -> ValType 
sliceValType slice (Left varInfo) = Left $ sliceVarInfo slice varInfo
sliceValType slice (Right int)    = Right (getBits slice int)

sliceVarInfo :: Maybe (Int, Int) -> VarInfo -> VarInfo
sliceVarInfo Nothing        varInfo = varInfo 
sliceVarInfo s@(Just(l, u)) varInfo = varInfo {sz = u - l + 1, slice = restrict s (slice varInfo)}

--TODO dont ignore slice
passValTSL3 :: AST v c (Either (Leaf f TheVarType) ValType) -> f -> AST v c (Leaf f TheVarType)
passValTSL3 valE vars = fmap (either id id) $ f <$$> valE
    where
    f (Left (VarInfo name Abs    sz section slice)) = error "passValTSL3"
    f (Left (VarInfo name NonAbs sz section slice)) = Backend.EqVar (Left vars) (eSectVar section name sz)
    f (Right const)                                 = Backend.EqConst (Left vars) const
        
--old
varEqOne :: TheVarType -> AST v c (Leaf f TheVarType)
varEqOne x = eqConst (Right x) 1

--fromJust map lookup
fjml k mp = fromJustNote "fjml" $ Map.lookup k mp

--Used to compile value expressions into TSL and NS preds containing the
--absVar argument as the NS element
valExprToTSL :: ValExpr (ASTEqPred ValType) ValType -> Abs1Return f v c
valExprToTSL (Lit (Left (VarInfo name Abs _ sect s1)))     = Abs1Return (const ($ Left (name, sect, s1))) [Left (name, sect, s1)] 
valExprToTSL (Lit (Left (VarInfo name NonAbs sz sect s1))) = error "valExprToTSL with a non-pred variable"
valExprToTSL (Lit (Right int))                             = Abs1Return (const ($ Right int)) [Right int] 
valExprToTSL (CaseV cases)                                 = Abs1Return tsl allPreds 
    where
    tsl c func = Case $ zip conds (zipWith f (map (($ func) . ($ c) . abs1Tsl) ccases) (map abs1Preds ccases))
        where
        f tslcase preds = Backend.Conj $ if' c (map (Backend.Not . func) (allPreds \\ preds)) [] ++ [tslcase]
    conds    = conds'
    ccases   = map (valExprToTSL . snd) cases
    conds'   = map (binExprToAST . fst) cases
    allPreds = nub $ concatMap abs1Preds ccases

data Abs1Return f v c = Abs1Return {
    --The update expressions
    abs1Tsl      :: Bool -> (Either (String, Section, Slice) Int -> AST v c (Leaf f TheVarType)) -> AST v c (Leaf f TheVarType),
    --List of vars that the variable being abstracted was compared to
    abs1Preds    :: [Either (String, Section, Slice) Int]
}

data Abs2Return f v c = Abs2Return {
    abs2Tsl   :: f -> AST v c (Leaf f TheVarType)
}

data Return f v c = Return {
    varsRet :: [String],
    abs1Ret :: String -> Abs1Return f v c,
    abs2Ret :: String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> Abs2Return f v c,
    astRet  :: String -> AST v c (Either (Leaf f TheVarType) ValType)
}

abstract :: CtrlExpr String (ASTEqPred ValType) ValType -> Either String (Return f v c)
abstract (AST.Signal var valExp) = return $ Return [] abs1 abs2 astRet
    where
    abs1   = error "abs1 called on signal"
    abs2   = error "abs2 called on signal"
    astRet = error "not implemented"
abstract (AST.Assign var valExp) = return $ Return [var] abs1 abs2 astRet
    where
    abs1 absVar
        | absVar == var = valExprToTSL valExp 
        | otherwise     = error $ "Invariant broken: " ++ var ++ " is not assigned here"
    abs2 lv s1 rv s2 
        | var == lv && var == rv = Abs2Return $ equalityValue lv s1 rv s2 (abs1 lv) (abs1 rv)
        | otherwise              = error $ "Invariant broken: " ++ lv ++ " and " ++ rv ++ " are not assigned here"
    astRet varr 
        | var == varr = valExprToAST valExp
        | otherwise   = error "invariant broken: astRet"
abstract (AST.CaseC cases)  = join $ res <$> sequenceA subcases
    where
    subcases     = map (abstract . snd) cases
    res subcases = if' (all (==hd) rst) (return $ Return hd abs1 abs2 astR) (throwError "Different vars assigned in case branches")
        where
        (hd:rst)   = map (sort . varsRet) subcases
        caseabs1s  = map abs1Ret subcases
        caseabs2s  = map abs2Ret subcases
        conds      = map (binExprToAST . fst) cases
        abs1 absVar 
            | absVar `elem` hd = Abs1Return tsl preds 
            | otherwise        = error $ "Invariant broken: " ++ absVar ++ " is not assigned in case"
                where
                abs1ress   = map ($ absVar) caseabs1s
                tsl c func = Backend.Case $ zip conds' $ map (uncurry f . (($ c) . abs1Tsl &&& abs1Preds))  abs1ress
                    where
                    f tslcase preds = Backend.Conj $ if' c (map (Backend.Not . func) (allPreds \\ preds)) [] ++ [tslcase func]
                conds'     = map (binExprToAST . fst) cases
                allPreds   = nub $ concatMap abs1Preds abs1ress
                preds      = nub $ concatMap abs1Preds abs1ress
        abs2 lv s1 rv s2 = Abs2Return tsl 
            where
            rec   = map (\f -> f lv s1 rv s2) caseabs2s
            tsl v = Backend.Case $ zip conds (map (($ v) . abs2Tsl) rec)
        astR var 
            | var `elem` hd = Backend.Case $ zip conds recs
            | otherwise     = error $ "Invariant broken: " ++ var ++ " is not assigned in case"
                where
                conds = map (fmap Left . binExprToAST . fst) cases
                recs  = map (($ var) . astRet)               subcases

abstract (AST.Conj es) = join $ res <$> sequenceA rres
    where
    rres     = map abstract es
    res rres = if' (disjoint allVars) (return $ Return allVars abs1 abs2 astR) (throwError "Vars assigned in case statement are not disjoint")
        where
        varsAssigned        = map varsRet rres
        allVars             = concat varsAssigned
        theMap              = createTheMap $ zip varsAssigned rres
        createTheMap :: [([String], Return f v c)] -> Map String (Int, Return f v c)
        createTheMap things = Map.unions $ map (uncurry f) (zipWith g things [0..])
            where
            f :: [String] -> (Int, Return f v c) -> Map String (Int, Return f v c)
            f vars func = Map.fromList (map (,func) vars)
            g :: (a, b) -> c -> (a, (c, b))
            g (x, y) z  = (x, (z, y))
        abs1 absVar 
            | absVar `elem` allVars = abs1Ret (snd $ fromJustNote "varsAssigned Conj" $ Map.lookup absVar theMap) absVar 
            | otherwise             = error $ "Invariant broken: " ++ absVar ++ " is not assigned in CONJ"
        abs2 lv s1 rv s2
            | fst lres == fst rres  = abs2Ret (snd lres) lv s1 rv s2 
            | otherwise             = Abs2Return tsl 
            where
            getRet var      = fromJustNote ("getIdent: " ++ var) $ Map.lookup var theMap
            lres            = getRet lv 
            rres            = getRet rv
            labs1ret        = abs1Ret (snd lres) lv
            rabs1ret        = abs1Ret (snd rres) rv
            tsl             = equalityValue lv s1 rv s2 labs1ret rabs1ret
        astR var
            | var `elem` allVars = astRet (snd $ fromJustNote "varsAssigned Conj" $ Map.lookup var theMap) var
            | otherwise          = error $ "Invariant broken: " ++ var ++ " is not assigned in CONJ"

doExists :: (Ord a) => [a] -> ((a -> AST v c (Leaf f x)) -> AST v c (Leaf f x)) -> AST v c (Leaf f x)
doExists vars func = doExists' vars Map.empty
    where
    doExists' [] accum     = func (flip fjml accum)
    doExists' (x:xs) accum = Exists $ \v -> doExists' xs (Map.insert x (QuantLit v) accum)

restrict :: Slice -> Slice -> Slice
restrict Nothing          Nothing        = Nothing
restrict Nothing          (Just sl)      = Just sl
restrict (Just sl)        Nothing        = Just sl
restrict (Just (x1, x2)) (Just (y1, y2)) = Just (x1 + y1, y1 + x2)

getBits :: Slice -> Int -> Int
getBits Nothing x       = x
getBits (Just (l, u)) x = (shift (-l) x) .&. (2 ^ (u - l + 1) - 1)

equalityValue :: String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> Abs1Return f v c -> Abs1Return f v c -> (f -> AST v c (Leaf f TheVarType))
equalityValue lv s1Var rv s2Var labs1ret rabs1ret = tsl
    where
    tsl v        = doExists allPreds (\mp -> Backend.Conj [abs1Tsl labs1ret True (mp . (lv,)), abs1Tsl rabs1ret True (mp . (rv,)), theExpr v mp])
    allPreds     = map (lv,) (abs1Preds labs1ret) ++ map (rv,) (abs1Preds rabs1ret)
    theExpr v mp = Backend.Disj (map Backend.Conj (map (map ($ mp) . ($ v)) tsls))
    cartProd     = [(x, y) | x <- abs1Preds labs1ret, y <- abs1Preds rabs1ret]
    tsls         = map (uncurry func) cartProd
        where
        func p1 p2 = (\v -> [($ (lv, p1)), ($ (rv, p2)), const $ XNor (eqConst (Left v) 1) tsl]) 
            where
            tsl = func' p1 p2
            func' (Left (r1, sect1, s1)) (Left (r2, sect2, s2))   
                | r1==r2 && restrict s1Var s1 == restrict s2Var s2 = T
                | otherwise                                        = varEqOne $ eSectVarPred sect1 sect2 r1 (restrict s1Var s1) r2 (restrict s2Var s2)
            func' (Left (r1, sect, s1)) (Right r2)                 = varEqOne $ eSectConstPred sect r1 (restrict s1Var s1) r2 
            func' (Right r1)            (Left (r2, sect, s2))      = varEqOne $ eSectConstPred sect r2 (restrict s2Var s2) r1 
            func' (Right r1)            (Right r2)                 = if' (getBits s1Var r1 == getBits s2Var r2) T F 

equalityConst :: Abs1Return f v c -> Maybe (Int, Int) -> Int -> f -> AST v c (Leaf f TheVarType)
equalityConst Abs1Return{..} s int v = abs1Tsl False func
    where
    --Argument of func is the value of the variable represented by the Abs1Return has been asigned to
    func (Left (name, sect, sl)) = eqConst (Left v) 1 `Backend.XNor` varEqOne (eSectConstPred sect name (restrict s sl) int)
    func (Right c)               = eqConst (Left v) 1 `Backend.XNor` if' (getBits s c == int) T F 

