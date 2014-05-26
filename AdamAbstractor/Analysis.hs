{-#LANGUAGE TupleSections, GADTs, RecordWildCards, NoMonomorphismRestriction #-}
module AdamAbstractor.Analysis (
    VarInfo(..),
    Return(..),
    abstract,
    binExprToAST,
    TheVarType,
    TheVarType',
    ValType,
    getBits,
    passValTSL3,
    equalityConst
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

import AdamAbstractor.AST as AST
import AdamAbstractor.Predicate
import AdamAbstractor.Backend as Backend

import Synthesis.Interface hiding (VarInfo, NonAbs)

--Utility functions
if' True  x y = x
if' False x y = y

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

    --TODO: slice ignored for unabstracted variables
    makePred' (Left (VarInfo x NonAbs sz sect slice)) 
             (Right y) 
             = Right $ Backend.EqConst (Right (eSectVar sect x sz)) y

    makePred' (Right y) 
             (Left (VarInfo x Abs sz sect slice))
             = Right $ varEqOne2 $ eSectConstPred sect x slice y 

    --TODO: slice ignored for unabstracted variables
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
absBOpToTSLBOp AST.Imp = Backend.Imp

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

--must at least always have an outgoing
handleValPred2 :: f -> AST v c (Either (Leaf f TheVarType) ValType) -> Maybe (Int, Int) -> AST v c (Either (Leaf f TheVarType) ValType) -> Maybe (Int, Int) -> AST v c (Leaf f TheVarType)
handleValPred2 f x sx y sy = XNor (eqConst (Left f) 1) $ fmap (either id id) $ makePred <$$> (sliceValType sx <$$> x) <**> (sliceValType sy <$$> y)

equalityConst :: f -> AST v c (Either (Leaf f TheVarType) ValType) -> Maybe (Int, Int) -> Int -> AST v c (Leaf f TheVarType)
equalityConst f x sx y = XNor (eqConst (Left f) 1) $ fmap (either id id) $ func y <$$> x 
    where
    func const (Left (VarInfo x Abs    sz sect slice)) = varEqOne2 $ eSectConstPred sect x slice const
    --TODO: slice ignored for unabstracted variables
    func const (Left (VarInfo x NonAbs sz sect slice)) = Backend.EqConst (Right (eSectVar sect x sz)) const
    func const (Right const2)                          = ConstLeaf $ if' (const == const2) True False

sliceValType :: Maybe(Int, Int) -> ValType -> ValType 
sliceValType slice (Left varInfo) = Left $ sliceVarInfo slice varInfo
sliceValType slice (Right int)    = Right (getBits slice int)

sliceVarInfo :: Maybe (Int, Int) -> VarInfo -> VarInfo
sliceVarInfo Nothing        varInfo = varInfo 
sliceVarInfo s@(Just(l, u)) varInfo = varInfo {sz = u - l + 1, slice = restrict s (slice varInfo)}

--TODO: slice ignored for unabstracted vars
passValTSL3 :: AST v c (Either (Leaf f TheVarType) ValType) -> f -> AST v c (Leaf f TheVarType)
passValTSL3 valE vars = fmap (either id id) $ f <$$> valE
    where
    f (Left (VarInfo name Abs    sz section slice)) = error "passValTSL3"
    f (Left (VarInfo name NonAbs sz section slice)) = Backend.EqVar (Left vars) (eSectVar section name sz)
    f (Right const)                                 = Backend.EqConst (Left vars) const
        
data Return f v c = Return {
    varsRet :: [String],
    abs2Ret :: String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> f -> AST v c (Leaf f TheVarType),
    astRet  :: String -> AST v c (Either (Leaf f TheVarType) ValType)
}

abstract :: CtrlExpr String (ASTEqPred ValType) ValType -> Either String (Return f v c)
abstract (AST.Signal var valExp) = return $ Return [] abs2 astRet
    where
    abs2   = error "abs2 called on signal"
    astRet = error "not implemented"
abstract (AST.Assign var valExp) = return $ Return [var] abs2 astRet
    where
    abs2 lv s1 rv s2 
        | var == lv && var == rv = error "abs2 on assignment"
        | otherwise              = error $ "Invariant broken: " ++ lv ++ " and " ++ rv ++ " are not assigned here"
    astRet varr 
        | var == varr = valExprToAST valExp
        | otherwise   = error "invariant broken: astRet"
abstract (AST.CaseC cases)  = join $ res <$> sequenceA subcases
    where
    subcases     = map (abstract . snd) cases
    res subcases = if' (all (==hd) rst) (return $ Return hd abs2 astR) (throwError "Different vars assigned in case branches")
        where
        (hd:rst)   = map (sort . varsRet) subcases
        caseabs2s  = map abs2Ret subcases
        conds      = map (binExprToAST . fst) cases
        abs2 lv s1 rv s2 = tsl 
            where
            rec   = map (\f -> f lv s1 rv s2) caseabs2s
            tsl v = Backend.Case $ zip conds (map (($ v)) rec)
        astR var 
            | var `elem` hd = Backend.Case $ zip conds recs
            | otherwise     = error $ "Invariant broken: " ++ var ++ " is not assigned in case"
                where
                conds = map (fmap Left . binExprToAST . fst) cases
                recs  = map (($ var) . astRet)               subcases

abstract (AST.Conj es) = join $ res <$> sequenceA rres
    where
    rres     = map abstract es
    res rres = if' (disjoint allVars) (return $ Return allVars abs2 astR) (throwError "Vars assigned in case statement are not disjoint")
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
        abs2 lv s1 rv s2
            | fst lres == fst rres  = abs2Ret (snd lres) lv s1 rv s2 
            | otherwise             = \f -> handleValPred2 f lASTRet s1 rASTRet s2
            where
            getRet var      = fromJustNote ("getIdent: " ++ var) $ Map.lookup var theMap
            lres            = getRet lv 
            rres            = getRet rv
            lASTRet         = astRet (snd lres) lv
            rASTRet         = astRet (snd rres) rv
        astR var
            | var `elem` allVars = astRet (snd $ fromJustNote "varsAssigned Conj" $ Map.lookup var theMap) var
            | otherwise          = error $ "Invariant broken: " ++ var ++ " is not assigned in CONJ"

--Slice a slice
--The second slice gets sliced by the first slice
restrict :: Slice -> Slice -> Slice
restrict Nothing          Nothing        = Nothing
restrict Nothing          (Just sl)      = Just sl
restrict (Just sl)        Nothing        = Just sl
restrict (Just (x1, x2)) (Just (y1, y2)) = Just (y1 + x1, y1 + x2)

--Slice an integer
getBits :: Slice -> Int -> Int
getBits Nothing x       = x
getBits (Just (l, u)) x = (shift (-l) x) .&. (2 ^ (u - l + 1) - 1)

