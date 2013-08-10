{-#LANGUAGE TupleSections, GADTs, RecordWildCards #-}
module AdamAbstractor.Analysis (
    VarInfo(..),
    Abs2Return(..),
    PassThroughReturn(..),
    Return(..),
    abstract,
    binExpToTSL,
    equalityConst,
    TheVarType,
    ValType,
    getBits
    ) where

import Prelude hiding (sequence)
import Control.Applicative
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

absBOpToTSLBOp AST.And = Backend.And
absBOpToTSLBOp AST.Or  = Backend.Or

singleton x = [x]

type TheVarType = BAVar (VarType EqPred) (VarType EqPred)

varEqOne :: TheVarType -> AST f v c TheVarType
varEqOne x = Backend.EqConst (Right x) 1

type ValType = Either VarInfo Int

--Takes two value expressions and returns the backend code that states that
--they are equal and the new predicates that are required to make this
--decision
handleValPred :: ValExpr ValType -> ValExpr ValType -> AST f v c TheVarType
handleValPred (Lit (Left (VarInfo x Abs _ sect s)))
              (Lit (Right y)) 
              = varEqOne $ eSectConstPred sect x s y 
handleValPred (Lit (Left (VarInfo x NonAbs sz sect _))) 
              (Lit (Right y)) 
              = Backend.EqConst (Right (eSectVar sect x sz)) y
handleValPred (Lit (Right y)) 
              (Lit (Left (VarInfo x Abs _ sect s)))
              = varEqOne $ eSectConstPred sect x s y 
handleValPred (Lit (Right y)) 
              (Lit (Left (VarInfo x NonAbs sz sect _)))  
              = Backend.EqConst (Right (eSectVar sect x sz)) y
handleValPred (Lit (Left (VarInfo x Abs _ sect1 s1))) 
              (Lit (Left (VarInfo y Abs _ sect2 s2))) 
              = varEqOne $ eSectVarPred sect1 sect2 x s1 y s2
handleValPred (Lit (Left (VarInfo x NonAbs sz1 sect1 _))) 
              (Lit (Left (VarInfo y NonAbs sz2 sect2 _))) 
              = Backend.EqVar (Right (eSectVar sect1 x sz1)) (eSectVar sect2 y sz2 )
handleValPred (Lit (Left _))  
              (Lit (Left _))  
              = error "handleValPred: Attempted to compare pred var and non-pred var"
handleValPred (Lit (Right x)) 
              (Lit (Right y)) 
              = if' (x==y) T F
{-
handleValPred l r                         = equalityValue "anon1" "anon2" (uncurryValExpToTSLRet Abs1Return lr) (uncurryValExpToTSLRet Abs1Return rr)
    where
    lr = valExprToTSL "anon1" l
    rr = valExprToTSL "anon2" r
-}

binExpToTSL :: BinExpr ValType -> AST f v c TheVarType
binExpToTSL TrueE                  = T
binExpToTSL FalseE                 = F
binExpToTSL (AST.Not x)            = Backend.Not $ binExpToTSL x
binExpToTSL (Bin op x y)           = absBOpToTSLBOp op (binExpToTSL x) (binExpToTSL y)
binExpToTSL (AST.Pred AST.Eq x y)  = handleValPred x y
binExpToTSL (AST.Pred AST.Neq x y) = Backend.Not $ handleValPred x y

--fromJust map lookup
fjml k mp = fromJustNote "fjml" $ Map.lookup k mp

--Used to compile value expressions into TSL and NS preds containing the
--absVar argument as the NS element
valExprToTSL :: ValExpr ValType -> Abs1Return f v c
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
    conds'   = map (binExpToTSL . fst) cases
    allPreds = nub $ concatMap abs1Preds ccases

passValTSL :: ValExpr ValType -> Either String (PassThroughReturn f v c)
passValTSL (Lit (Left (VarInfo var NonAbs sz sect _))) = return $ PassThroughReturn (\v -> Backend.EqVar (Left v) (eSectVar sect var sz)) [] [var]
passValTSL (Lit (Left (VarInfo var Abs _ sect _)))     = error "passValTSL: abstracted variable"
passValTSL (Lit (Right int))                           = return $ PassThroughReturn (\v -> Backend.EqConst (Left v) int) [int] []
passValTSL (CaseV cases)                               = f <$> sequence recs
    where
    conds  = map (binExpToTSL . fst) cases
    recs   = map (passValTSL . snd) cases
    f recs = PassThroughReturn tsl ints vars
        where
        tsl v = Case $ zip conds (map (($ v) . passTSL) recs) 
        ints  = nub $ concatMap passInts recs
        vars  = nub $ concatMap passVars recs

data Abs1Return f v c = Abs1Return {
    --The update expressions
    abs1Tsl      :: Bool -> (Either (String, Section, Slice) Int -> AST f v c TheVarType) -> AST f v c TheVarType,
    --List of vars that the variable being abstracted was compared to
    abs1Preds    :: [Either (String, Section, Slice) Int]
}

data Abs2Return f v c = Abs2Return {
    abs2Tsl   :: f -> AST f v c TheVarType
}

data PassThroughReturn f v c = PassThroughReturn {
    passTSL   :: f -> AST f v c TheVarType,
    passInts  :: [Int],
    passVars  :: [String]
}

data SignalReturn f v c = SignalReturn {
    sigPassTSL :: Either String (PassThroughReturn f v c),
    sigAbs1    :: Abs1Return f v c
}

data Return f v c = Return {
    varsRet :: [String],
    abs1Ret :: String -> Abs1Return f v c,
    abs2Ret :: String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> Abs2Return f v c,
    passRet :: String -> Either String (PassThroughReturn f v c),
    sigRet  :: String -> SignalReturn f v c
}

abstract :: CtrlExpr String ValType -> Either String (Return f v c)
abstract (AST.Signal var valExp) = return $ Return [] abs1 abs2 pass sig
    where
    abs1    = error "abs1 called on signal"
    abs2    = error "abs2 called on signal"
    pass    = error "pass called on signal"
    sig var = undefined --SignalReturn pass abs1
        where
        pass = passValTSL valExp
        abs1 = valExprToTSL valExp
abstract (AST.Assign var valExp) = return $ Return [var] abs1 abs2 pass sig
    where
    abs1 absVar
        | absVar == var = valExprToTSL valExp 
        | otherwise     = error $ "Invariant broken: " ++ var ++ " is not assigned here"
    abs2 = error "Invariant broken: abs2 called on an assignment"
    pass varr 
        | var == varr = passValTSL valExp
        | otherwise   = error "invariant broken: pass"
    sig = error "Invariant broken: sig called on assignment"
abstract (AST.CaseC cases)  = join $ res <$> sequenceA subcases
    where
    subcases     = map (abstract . snd) cases
    res subcases = if' (all (==hd) rst) (return $ Return hd abs1 abs2 pass sig) (throwError "Different vars assigned in case branches")
        where
        (hd:rst)   = map (sort . varsRet) subcases
        caseabs1s  = map abs1Ret subcases
        caseabs2s  = map abs2Ret subcases
        casePasses = map passRet subcases
        conds      = map (binExpToTSL . fst) cases
        abs1 absVar 
            | absVar `elem` hd = Abs1Return tsl preds 
            | otherwise        = error $ "Invariant broken: " ++ absVar ++ " is not assigned in case"
                where
                abs1ress   = map ($ absVar) caseabs1s
                tsl c func = Backend.Case $ zip conds' $ map (uncurry f . (($ c) . abs1Tsl &&& abs1Preds))  abs1ress
                    where
                    f tslcase preds = Backend.Conj $ if' c (map (Backend.Not . func) (allPreds \\ preds)) [] ++ [tslcase func]
                conds'     = map (binExpToTSL . fst) cases
                allPreds   = nub $ concatMap abs1Preds abs1ress
                preds      = nub $ concatMap abs1Preds abs1ress
        abs2 lv s1 rv s2 = Abs2Return tsl 
            where
            rec   = map (\f -> f lv s1 rv s2) caseabs2s
            tsl v = Backend.Case $ zip conds (map (($ v) . abs2Tsl) rec)
        pass var  = f <$> sequence rec
            where
            rec   = map ($ var) casePasses
            f rec = PassThroughReturn (\v -> Backend.Case $ zip conds (map (($ v) . passTSL) rec)) (nub $ concatMap passInts rec) (nub $ concatMap passVars rec)
        sig  = error "not implemented"
abstract (AST.Conj es) = join $ res <$> sequenceA rres
    where
    rres     = map abstract es
    res rres = if' (disjoint allVars) (return $ Return allVars abs1 abs2 pass sig) (throwError "Vars assigned in case statement are not disjoint")
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
            | fst lres == fst rres  = abs2 lv s1 rv s2 --TODO this cant possibly be right
            | otherwise             = Abs2Return tsl 
            where
            getRet var      = fromJustNote ("getIdent: " ++ var) $ Map.lookup var theMap
            lres            = getRet lv 
            rres            = getRet rv
            labs1ret        = abs1Ret (snd lres) lv
            rabs1ret        = abs1Ret (snd rres) rv
            tsl             = equalityValue lv s1 rv s2 labs1ret rabs1ret
        pass var = passRet (snd $ fromJustNote "pass conj" $ Map.lookup var theMap) var
        sig      = error "not implemented"

doExists :: (Ord a) => [a] -> ((a -> AST f v c x) -> AST f v c x) -> AST f v c x
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

equalityValue :: String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> Abs1Return f v c -> Abs1Return f v c -> (f -> AST f v c TheVarType)
equalityValue lv s1Var rv s2Var labs1ret rabs1ret = tsl
    where
    tsl v        = doExists allPreds (\mp -> Backend.Conj [abs1Tsl labs1ret True (mp . (lv,)), abs1Tsl rabs1ret True (mp . (rv,)), theExpr v mp])
    allPreds     = map (lv,) (abs1Preds labs1ret) ++ map (rv,) (abs1Preds rabs1ret)
    theExpr v mp = Backend.Disj (map Backend.Conj (map (map ($ mp) . ($ v)) tsls))
    cartProd     = [(x, y) | x <- abs1Preds labs1ret, y <- abs1Preds rabs1ret]
    tsls         = map (uncurry func) cartProd
        where
        func p1 p2 = (\v -> [($ (lv, p1)), ($ (rv, p2)), const $ XNor (Backend.EqConst (Left v) 1) tsl]) 
            where
            tsl = func' p1 p2
            func' (Left (r1, sect1, s1)) (Left (r2, sect2, s2))   
                | r1==r2 && restrict s1Var s1 == restrict s2Var s2 = T
                | otherwise                                        = varEqOne $ eSectVarPred sect1 sect2 r1 (restrict s1Var s1) r2 (restrict s2Var s2)
            func' (Left (r1, sect, s1)) (Right r2)                 = varEqOne $ eSectConstPred sect r1 (restrict s1Var s1) r2 
            func' (Right r1)            (Left (r2, sect, s2))      = varEqOne $ eSectConstPred sect r2 (restrict s2Var s2) r1 
            func' (Right r1)            (Right r2)                 = if' (getBits s1Var r1 == getBits s2Var r2) T F 

equalityConst :: Abs1Return f v c -> Maybe (Int, Int) -> Int -> f -> AST f v c TheVarType
equalityConst Abs1Return{..} s int v = abs1Tsl False func
    where
    --Argument of func is the value of the variable represented by the Abs1Return has been asigned to
    func (Left (name, sect, sl)) = Backend.EqConst (Left v) 1 `Backend.XNor` varEqOne (eSectConstPred sect name (restrict s sl) int)
    func (Right c)               = Backend.EqConst (Left v) 1 `Backend.XNor` if' (getBits s c == int) T F 

