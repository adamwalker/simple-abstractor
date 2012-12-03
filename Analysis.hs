{-#LANGUAGE TupleSections, GADTs #-}
module Analysis where

import Prelude hiding (sequence)
import Control.Applicative
import Data.Traversable
import Control.Monad.Error hiding (sequence) 
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List
import Data.Maybe
import Control.Arrow

import Safe
import Data.Tuple.All
import Debug.TraceUtils

import AST
import Predicate
import Backend

--Utility functions
if' True  x y = x
if' False x y = y

listsIntersect :: (Eq a) => [a] -> [a] -> Bool
listsIntersect l r = or $ map (`elem` r) l

disjoint :: (Eq a) => [a] -> Bool
disjoint (hd:rst) = not (hd `elem` rst) && disjoint rst
disjoint []       = True

--the abstractor

data VarInfo = VarInfo {
    name    :: String,
    typ     :: VarAbsType,
    section :: Section
}

absBOpToTSLBOp AST.And = Backend.And
absBOpToTSLBOp AST.Or  = Backend.Or

--Takes two value expressions and returns the backend code that states that
--they are equal and the new predicates that are required to make this
--decision
handleValPred :: ValExpr (Either VarInfo Int)  -> ValExpr (Either VarInfo Int) -> (AST f v c Predicate.Pred Predicate.Var, [EqPred])
handleValPred (Lit (Left (VarInfo x Abs sect)))         (Lit (Right y)) = (Backend.Pred (pred, sect), [pred]) where pred = constructConstPred x y
handleValPred (Lit (Left (VarInfo x (NonAbs _) sect)))  (Lit (Right y)) = (Backend.EqConst (Right (x, sect)) y, []) 
handleValPred (Lit (Right y)) (Lit (Left (VarInfo x Abs sect)))         = (Backend.Pred (pred, sect), [pred]) where pred = constructConstPred x y
handleValPred (Lit (Right y)) (Lit (Left (VarInfo x (NonAbs _) sect)))  = (Backend.EqConst (Right (x, sect)) y, []) 
handleValPred (Lit (Left (VarInfo x Abs sect1))) (Lit (Left (VarInfo y Abs sect2)))               = (Backend.Pred (pred, effectiveSection sect1 sect2), [pred]) where pred = constructVarPred x y
handleValPred (Lit (Left (VarInfo x (NonAbs _) sect1))) (Lit (Left (VarInfo y (NonAbs _) sect2))) = (Backend.EqVar (Right (x, sect1)) (y, sect2), []) 
handleValPred (Lit (Left _))  (Lit (Left _))  = error "handleValPred: Attempted to compare pred var and non-pred var"
handleValPred (Lit (Right x)) (Lit (Right y)) = (if' (x==y) T F, [])
{-
handleValPred l r                         = equalityValue "anon1" "anon2" (uncurryValExpToTSLRet Abs1Return lr) (uncurryValExpToTSLRet Abs1Return rr)
    where
    lr = valExprToTSL "anon1" l
    rr = valExprToTSL "anon2" r
    -}

binExpToTSL :: BinExpr (Either VarInfo Int) -> (AST f v c Predicate.Pred Predicate.Var, [EqPred])
binExpToTSL TrueE                  = (T, [])
binExpToTSL FalseE                 = (F, [])
binExpToTSL (AST.Not x)            = (Backend.Not (fst rec), snd rec) where rec = binExpToTSL x
binExpToTSL (Bin op x y)           = (absBOpToTSLBOp op (fst lr) (fst rr), nub $ snd lr ++ snd rr)
                                        where
                                        lr = binExpToTSL x 
                                        rr = binExpToTSL y
binExpToTSL (AST.Pred AST.Eq x y)  = handleValPred x y
binExpToTSL (AST.Pred AST.Neq x y) = (Backend.Not $ fst r, snd r) where r = handleValPred x y

nsPredToString :: NSEQPred -> String
nsPredToString (NsEqVar l r)   = "\"" ++ l ++ "'==" ++ r ++ "\""
nsPredToString (NsEqConst x c) = "\"" ++ x ++ "'==" ++ show c ++ "\""

data ValExprToTSLRet f v c = ValExprToTSLRet {
    valExpTSL   :: Map NSEQPred v -> AST f v c Predicate.Pred Predicate.Var,
    primedPreds :: [NSEQPred],
    newPreds    :: [EqPred]
}

uncurryValExpToTSLRet :: ((Map NSEQPred v -> AST f v c Predicate.Pred Predicate.Var) -> [NSEQPred] -> [EqPred] -> a) -> ValExprToTSLRet f v c -> a
uncurryValExpToTSLRet f (ValExprToTSLRet x y z) = f x y z

fjml k mp = fromJustNote "fjml" $ Map.lookup k mp

--Used to compile value expressions into TSL and NS preds containing the
--absVar argument as the NS element
valExprToTSL :: String -> ValExpr (Either VarInfo Int) -> ValExprToTSLRet f v c
valExprToTSL absVar = valExprToTSL'
    where
    valExprToTSL' (Lit (Left (VarInfo name Abs sect)))         = ValExprToTSLRet (\mp -> QuantLit $ fjml pred mp) [pred] [] where pred = NsEqVar absVar name
    valExprToTSL' (Lit (Left (VarInfo name (NonAbs _) sect)))  = error "valExprToTSL with a non-pred variable"
    valExprToTSL' (Lit (Right int)) = ValExprToTSLRet (\mp -> QuantLit $ fjml pred mp) [pred] [] where pred = NsEqConst absVar int
    valExprToTSL' (CaseV cases)     = ValExprToTSLRet tsl allPreds newPreds 
        where
        tsl mp = Case $ zip conds (map (uncurry f) (zip (map (($ mp) . valExpTSL) ccases) (map primedPreds ccases)))
            where
            f tslcase preds = Backend.Conj $ map (Backend.Not . QuantLit . flip fjml mp) (allPreds \\ preds) ++ [tslcase]
        conds  = map fst conds'
        ccases = map (valExprToTSL' . snd) cases
        conds' = map (binExpToTSL . fst) cases
        newPreds = nub $ concat $ map snd conds'
        allPreds = nub $ concat $ map primedPreds ccases

data PassValTSLRet f v c = PassValTSLRet {
    passValTSLTSL   :: f -> AST f v c Predicate.Pred Predicate.Var,
    passValTSLPreds :: [EqPred],
    passValTSLInts  :: [Int],
    passValTSLVars  :: [String]
}

passValTSL :: ValExpr (Either VarInfo Int) -> Either String (PassValTSLRet f v c)
passValTSL = passValTSL' 
    where
    passValTSL' (Lit (Left (VarInfo var (NonAbs _) sect))) = return $ PassValTSLRet (\v -> Backend.EqVar (Left v) (var, StateSection)) [] [] [var]
    passValTSL' (Lit (Left (VarInfo var Abs sect)))        = error "passValTSL: abstracted variable"
    passValTSL' (Lit (Right int)) = return $ PassValTSLRet (\v -> Backend.EqConst (Left v) int) [] [int] []
    passValTSL' (CaseV cases)     = f <$> sequence recs
        where
        conds  = map (binExpToTSL . fst) cases
        recs   = map (passValTSL' . snd) cases
        f recs = PassValTSLRet tsl preds ints vars
            where
            tsl v = Case $ zip (map fst conds) (map (($ v) . passValTSLTSL) recs) 
            preds = nub $ concat $ map snd conds ++ map passValTSLPreds recs
            ints  = nub $ concat $ map passValTSLInts recs
            vars  = nub $ concat $ map passValTSLVars recs

data Abs1Return f v c = Abs1Return {
    abs1Tsl       :: Map NSEQPred v -> AST f v c Predicate.Pred Predicate.Var,
    abs1Preds     :: [NSEQPred],
    abs1newPreds  :: [EqPred]
}

data Abs2Return f v c = Abs2Return {
    abs2Tsl   :: v -> AST f v c Predicate.Pred Predicate.Var,
    abs2Preds :: [EqPred]
}

data PassThroughReturn f v c = PassThroughReturn {
    passTSL   :: f -> AST f v c Predicate.Pred Predicate.Var,
    passPreds :: [EqPred],
    passInts  :: [Int],
    passVars  :: [String]
}

data SignalReturn f v c = SignalReturn {
    sigPassTSL :: PassThroughReturn f v c,
    sigAbs1    :: Abs1Return f v c
}

data Return f v c = Return {
    varsRet :: [String],
    abs1Ret :: String -> Abs1Return f v c,
    abs2Ret :: String -> String -> Abs2Return f v c,
    passRet :: String -> Either String (PassThroughReturn f v c)
}

abstract :: CtrlExpr String (Either VarInfo Int) -> Either String (Return f v c)
abstract (AST.Signal var valExp) = return $ Return [] abs1 abs2 pass
    where
    abs1 = error "abs1 called on signal"
    abs2 = error "abs2 called on signal"
    pass = error "pass called on signal"
abstract (AST.Assign var valExp) = return $ Return [var] abs1 abs2 pass
    where
    abs1 absVar 
        | absVar == var = uncurryValExpToTSLRet Abs1Return $ valExprToTSL var valExp
        | otherwise     = error $ "Invariant broken: " ++ var ++ " is not assigned here"
    abs2 = error "Invariant broken: abs2 called on an assignment"
    pass varr 
        | var == varr = f <$> rec
        | otherwise = error "invariant broken: pass"
            where
            rec = passValTSL valExp
            f rec = PassThroughReturn tsl preds ints vars
                where
                PassValTSLRet tsl preds ints vars = rec
abstract (AST.CaseC cases)  = join $ res <$> sequenceA subcases
    where
    subcases = map (abstract . snd) cases
    res subcases = if' (and (map (==hd) rst)) (return $ Return hd abs1 abs2 pass) (throwError "Different vars assigned in case branches")
        where
        (hd:rst)   = map (sort . varsRet) subcases
        caseabs1s  = map abs1Ret subcases
        caseabs2s  = map abs2Ret subcases
        casePasses = map passRet subcases
        conds = map (binExpToTSL . fst) cases
        abs1 absVar 
            | absVar `elem` hd = Abs1Return tsl preds (nub $ concat (map snd conds') ++ concat (map abs1newPreds abs1ress))
            | otherwise        = error $ "Invariant broken: " ++ absVar ++ " is not assigned in case"
                where
                abs1ress = map ($ absVar) caseabs1s
                tsl mp = Backend.Case $ zip (map fst conds') $ map (uncurry f . (abs1Tsl &&& abs1Preds))  abs1ress
                    where
                    f tslcase preds = Backend.Conj $ map (Backend.Not . QuantLit . flip fjml mp) (allPreds \\ preds) ++ [tslcase mp]
                conds' = map (binExpToTSL . fst) cases
                allPreds = nub $ concat $ map abs1Preds abs1ress
                preds = nub $ concat $ map abs1Preds abs1ress
        abs2 lv rv = Abs2Return tsl preds
            where
            rec = map (($ lv) >>> ($ rv)) caseabs2s
            tsl v = Backend.Case $ zip (map fst conds) (map (($ v) . abs2Tsl) rec)
            preds = nub $ concat $ map abs2Preds rec ++ map snd conds
        pass var = f <$> sequence rec
            where
            rec = map ($ var) casePasses
            f rec = PassThroughReturn (\v -> Backend.Case $ zip (map fst conds) (map (($ v) . passTSL) rec)) (nub $ concat $ map passPreds rec ++ map snd conds) (nub $ concat $ map passInts rec) (nub $ concat $ map passVars rec)
abstract (AST.Conj es) = join $ res <$> sequenceA rres
    where
    rres = map abstract es
    res rres = if' (disjoint allVars) (return $ Return allVars abs1 abs2 pass) (throwError "Vars assigned in case statement are not disjoint")
        where
        varsAssigned = map varsRet rres
        allVars  = concat varsAssigned
        theMap = createTheMap $ zip varsAssigned rres
        createTheMap :: [([String], Return f v c)] -> Map String (Int, Return f v c)
        createTheMap things = Map.unions $ map (uncurry f) (zipWith g things [0..])
            where
            f :: [String] -> (Int, Return f v c) -> Map String (Int, Return f v c)
            f vars func = Map.fromList (map (,func) vars)
            g :: (a, b) -> c -> (a, (c, b))
            g (x, y) z = (x, (z, y))
        abs1 absVar
            | absVar `elem` allVars = abs1Ret (snd $ fromJustNote "varsAssigned Conj" $ Map.lookup absVar theMap) absVar
            | otherwise             = error $ "Invariant broken: " ++ absVar ++ " is not assigned in CONJ"
        abs2 lv rv 
            | fst lres == fst rres = abs2 lv rv
            | otherwise            = Abs2Return tsl newPreds
            where
            getRet var = fromJustNote "getIdent" $ Map.lookup var theMap
            labs1ret = abs1Ret (snd lres) lv
            rabs1ret = abs1Ret (snd rres) rv
            lres = getRet lv
            rres = getRet rv
            (tsl, newPreds) = equalityValue lv rv labs1ret rabs1ret
        pass var = passRet (snd $ fromJustNote "pass conj" $ Map.lookup var theMap) var

doExists :: (Ord a) => [a] -> (Map a v -> AST f v c x y) -> AST f v c x y
doExists vars func = doExists' vars Map.empty
    where
    doExists' [] accum     = func accum
    doExists' (x:xs) accum = Exists $ \v -> doExists' xs (Map.insert x v accum)

toQV :: NSEQPred -> Map NSEQPred v -> AST f v c Predicate.Pred Predicate.Var
toQV nsp mp = QuantLit $ fjml nsp mp

equalityValue :: String -> String -> Abs1Return f v c -> Abs1Return f v c -> (v -> AST f v c Predicate.Pred Predicate.Var, [EqPred])
equalityValue lv rv labs1ret rabs1ret = (tsl, newPreds)
    where
    tsl v        = doExists allPreds (\mp -> Backend.Conj $ [abs1Tsl labs1ret mp, abs1Tsl rabs1ret mp, theExpr v mp])
    newPreds     = nub $ abs1newPreds labs1ret ++ abs1newPreds rabs1ret ++ catMaybes preds
    allPreds     = nub $ abs1Preds labs1ret ++ abs1Preds rabs1ret
    theExpr v mp = XNor (Backend.QuantLit v) (Backend.Disj (map Backend.Conj (map (map ($ mp)) tsls)))
    cartProd     = [(x, y) | x <- (abs1Preds labs1ret), y <- (abs1Preds rabs1ret)]
    (tsls, preds) = unzip $ map (uncurry func) cartProd
        where
        func p1 p2 = ([toQV p1, toQV p2, const tsl], pred) 
            where
            (tsl, pred) = func' p1 p2
            func' (NsEqVar l1 r1)   (NsEqVar l2 r2)   
                | r1==r2    = (T, Nothing)
                | otherwise = (Backend.Pred (pred, StateSection), Just pred) where pred = constructVarPred r1 r2
            func' (NsEqVar l1 r1)   (NsEqConst l2 r2) = (Backend.Pred (pred, StateSection), Just pred) where pred = constructConstPred r1 r2
            func' (NsEqConst l1 r1) (NsEqVar l2 r2)   = (Backend.Pred (pred, StateSection), Just pred) where pred = constructConstPred r2 r1
            func' (NsEqConst l1 r1) (NsEqConst l2 r2) = (if' (r1==r2) T F, Nothing)

eqConstraintTSL :: String -> String -> String -> AST f v c Predicate.Pred Predicate.Var
eqConstraintTSL x y z = Backend.Conj $ [func x y z, func y z x, func z x y]
    where
    func x y z = (mt x y `ma` mt y z) `mi` mt x z
    mt x y     = Backend.Pred $ (constructVarPred x y, StateSection)
    mi x y     = Backend.Imp x y
    ma x y     = Backend.And x y

constraintSection :: [(String, String, String)] -> AST f v c Predicate.Pred Predicate.Var
constraintSection x = Backend.Conj $ map (uncurryN eqConstraintTSL) x

