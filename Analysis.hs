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

import qualified SyntaxTree
import SyntaxTree hiding (Not, Conj)

import AST
import Predicate

absBOpToTSLBOp AST.And = SyntaxTree.And
absBOpToTSLBOp AST.Or  = SyntaxTree.Or

handleSimpleValPred :: ValExpr -> ValExpr -> (AST a, [EqPred])
handleSimpleValPred (StringLit x) (IntLit    y) = (predToTerm pred, [pred])
    where
    pred = constructConstPred x y
handleSimpleValPred (IntLit    x) (StringLit y) = (predToTerm pred, [pred])
    where
    pred = constructConstPred y x
handleSimpleValPred (StringLit x) (StringLit y) = (predToTerm pred, [pred])
    where
    pred = constructVarPred x y
handleSimpleValPred (IntLit    x) (IntLit    y) = (if' (x==y) (TopBot Top) (TopBot Bot), [])

binExpToTSL :: BinExpr -> (Mu () AST, [EqPred])
binExpToTSL = first (Mu ()) . binExpToTSL'
    where
    binExpToTSL' TrueE              = (TopBot Top, [])
    binExpToTSL' FalseE             = (TopBot Bot, [])
    binExpToTSL' (Not x)            = (UnOp SyntaxTree.Not (fst rec), snd rec) where rec = binExpToTSL x
    binExpToTSL' (Bin op x y)       = (BinOp (absBOpToTSLBOp op) (fst lr) (fst rr), nub $ snd lr ++ snd rr)
        where
        lr = binExpToTSL x 
        rr = binExpToTSL y
    binExpToTSL' (Pred AST.Eq x y)  = handleSimpleValPred x y
    binExpToTSL' (Pred AST.Neq x y) = (UnOp SyntaxTree.Not $ Mu () $ fst r, snd r) where r = handleSimpleValPred x y
    binExpToTSL' (Atom ident)       = (Term $ Ident [ident] False, [])

predToString :: EqPred -> String
predToString pred = predToString' val
    where
    predToString' (Left (l, r))  = "\"" ++ l ++ "==" ++ r ++ "\""
    predToString' (Right (x, c)) = "\"" ++ x ++ "==" ++ show c ++ "\""
    val = getPred pred

predToIdent :: EqPred -> Ident 
predToIdent pred = Ident [(predToString pred)] False

predToTerm :: EqPred -> AST a
predToTerm = Term . predToIdent

nsPredToString :: NSEQPred -> String
nsPredToString (NsEqVar l r)   = "\"" ++ l ++ "'==" ++ r ++ "\""
nsPredToString (NsEqConst x c) = "\"" ++ x ++ "'==" ++ show c ++ "\""

nsPredToIdent :: NSEQPred -> Ident
nsPredToIdent pred = Ident [(nsPredToString pred)] False

nsPredToTerm :: NSEQPred -> AST a
nsPredToTerm = Term . nsPredToIdent

data ValExprToTSLRet = ValExprToTSLRet {
    valExpTSL   :: Mu () AST,
    primedPreds :: [NSEQPred],
    newPreds    :: [EqPred]
}

uncurryValExpToTSLRet :: (Mu () AST -> [NSEQPred] -> [EqPred] -> a) -> ValExprToTSLRet -> a
uncurryValExpToTSLRet f (ValExprToTSLRet x y z) = f x y z

valExprToTSL :: String -> ValExpr -> ValExprToTSLRet
valExprToTSL absVar = valExprToTSL'
    where
    valExprToTSL' (StringLit var) = ValExprToTSLRet (Mu () $ nsPredToTerm pred) [pred] []
        where
        pred = NsEqVar absVar var
    valExprToTSL' (IntLit int)    = ValExprToTSLRet (Mu () $ nsPredToTerm pred) [pred] []
        where
        pred = NsEqConst absVar int
    valExprToTSL' (CaseV cases)   = ValExprToTSLRet (Mu () $ SyntaxTree.Case $ zip conds (map (uncurry f) (zip (map valExpTSL ccases) (map primedPreds ccases)))) allPreds newPreds
        where
        ccases = map (valExprToTSL' . snd) cases
        conds' = map (binExpToTSL . fst) cases
        conds  = map fst conds'
        newPreds = nub $ concat $ map snd conds'
        allPreds = nub $ concat $ map primedPreds ccases
        f :: Mu () AST -> [NSEQPred] -> Mu () AST
        f tslcase preds = Mu () $ BlockOp SyntaxTree.Conj $ map (Mu () . UnOp SyntaxTree.Not . Mu () . nsPredToTerm) (allPreds \\ preds) ++ [tslcase]
    valExprToTSL' (IfV c t e)     = ValExprToTSLRet (Mu () $ TernOp (fst $ binExpToTSL c) tslT tslE) allPreds newPreds
        where 
        ValExprToTSLRet tslT' predsT newPredsT = valExprToTSL' t 
        ValExprToTSLRet tslE' predsE newPredsE = valExprToTSL' e
        tslT = Mu () $ BlockOp SyntaxTree.Conj $ map (Mu () . UnOp SyntaxTree.Not . Mu () . nsPredToTerm) (predsE \\ predsT) ++ [tslT']
        tslE = Mu () $ BlockOp SyntaxTree.Conj $ map (Mu () . UnOp SyntaxTree.Not . Mu () . nsPredToTerm) (predsT \\ predsE) ++ [tslE']
        allPreds = nub $ predsT ++ predsE 
        newPreds = nub $ newPredsT ++ newPredsE

data PassValTSLRet = PassValTSLRet {
    passValTSLTSL   :: Mu () AST,
    passValTSLPreds :: [EqPred]
}

uncurryPassValTSLRet :: (Mu () AST -> [EqPred] -> a) -> PassValTSLRet -> a
uncurryPassValTSLRet f (PassValTSLRet x y) = f x y 

passValTSL :: ValExpr -> Either String PassValTSLRet
passVaTSL (StringLit var) = return $ PassValTSLRet (Mu () $ Term (Ident [var] False)) []
passValTSL (IntLit int)    = return $ PassValTSLRet (Mu () $ Lit (fromIntegral int)) []
passValTSL (CaseV cases)   = f <$> sequence recs
    where
    conds = map (binExpToTSL . fst) cases
    recs  = map (passValTSL . snd) cases
    f recs = PassValTSLRet (Mu () $ SyntaxTree.Case $ zip (map fst conds) (map passValTSLTSL recs)) (nub $ concat $ map snd conds ++ map passValTSLPreds recs)
passValTSL (IfV c t e)     = f <$> tr <*> er
    where
    (ctsl, cpreds)         = binExpToTSL c
    tr = passValTSL t
    er = passValTSL e
    f tr er = PassValTSLRet (Mu () $ TernOp ctsl ttsl etsl) (nub $ cpreds ++ tpreds ++ epreds)
        where
        PassValTSLRet ttsl tpreds = tr 
        PassValTSLRet etsl epreds = er

if' True  x y = x
if' False x y = y

listsIntersect :: (Eq a) => [a] -> [a] -> Bool
listsIntersect l r = or $ map (`elem` r) l

disjoint :: (Eq a) => [a] -> Bool
disjoint (hd:rst) = not (hd `elem` rst) && disjoint rst
disjoint []       = True

data Abs1Return = Abs1Return {
    abs1Tsl       :: Mu () AST,
    abs1Preds     :: [NSEQPred],
    abs1newPreds  :: [EqPred]
}

data Abs2Return = Abs2Return {
    abs2Tsl   :: Mu () AST,
    abs2Preds :: [EqPred]
}

data PassThroughReturn = PassThroughReturn {
    passTSL   :: Mu () AST,
    passPreds :: [EqPred]
}

data Return = Return {
    varsRet :: [String],
    abs1Ret :: String -> Abs1Return,
    abs2Ret :: String -> String -> Abs2Return,
    passRet :: String -> Either String PassThroughReturn
}

abstract :: CtrlExpr -> Either String Return
abstract (Assign var valExp) = return $ Return [var] abs1 abs2 pass
    where
    abs1 absVar 
        | absVar == var = uncurryValExpToTSLRet Abs1Return $ valExprToTSL var valExp
        | otherwise     = error $ "Invariant broken: " ++ var ++ " is not assigned here"
    abs2 = error "Invariant broken: abs2 called on an assignment"
    pass var = f <$> rec
        where
        rec = passValTSL valExp
        f rec = PassThroughReturn (Mu () $ BinOp SyntaxTree.Eq (Mu () $ Term (Ident [var] False)) tsl) preds
            where
            PassValTSLRet tsl preds = rec
abstract (CaseC cases)  = join $ res <$> sequenceA subcases
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
            | absVar `elem` hd = Abs1Return tsl preds (nub $ concat (map snd binExpRes) ++ concat (map abs1newPreds abs1ress))
            | otherwise        = error $ "Invariant broken: " ++ absVar ++ " is not assigned in case"
                where
                abs1ress = map ($ absVar) caseabs1s
                binExpRes = map (binExpToTSL . fst) cases
                allPreds = nub $ concat $ map abs1Preds abs1ress
                tsl   = Mu () $ SyntaxTree.Case $ zip (map fst binExpRes) $ map (uncurry f . (abs1Tsl &&& abs1Preds))  abs1ress
                f tslcase preds = Mu () $ BlockOp SyntaxTree.Conj $ map (Mu () . UnOp SyntaxTree.Not . Mu () . nsPredToTerm) (allPreds \\ preds) ++ [tslcase]
                preds = nub $ concat $ map abs1Preds abs1ress
        abs2 lv rv = Abs2Return tsl preds
            where
            rec = map (($ lv) >>> ($ rv)) caseabs2s
            tsl = Mu () $ SyntaxTree.Case $ zip (map fst conds) (map abs2Tsl rec)
            preds = nub $ concat $ map abs2Preds rec ++ map snd conds
        pass var = f <$> sequence rec
            where
            rec = map ($ var) casePasses
            f rec = PassThroughReturn (Mu () $ SyntaxTree.Case $ zip (map fst conds) (map passTSL rec)) (nub $ concat $ map passPreds rec ++ map snd conds)
abstract (IfC c et ee)  = join $ res <$> rt <*> re
    where
    rt = abstract et
    re = abstract ee
    res rt re = if' (vt == ve) (return $ Return vt abs1 abs2 pass) (throwError "Different vars assigned in if branches")
        where
        vt  = sort $ varsRet rt
        ve  = sort $ varsRet rt 
        ta1 = abs1Ret rt
        ea1 = abs1Ret rt
        ta2 = abs2Ret rt
        ea2 = abs2Ret rt
        cr = binExpToTSL c
        abs1 absVar
            | absVar `elem` vt = Abs1Return tsl (nub $ abs1Preds abstres ++ abs1Preds abseres) (nub $ snd binExpRes ++ abs1newPreds abstres ++ abs1newPreds abseres)
            | otherwise        = error $ "Invariant broken: " ++ absVar ++ " is not assigned in if"
                where
                abstres = ta1 absVar
                abseres = ea1 absVar
                binExpRes = binExpToTSL c
                tsl = Mu () $ TernOp (fst binExpRes) (abs1Tsl abstres) (abs1Tsl abseres)
                tslT = Mu () $ BlockOp SyntaxTree.Conj $ map (Mu () . UnOp SyntaxTree.Not . Mu () . nsPredToTerm) (abs1Preds abseres \\ abs1Preds abstres) ++ [abs1Tsl abstres]
                tslE = Mu () $ BlockOp SyntaxTree.Conj $ map (Mu () . UnOp SyntaxTree.Not . Mu () . nsPredToTerm) (abs1Preds abstres \\ abs1Preds abseres) ++ [abs1Tsl abseres]
        abs2 lv rv = Abs2Return tsl preds
            where
            tr = ta2 lv rv
            er = ea2 lv rv
            tsl = Mu () $ TernOp (fst cr) (abs2Tsl tr) (abs2Tsl er)
            preds = nub $ abs2Preds tr ++ abs2Preds er ++ snd cr
        pass var = f cr <$> tr <*> er
            where
            tr = passRet rt var
            er = passRet re var
            f cr tr er = PassThroughReturn (Mu () $ TernOp (fst cr) (passTSL tr) (passTSL er)) (nub $ snd cr ++ passPreds tr ++ passPreds er)
abstract (Conj es) = join $ res <$> sequenceA rres
    where
    rres = map abstract es
    res rres = if' (disjoint allVars) (return $ Return allVars abs1 abs2 pass) (throwError "Vars assigned in case statement are not disjoint")
        where
        varsAssigned = map varsRet rres
        allVars  = concat varsAssigned
        theMap = createTheMap $ zip varsAssigned rres
        createTheMap :: [([String], Return)] -> Map String (Int, Return)
        createTheMap things = Map.unions $ map (uncurry f) (zipWith g things [0..])
            where
            f :: [String] -> (Int, Return) -> Map String (Int, Return)
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
            tsl = Mu () $ Quant Exists (map nsPredToIdent allPreds) $ Mu () $ BlockOp SyntaxTree.Conj $ [abs1Tsl labs1ret, abs1Tsl rabs1ret, thePreds]
            getRet var = fromJustNote "getIdent" $ Map.lookup var theMap
            labs1ret = abs1Ret (snd lres) lv
            rabs1ret = abs1Ret (snd rres) rv
            allPreds = nub $ abs1Preds labs1ret ++ abs1Preds rabs1ret
            lres = getRet lv
            rres = getRet rv
            newPreds = nub $ abs1newPreds labs1ret ++ abs1newPreds rabs1ret ++ catMaybes preds
            thePreds = Mu () $ BinOp SyntaxTree.Eq (Mu () $ predToTerm $ constructVarPred lv rv) $ Mu () $ BlockOp SyntaxTree.Disj $ map ((Mu () . BlockOp SyntaxTree.Conj . map (Mu ()))) tsls
            cartProd = [(x, y) | x <- (abs1Preds labs1ret), y <- (abs1Preds rabs1ret)]
            (tsls, preds) = unzip $ map (uncurry func) cartProd
                where
                func p1 p2 = ([nsPredToTerm p1, nsPredToTerm p2, tsl], pred) where (tsl, pred) = func' p1 p2
                func' (NsEqVar l1 r1)   (NsEqVar l2 r2)   
                    | r1==r2    = (TopBot Top, Nothing)
                    | otherwise = (predToTerm pred, Just pred) where pred = constructVarPred r1 r2
                func' (NsEqVar l1 r1)   (NsEqConst l2 r2) = (predToTerm pred, Just pred) where pred = constructConstPred r1 r2
                func' (NsEqConst l1 r1) (NsEqVar l2 r2)   = (predToTerm pred, Just pred) where pred = constructConstPred r2 r1
                func' (NsEqConst l1 r1) (NsEqConst l2 r2) = (TopBot (if' (r1==r2) Top Bot), Nothing)
        pass var = passRet (snd $ fromJustNote "pass conj" $ Map.lookup var theMap) var

eqConstraintTSL :: String -> String -> String -> Mu () AST
eqConstraintTSL x y z = Mu () $ BlockOp SyntaxTree.Conj $ [func x y z, func y z x, func z x y]
    where
    func x y z = (mt x y `ma` mt y z) `mi` mt x z
    mt x y     = Mu () $ predToTerm $ constructVarPred x y
    mi x y     = Mu () $ BinOp Imp x y
    ma x y     = Mu () $ BinOp SyntaxTree.And x y

constraintSection :: [(String, String, String)] -> Mu () AST
constraintSection x = Mu () $ BlockOp SyntaxTree.Conj $ map (uncurryN eqConstraintTSL) x

