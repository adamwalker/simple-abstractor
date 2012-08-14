{-#LANGUAGE TupleSections, GADTs #-}
module Analysis where

import Control.Applicative
import Data.Traversable
import Control.Monad.Error 
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List
import Control.Arrow

import Safe

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
    binExpToTSL' (Not x)            = (UnOp SyntaxTree.Not (fst rec), snd rec)
        where
        rec = binExpToTSL x
    binExpToTSL' (Bin op x y)       = (BinOp (absBOpToTSLBOp op) (fst lr) (fst rr), nub $ snd lr ++ snd rr)
        where
        lr = binExpToTSL x 
        rr = binExpToTSL y
    binExpToTSL' (Pred AST.Eq x y)  = handleSimpleValPred x y
    binExpToTSL' (Pred AST.Neq x y) = (UnOp SyntaxTree.Not $ Mu () $ fst r, snd r)
        where
        r = handleSimpleValPred x y
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

valExprToTSL :: String -> ValExpr -> (Mu () AST, [EqPred])
valExprToTSL absVar = valExprToTSL'
    where
    valExprToTSL' = first (Mu ()) . valExprToTSL''
        where
        valExprToTSL'' (StringLit var) = (Term $ Ident [(predToString pred)] False, [pred])
            where
            pred = constructVarPred (absVar ++ "'") var
        valExprToTSL'' (IntLit int)    = (Term $ Ident [(predToString pred)] False, [pred])
            where
            pred = constructConstPred (absVar ++ "'") int
        valExprToTSL'' (CaseV cases)   = (SyntaxTree.Case $ zip conds (map (uncurry f) ccases), allPreds)
            where
            ccases = map (valExprToTSL' . snd) cases
            conds = map (fst . binExpToTSL . fst) cases
            allPreds = nub $ concat $ map snd ccases
            f tslcase preds = Mu () $ BlockOp SyntaxTree.Conj $ map (Mu () . UnOp SyntaxTree.Not . Mu () . predToTerm) (allPreds \\ preds) ++ [tslcase]
        valExprToTSL'' (IfV c t e)     = (TernOp (fst $ binExpToTSL c) tslT tslE, nub $ nub $ predsT ++ predsE)
            where 
            (tslT', predsT) = valExprToTSL' t 
            (tslE', predsE) = valExprToTSL' e
            tslT = Mu () $ BlockOp SyntaxTree.Conj $ map (Mu () . UnOp SyntaxTree.Not . Mu () . predToTerm) (predsE \\ predsT) ++ [tslT']
            tslE = Mu () $ BlockOp SyntaxTree.Conj $ map (Mu () . UnOp SyntaxTree.Not . Mu () . predToTerm) (predsT \\ predsE) ++ [tslE']

if' True  x y = x
if' False x y = y

listsIntersect :: (Eq a) => [a] -> [a] -> Bool
listsIntersect l r = or $ map (`elem` r) l

disjoint :: (Eq a) => [a] -> Bool
disjoint (hd:rst) = not (hd `elem` rst) && disjoint rst
disjoint []       = True

data Abs1Return = Abs1Return {
    abs1Tsl   :: Mu () AST,
    abs1Preds :: [EqPred]
}

data Abs2Return = Abs2Return {
    abs2Tsl   :: Mu () AST,
    abs2Preds :: [EqPred]
}

data Return = Return {
    varsRet :: [String],
    abs1Ret :: String -> Abs1Return,
    abs2Ret :: String -> String -> Abs2Return
}

varsAssigned :: CtrlExpr -> Either String Return
varsAssigned (Assign var valExp) = return $ Return [var] abs1 abs2
    where
    abs1 absVar 
        | absVar == var = uncurry Abs1Return $ valExprToTSL var valExp
        | otherwise     = error $ "Invariant broken: " ++ var ++ " is not assigned here"
    abs2 = error "Invariant broken: abs2 called on an assignment"
varsAssigned (CaseC cases)  = join $ res <$> sequenceA subcases
    where
    subcases = map (varsAssigned . snd) cases
    res subcases = if' (and (map (==hd) rst)) (return $ Return hd abs1 abs2) (throwError "Different vars assigned in case branches")
        where
        (hd:rst)  = map (sort . varsRet) subcases
        caseabs1s = map abs1Ret subcases
        caseabs2s = map abs2Ret subcases
        abs1 absVar 
            | absVar `elem` hd = Abs1Return tsl preds 
            | otherwise        = error $ "Invariant broken: " ++ absVar ++ " is not assigned in case"
                where
                abs1ress = map ($ absVar) caseabs1s
                tsl   = Mu () $ SyntaxTree.Case $ zip (map (fst . binExpToTSL . fst) cases) $ map abs1Tsl abs1ress
                preds = nub $ concat $ map abs1Preds abs1ress
        abs2 lv rv = Abs2Return tsl preds
            where
            rec = map (($ lv) >>> ($ rv)) caseabs2s
            tsl = Mu () $ SyntaxTree.Case $ zip (map (fst . binExpToTSL . fst) cases) (map abs2Tsl rec)
            preds = nub $ concat $ map abs2Preds rec
varsAssigned (IfC c et ee)  = join $ res <$> rt <*> re
    where
    rt = varsAssigned et
    re = varsAssigned ee
    res rt re = if' (vt == ve) (return $ Return vt abs1 abs2) (throwError "Different vars assigned in if branches")
        where
        vt  = sort $ varsRet rt
        ve  = sort $ varsRet rt 
        ta1 = abs1Ret rt
        ea1 = abs1Ret rt
        ta2 = abs2Ret rt
        ea2 = abs2Ret rt
        abs1 absVar
            | absVar `elem` vt = Abs1Return tsl (nub $ abs1Preds abstres ++ abs1Preds abseres)
            | otherwise        = error $ "Invariant broken: " ++ absVar ++ " is not assigned in if"
                where
                abstres = ta1 absVar
                abseres = ea1 absVar
                tsl = Mu () $ TernOp (fst $ binExpToTSL c) (abs1Tsl abstres) (abs1Tsl abseres)
        abs2 lv rv = Abs2Return tsl preds
            where
            tr = ta2 lv rv
            er = ea2 lv rv
            tsl = Mu () $ TernOp (fst $ binExpToTSL c) (abs2Tsl tr) (abs2Tsl er)
            preds = nub $ abs2Preds tr ++ abs2Preds er
varsAssigned (Conj es) = join $ res <$> sequenceA rres
    where
    rres = map varsAssigned es
    res rres = if' (disjoint allVars) (return $ Return allVars abs1 abs2) (throwError "Vars assigned in case statement are not disjoint")
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
            tsl = Mu () $ Quant Exists (map predToIdent allPreds) $ Mu () $ BlockOp SyntaxTree.Conj $ [abs1Tsl labs1ret, abs1Tsl rabs1ret, thePreds]
            getRet var = fromJustNote "getIdent" $ Map.lookup var theMap
            labs1ret = abs1Ret (snd lres) lv
            rabs1ret = abs1Ret (snd rres) rv
            allPreds = nub $ abs1Preds labs1ret ++ abs1Preds rabs1ret
            lres = getRet lv
            rres = getRet rv
            newPreds = undefined
            thePreds = Mu () $ BinOp SyntaxTree.Eq (Mu () $ predToTerm $ constructVarPred lv rv) $ Mu () $ BlockOp SyntaxTree.Disj $ map ((Mu () . BlockOp SyntaxTree.Conj . map (Mu ()) . uncurry func . ((getPred &&& id) *** (getPred &&& id)))) cartProd
                where
                cartProd = [(x, y) | x <- (abs1Preds labs1ret), y <- (abs1Preds rabs1ret)]
                --func :: (PredEither, EqPred) -> (PredEither, EqPred) -> (Mu () AST, Mu () AST, Mu () AST, 
                func (Left (l1, r1), l)  (Left (l2, r2), r)  = [predToTerm $ constructVarPred r1 r2, predToTerm l, predToTerm r]
                func (Left (l1, r1), l)  (Right (l2, r2), r) = [predToTerm $ constructConstPred r1 r2, predToTerm l, predToTerm r]
                func (Right (l1, r1), l) (Left (l2, r2), r)  = [predToTerm $ constructConstPred r2 r1, predToTerm l, predToTerm r]
                func (Right (l1, r1), l) (Right (l2, r2), r) = [TopBot (if' (r1==r2) Top Bot), predToTerm l, predToTerm r]

