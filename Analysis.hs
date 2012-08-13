{-#LANGUAGE TupleSections #-}
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

binExpToTSL :: BinExpr -> Mu () AST 
binExpToTSL = Mu () . binExpToTSL'
    where
    binExpToTSL' TrueE           = TopBot Top
    binExpToTSL' FalseE          = TopBot Bot
    binExpToTSL' (Not x)         = UnOp SyntaxTree.Not (binExpToTSL x)
    binExpToTSL' (Bin op x y)    = BinOp (absBOpToTSLBOp op) (binExpToTSL x) (binExpToTSL y)
    binExpToTSL' (Pred pred x y) = Term $ Ident ["Some pred in binExpToTSL"] False

predToString :: EqPred -> String
predToString pred = predToString' val
    where
    predToString' (Left (l, r))  = "\"" ++ l ++ "==" ++ r ++ "\""
    predToString' (Right (x, c)) = "\"" ++ x ++ "==" ++ show c ++ "\""
    val = getPred pred

predToTerm :: EqPred -> AST a
predToTerm pred = Term $ Ident [(predToString pred)] False

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
            conds = map (binExpToTSL . fst) cases
            allPreds = nub $ concat $ map snd ccases
            f tslcase preds = Mu () $ BlockOp SyntaxTree.Conj $ map (Mu () . UnOp SyntaxTree.Not . Mu () . predToTerm) (allPreds \\ preds) ++ [tslcase]
        valExprToTSL'' (IfV c t e)     = (TernOp (binExpToTSL c) tslT tslE, nub $ nub $ predsT ++ predsE)
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

varsAssigned :: CtrlExpr -> Either String ([String], String -> Mu () AST)
varsAssigned (Assign var valExp) = return ([var], abs1)
    where
    abs1 absVar 
        | absVar == var = fst $ valExprToTSL var valExp
        | otherwise     = error $ "Invariant broken: " ++ var ++ " is not assigned here"
varsAssigned (CaseC cases)  = join $ res <$> sequenceA subcases
    where
    subcases = map (varsAssigned . snd) cases
    res subcases = if' (and (map (==hd) rst)) (return (hd, abs1)) (throwError "Different vars assigned in case branches")
        where
        (hd:rst)  = map (sort . fst) subcases
        caseabs1s = map snd subcases
        abs1 absVar 
            | absVar `elem` hd = Mu () $ SyntaxTree.Case $ zip (map (binExpToTSL . fst) cases) (map ($ absVar) caseabs1s)
            | otherwise        = error $ "Invariant broken: " ++ absVar ++ " is not assigned in case"
varsAssigned (IfC c et ee)  = join $ res <$> rt <*> re
    where
    rt = varsAssigned et
    re = varsAssigned ee
    res rt re = if' (vt == ve) (return (vt, abs1)) (throwError "Different vars assigned in if branches")
        where
        vt  = sort $ fst rt
        ve  = sort $ fst rt 
        ta1 = snd rt
        ea1 = snd rt
        abs1 absVar
            | absVar `elem` vt = Mu () $ TernOp (binExpToTSL c) (ta1 absVar) (ea1 absVar)
            | otherwise        = error $ "Invariant broken: " ++ absVar ++ " is not assigned in if"
varsAssigned (Conj es) = join $ res <$> sequenceA rres
    where
    rres = map varsAssigned es
    res rres = if' (disjoint allVars) (return (allVars, abs1)) (throwError "Vars assigned in case statement are not disjoint")
        where
        varsAssigned = map fst rres
        allVars  = concat varsAssigned
        theMap = createTheMap $ zip varsAssigned (map snd rres)
        createTheMap :: [([String], (String -> Mu () AST))] -> Map String (String -> Mu () AST)
        createTheMap things = Map.unions $ map (uncurry f) things
            where
            f :: [String] -> (String -> Mu () AST) -> Map String (String -> Mu () AST)
            f vars func = Map.fromList (map (,func) vars)
        abs1 absVar
            | absVar `elem` allVars = (fromJustNote "varsAssigned Conj" $ Map.lookup absVar theMap) absVar
            | otherwise             = error $ "Invariant broken: " ++ absVar ++ " is not assigned in CONJ"

