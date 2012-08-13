module Analysis where

import Control.Applicative
import Data.Traversable
import Control.Monad.Error 
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List
import Control.Arrow

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
    binExpToTSL' (Pred pred x y) = undefined

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

varsAssigned :: CtrlExpr -> Either String [String]
varsAssigned (Assign var _) = return [var]
varsAssigned (CaseC cases)  = join $ res <$> sequenceA subvars
    where
    subvars = map (liftA sort . varsAssigned . snd) cases
    res (hd:rst) = if' (and (map (==hd) rst)) (return hd) (throwError "Different vars assigned in case branches")
varsAssigned (IfC _ et ee)  = join $ res <$> vt <*> ve 
    where
    vt = sort <$> varsAssigned et
    ve = sort <$> varsAssigned ee
    res vt ve = if' (vt==ve) (return vt) (throwError "Different vars assigned in if branches")
varsAssigned (Conj es) = join $ res <$> sequenceA vars
    where
    vars = map varsAssigned es
    res vars = if' (disjoint allVars) (return allVars) (throwError "Vars assigned in case statement are not disjoint")
        where
        allVars = concat vars

{-
type Result = String

doVal :: ValExpr -> Result
doVal (StringLit str) = str
doVal (IntLit    int) = show int

prep :: [CtrlExpr] -> Map String CtrlExpr
prep = undefined

createTheMap :: [([String], CtrlExpr)] -> Map String CtrlExpr
createTheMap = undefined

abstract1 :: CtrlExpr -> String -> Result 
abstract1 (Assign var valAss) varReq 
    | var==valReq = var ++ "'==" ++ doVal valAss
    | otherwise   = error $ "Invariant broken: " ++ var ++ " is not assigned here"
abstract1 (CaseC cases) varReq = "case(){" ++ show procCases ++ "}"
    where
    procCases = map (abstract1 . snd) cases
abstract1 (If c t e) varReq = "if(){" ++ show procT ++ "}{" ++ show procE ++ "}"
    where
    procT = abstract1 t varReq
    procE = abstract1 e varReq
abstract1 (Conj  conjs) varReq = abstract1 (fromJustNote ("Invariant broken: " ++  varReq ++ " is not assigned here") Map.lookup valReq) varReq
    where
    res = map (varsAssigned &&& id) conjs
    theMap = createTheMap res
-}
