{-# LANGUAGE RecordWildCards, PolymorphicComponents, ScopedTypeVariables #-}
module AdamAbstractor.CompileHelpers where

import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Control.Monad.State
import Control.Applicative

import Text.PrettyPrint.Leijen.Text (text)

import Cudd.Imperative

import AdamAbstractor.Analysis
import AdamAbstractor.AST hiding (Pred)
import AdamAbstractor.Backend as Backend
import AdamAbstractor.Predicate as Predicate
import Synthesis.Interface

import Data.Text.Lazy as Text

{-# NOINLINE traceST #-}
traceST :: String -> ST s ()
traceST = unsafeIOToST . putStrLn

compileBin :: STDdManager s u -> VarOps pdb TheVarType' s u -> BinExpr (ASTEqPred ValType) -> StateT pdb (ST s) (DDNode s u)
compileBin m ops = compile m ops . binExprToAST

newtype R s u = R {unR :: forall pdb. [(VarType EqPred, [DDNode s u])] -> VarOps pdb TheVarType' s u -> StateT pdb (ST s) ([DDNode s u], DDNode s u)}

compileUpdate :: CtrlExpr String (ASTEqPred ValType) ValType -> STDdManager s u -> Either String (R s u)
compileUpdate ce m = func <$> abstract ce <*> abstract ce
    where
    func ret dbg = R func2
        where 
        func2 preds ops = do
            res <- mapM (uncurry pred) preds 
            return (res, bzero m)
            where
            pred (Pred (Predicate.EqVar v1 s1 v2 s2)) x = do
                lift $ traceST $ show $ prettyPrint $ abs2Ret dbg v1 s1 v2 s2 (text $ pack "next")
                compile m ops $ abs2Ret ret v1 s1 v2 s2 x
            pred (Pred (Predicate.EqConst v s c))     x = do
                lift $ traceST $ show $ prettyPrint $ equalityConst (text $ pack "next") (astRet dbg v) s c
                compile m ops $ equalityConst x (astRet ret v) s c
            pred (Enum var)                           x = do
                lift $ traceST $ show $ prettyPrint $ passValTSL (astRet dbg var) (text $ pack "next")
                compile m ops $ passValTSL (astRet ret var) x

