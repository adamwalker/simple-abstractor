{-# LANGUAGE RecordWildCards #-}
module TopLevel where

import System.Environment
import Control.Monad.ST.Lazy
import Control.Monad.State
import Data.Functor

import Text.Parsec hiding ((<|>))

import CuddST
import CuddExplicitDeref

import Analysis
import AST
import Backend
import Parser
import Predicate
import Resolve

absRefineLoop :: STDdManager s u -> Abstractor pdb s u -> a -> a -> ST s Bool
absRefineLoop = undefined

main = do
    [fname] <- getArgs
    fres <- readFile fname
    let res = runST $ doIt fres
    print res

doIt :: String -> ST s (Either String Bool)
doIt fres = do
    m <- cuddInitSTDefaults
    case funcy m fres of 
        Left  err        -> return $ Left err
        Right abstractor -> liftM Right $ absRefineLoop m abstractor undefined undefined

data Abstractor pdb s u = Abstractor {
    pred :: VarOps pdb Pred Var s u -> EqPred -> DDNode s u   -> StateT pdb (ST s) (DDNode s u),
    pass :: VarOps pdb Pred Var s u -> String -> [DDNode s u] -> StateT pdb (ST s) (DDNode s u),
    goal :: VarOps pdb Pred Var s u -> StateT pdb (ST s) (DDNode s u),
    init :: VarOps pdb Pred Var s u -> StateT pdb (ST s) (DDNode s u)
}

funcy :: STDdManager s u -> String -> Either String (Abstractor pdb s u)
funcy m contents = do
    (Spec sdecls ldecls init goal trans) <- either (Left . show) Right $ parse top "" contents
    let theMap                           =  doDecls sdecls ldecls 
    tr                                   <- resolve theMap trans
    ir                                   <- resolveBin theMap init
    gr                                   <- resolveBin theMap goal
    func m tr ir gr

func :: STDdManager s u -> CtrlExpr String (Either VarInfo Int) -> BinExpr (Either VarInfo Int) -> BinExpr (Either VarInfo Int) -> Either String (Abstractor pdb s u)
func m trans initt goall = func <$> abstract trans
    where
    func Return{..} = Abstractor {..}
        where
        pred ops (Predicate.EqVar v1 v2) = compile m ops . abs2Tsl where Abs2Return {..} = abs2Ret v1 v2
        pred ops (Predicate.EqConst v c) = error "func: not implemented"
        pass ops var                     = compile m ops . passTSL where PassThroughReturn {..} = either (error "func") id $ passRet var
        goal ops                         = compile m ops tsl where (tsl, _) = binExpToTSL goall
        init ops                         = compile m ops tsl where (tsl, _) = binExpToTSL initt


