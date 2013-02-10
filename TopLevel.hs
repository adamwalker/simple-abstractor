{-# LANGUAGE RecordWildCards, PolymorphicComponents, ScopedTypeVariables #-}
module TopLevel where

import System.Environment
import Control.Monad.ST.Lazy
import Control.Monad.State
import Data.Functor
import qualified Data.Map as Map
import Data.Map (Map)

import Text.Parsec hiding ((<|>))

import CuddST
import CuddExplicitDeref
import CuddReorder

import Analysis
import AST
import Backend
import Parser
import Predicate
import Resolve
import qualified Refine
import qualified RefineLFP
import Interface

doMain = do
    [fname] <- getArgs
    fres <- readFile fname
    let res = runST $ doIt fres
    print res

doIt :: String -> ST s (Either String Bool)
doIt fres = do
    m <- cuddInitSTDefaults
    cuddAutodynEnable m CuddReorderGroupSift
    regStdPreReordHook m
    regStdPostReordHook m
    cuddEnableReorderingReporting m
    case funcy m fres of 
        Left  err        -> return $ Left err
        Right abstractor -> liftM Right $ RefineLFP.absRefineLoop m abstractor ts (error "No abstractor state")
            where
            ts    = Refine.TheorySolver ucs ucsl quant
            ucs   = const Nothing
            ucsl  = const $ const Nothing
            quant _ _ = return $ bone m

theAbs :: forall s u. STDdManager s u -> CtrlExpr String (Either Analysis.VarInfo Int) -> BinExpr (Either Analysis.VarInfo Int) -> BinExpr (Either Analysis.VarInfo Int) -> Either String (RefineLFP.Abstractor s u EqPred EqPred)
theAbs m trans init goal = func <$> abstract trans
    where
    func Return{..} = RefineLFP.Abstractor{..}
        where
        safeAbs :: VarOps pdb (BAPred EqPred EqPred) BAVar s u -> StateT pdb (ST s) (DDNode s u)
        safeAbs ops              = compile m ops tsl where (tsl, _) = binExpToTSL goal
        initAbs :: VarOps pdb (BAPred EqPred EqPred) BAVar s u -> StateT pdb (ST s) (DDNode s u)
        initAbs ops              = compile m ops tsl where (tsl, _) = binExpToTSL init
        updateAbs :: [(EqPred, DDNode s u)] -> [(String, [DDNode s u])] -> VarOps pdb (BAPred EqPred EqPred) BAVar s u -> StateT pdb (ST s) (DDNode s u)
        updateAbs preds vars ops = do
            x <- mapM (uncurry $ pred ops) preds 
            y <- mapM (uncurry $ pass ops) vars
            lift $ Backend.conj m $ x ++ y
            where
            pred ops (Predicate.EqVar v1 v2) = compile m ops . abs2Tsl       
                where Abs2Return {..}        = abs2Ret v1 v2
            pred ops (Predicate.EqConst v c) = compile m ops . equalityConst (abs1Ret v) c
            pass ops var                     = compile m ops . passTSL 
                where PassThroughReturn {..} = either (error "func") id $ passRet var

funcy :: STDdManager s u -> String -> Either String (RefineLFP.Abstractor s u EqPred EqPred)
funcy m contents = do
    (Spec sdecls ldecls odecls init goal trans) <- either (Left . show) Right $ parse top "" contents
    let theMap                                  =  doDecls sdecls ldecls odecls
    tr                                          <- resolve theMap trans
    ir                                          <- resolveBin theMap init
    gr                                          <- resolveBin theMap goal
    theAbs m tr ir gr

