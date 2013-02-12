{-# LANGUAGE RecordWildCards, PolymorphicComponents, ScopedTypeVariables #-}
module TopLevel where

import System.Environment
import Control.Monad.ST.Lazy
import Control.Monad.State
import Data.Functor
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Applicative

import Text.Parsec hiding ((<|>))
import qualified Text.Parsec.Token as T
import Text.Parsec.Language

import CuddST
import CuddExplicitDeref
import CuddReorder

import Analysis
import AST
import Backend
import Parser
import Predicate
import Resolve
import qualified RefineCommon
import qualified RefineGFP
import qualified RefineLFP
import qualified RefineReachFair
import Interface

data Spec = Spec {
    stateDecls   :: [Decl],
    labelDecls   :: [Decl],
    outcomeDecls :: [Decl],
    init         :: BinExpr (Either String Int),
    goal         :: BinExpr (Either String Int),
    fair         :: BinExpr (Either String Int),
    trans        :: CtrlExpr String (Either String Int)
}

lexer = T.makeTokenParser (emptyDef {T.reservedNames = reservedNames ++ ["STATE", "LABEL", "OUTCOME", "INIT", "GOAL", "TRANS", "FAIR"]
                                    ,T.reservedOpNames = reservedOps
                                    ,T.identStart = letter <|> char '_'
                                    ,T.identLetter = alphaNum <|> char '_'
                                    ,T.commentStart = "/*"
                                    ,T.commentEnd = "*/"
                                    ,T.commentLine = "//"
                                    })
T.TokenParser {..} = lexer

spec = Spec 
    <$  reserved "STATE"
    <*> sepEndBy (decl lexer) semi
    <*  reserved "LABEL"
    <*> sepEndBy (decl lexer) semi
    <*  reserved "OUTCOME"
    <*> sepEndBy (decl lexer) semi
    <*  reserved "INIT"
    <*> binExpr lexer
    <*  reserved "GOAL"
    <*> binExpr lexer
    <*  reserved "FAIR"
    <*> binExpr lexer
    <*  reserved "TRANS"
    <*> ctrlExpr lexer

top = whiteSpace *> spec <* eof

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
        Right abstractor -> liftM Right $ RefineReachFair.absRefineLoop m abstractor ts (error "No abstractor state")
            where
            ts    = RefineCommon.TheorySolver ucs ucsl quant
            ucs   = const Nothing
            ucsl  = const $ const Nothing
            quant _ _ = return $ bone m

theAbs :: forall s u. STDdManager s u -> CtrlExpr String (Either Analysis.VarInfo Int) -> BinExpr (Either Analysis.VarInfo Int) -> BinExpr (Either Analysis.VarInfo Int) -> BinExpr (Either Analysis.VarInfo Int) -> Either String (RefineReachFair.Abstractor s u EqPred EqPred)
theAbs m trans init goal fair = func <$> abstract trans
    where
    func Return{..} = RefineReachFair.Abstractor{..}
        where
        fairAbs :: VarOps pdb (BAPred EqPred EqPred) BAVar s u -> StateT pdb (ST s) (DDNode s u)
        fairAbs ops              = compile m ops tsl where (tsl, _) = binExpToTSL fair
        goalAbs :: VarOps pdb (BAPred EqPred EqPred) BAVar s u -> StateT pdb (ST s) (DDNode s u)
        goalAbs ops              = compile m ops tsl where (tsl, _) = binExpToTSL goal
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

funcy :: STDdManager s u -> String -> Either String (RefineReachFair.Abstractor s u EqPred EqPred)
funcy m contents = do
    Spec {..} <- either (Left . show) Right $ parse top "" contents
    let theMap =  doDecls stateDecls labelDecls outcomeDecls
    tr         <- resolve theMap trans
    ir         <- resolveBin theMap init
    gr         <- resolveBin theMap goal
    fr         <- resolveBin theMap fair
    theAbs m tr ir gr fr

