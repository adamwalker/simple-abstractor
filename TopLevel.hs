{-# LANGUAGE RecordWildCards, PolymorphicComponents, ScopedTypeVariables #-}
module TopLevel where

import System.Environment
import Control.Monad.ST
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

import Analysis
import AST hiding (Pred)
import Backend
import Parser
import Predicate
import Resolve
import qualified RefineCommon
--import qualified RefineGFP
--import qualified RefineLFP
--import qualified RefineReachFair
import qualified TermiteGame as Game
import Interface

data Spec = Spec {
    stateDecls   :: [Decl],
    labelDecls   :: [Decl],
    outcomeDecls :: [Decl],
    init         :: BinExpr (Either String Int),
    goal         :: [BinExpr (Either String Int)],
    fair         :: [BinExpr (Either String Int)],
    cont         :: BinExpr (Either String Int),
    trans        :: CtrlExpr String (Either String Int)
}

lexer = T.makeTokenParser (emptyDef {T.reservedNames = reservedNames ++ ["STATE", "LABEL", "OUTCOME", "INIT", "GOAL", "TRANS", "FAIR", "CONT"]
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
    <*> sepEndBy (binExpr lexer) semi
    <*  reserved "FAIR"
    <*> sepEndBy (binExpr lexer) semi
    <*  reserved "CONT"
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
    m <- RefineCommon.setupManager 
    case funcy m fres of 
        Left  err        -> return $ Left err
        Right abstractor -> liftM Right $ Game.absRefineLoop m abstractor ts (error "No abstractor state")
            where
            ts    = RefineCommon.TheorySolver ucs ucsl quant
            ucs   = const Nothing
            ucsl  = const $ const Nothing
            quant _ _ = return $ bone m

theAbs :: forall s u. STDdManager s u -> CtrlExpr String (Either Analysis.VarInfo Int) -> BinExpr (Either Analysis.VarInfo Int) -> [BinExpr (Either Analysis.VarInfo Int)] -> [BinExpr (Either Analysis.VarInfo Int)] -> BinExpr (Either Analysis.VarInfo Int) -> Either String (Game.Abstractor s u (VarType EqPred) (VarType EqPred))
theAbs m trans init goal fair cont = func <$> abstract trans
    where
    func Return{..} = Game.Abstractor{..}
        where
        fairAbs :: VarOps pdb TheVarType s u -> StateT pdb (ST s) [DDNode s u]
        fairAbs ops              = mapM (compile m ops . fst . binExpToTSL) fair
        goalAbs :: VarOps pdb TheVarType s u -> StateT pdb (ST s) [DDNode s u]
        goalAbs ops              = mapM (compile m ops . fst . binExpToTSL) goal
        initAbs :: VarOps pdb TheVarType s u -> StateT pdb (ST s) (DDNode s u)
        initAbs ops              = compile m ops tsl where (tsl, _) = binExpToTSL init
        contAbs :: VarOps pdb TheVarType s u -> StateT pdb (ST s) (DDNode s u)
        contAbs ops              = compile m ops tsl where (tsl, _) = binExpToTSL cont
        updateAbs :: [(VarType EqPred, [DDNode s u])] -> VarOps pdb TheVarType s u -> StateT pdb (ST s) (DDNode s u)
        updateAbs preds ops = do
            x <- mapM (uncurry $ pred ops) preds 
            lift $ Backend.conj m x 
            where
            pred ops (Pred (Predicate.EqVar v1 v2)) = compile m ops . abs2Tsl       
                where Abs2Return {..}               = abs2Ret v1 v2
            pred ops (Pred (Predicate.EqConst v c)) = compile m ops . equalityConst (abs1Ret v) c
            pred ops (Enum var)                     = compile m ops . passTSL 
                where PassThroughReturn {..}        = either (error "func") id $ passRet var

funcy :: STDdManager s u -> String -> Either String (Game.Abstractor s u (VarType EqPred) (VarType EqPred))
funcy m contents = do
    Spec {..} <- either (Left . show) Right $ parse top "" contents
    let theMap =  doDecls stateDecls labelDecls outcomeDecls
    tr         <- resolve theMap trans
    ir         <- resolveBin theMap init
    gr         <- mapM (resolveBin theMap) goal
    fr         <- mapM (resolveBin theMap) fair
    ct         <- resolveBin theMap cont
    theAbs m tr ir gr fr ct

