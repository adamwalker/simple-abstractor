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
import Control.Monad.Trans.Either
import Control.Error

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

compileBin :: STDdManager s u -> VarOps pdb TheVarType s u -> BinExpr ValType -> StateT pdb (ST s) (DDNode s u)
compileBin m ops = compile m ops . fst . binExpToTSL

newtype R s u = R {unR :: forall pdb. [(VarType EqPred, [DDNode s u])] -> VarOps pdb TheVarType s u -> StateT pdb (ST s) (DDNode s u)}

compileUpdate :: CtrlExpr String ValType -> STDdManager s u -> Either String (R s u)
compileUpdate ce m = func <$> abstract ce
    where
    func Return{..} = R func2
        where 
        func2 preds ops = do
            x <- mapM (uncurry pred) preds 
            lift $ Backend.conj m x 
            where
            pred (Pred (Predicate.EqVar v1 v2)) = compile m ops . abs2Tsl (abs2Ret v1 v2)       
            pred (Pred (Predicate.EqConst v c)) = compile m ops . equalityConst (abs1Ret v) c
            pred (Enum var)                     = compile m ops . passTSL (either (error "func") id (passRet var))

stdDef = (emptyDef {T.reservedNames = reservedNames 
                   ,T.reservedOpNames = reservedOps
                   ,T.identStart = letter <|> char '_'
                   ,T.identLetter = alphaNum <|> char '_'
                   ,T.commentStart = "/*"
                   ,T.commentEnd = "*/"
                   ,T.commentLine = "//"
                   })

ts :: STDdManager s u -> RefineCommon.TheorySolver s u sp lp
ts m = RefineCommon.TheorySolver ucs ucsl quant
    where
    ucs   = const Nothing
    ucsl  = const $ const Nothing
    quant _ _ = return $ bone m

data Decls = Decls {
    stateDecls   :: [Decl],
    labelDecls   :: [Decl],
    outcomeDecls :: [Decl]
}

lexer = T.makeTokenParser (stdDef {T.reservedNames = T.reservedNames stdDef ++ ["STATE", "LABEL", "OUTCOME", "INIT", "GOAL", "TRANS", "FAIR", "CONT"]})

data Rels a = Rels {
    init         :: BinExpr a,
    goal         :: [BinExpr a],
    fair         :: [BinExpr a],
    cont         :: BinExpr a,
    trans        :: CtrlExpr String a
}

data Spec = Spec {
    decls :: Decls,
    rels  :: Rels (Either String Int)
}

T.TokenParser {..} = lexer

parseDecls = Decls
    <$  reserved "STATE"
    <*> sepEndBy (decl lexer) semi
    <*  reserved "LABEL"
    <*> sepEndBy (decl lexer) semi
    <*  reserved "OUTCOME"
    <*> sepEndBy (decl lexer) semi

parseRels = Rels
    <$  reserved "INIT"
    <*> binExpr lexer
    <*  reserved "GOAL"
    <*> sepEndBy (binExpr lexer) semi
    <*  reserved "FAIR"
    <*> sepEndBy (binExpr lexer) semi
    <*  reserved "CONT"
    <*> binExpr lexer
    <*  reserved "TRANS"
    <*> ctrlExpr lexer

spec = Spec <$> parseDecls <*> parseRels

top = whiteSpace *> spec <* eof

doMain :: IO ()
doMain = runScript $ do
    [fname] <- liftIO $ getArgs
    fres    <- liftIO $ readFile fname
    res     <- hoistEither $ runST $ runEitherT $ do
        m   <- lift $ RefineCommon.setupManager 
        abs <- hoistEither $ do
            (Spec Decls{..} Rels{..}) <- either (Left . show) Right $ parse top "" fres
            let theMap                =  doDecls stateDecls labelDecls outcomeDecls
            resolved                  <- Rels <$> resolve theMap init 
                                              <*> mapM (resolve theMap) goal 
                                              <*> mapM (resolve theMap) fair 
                                              <*> resolve theMap cont 
                                              <*> resolve theMap trans
            theAbs m resolved
        lift $ Game.absRefineLoop m abs (ts m) (error "No abstractor state")
    liftIO $ print res

theAbs :: STDdManager s u -> Rels ValType -> Either String (Game.Abstractor s u (VarType EqPred) (VarType EqPred))
theAbs m Rels{..}  = func <$> updateAbs
    where
    func (R updateAbs) = Game.Abstractor {..}
    fairAbs ops        = mapM (compileBin m ops) fair
    goalAbs ops        = mapM (compileBin m ops) goal
    initAbs ops        = compileBin m ops init
    contAbs ops        = compileBin m ops cont
    updateAbs          = compileUpdate trans m

