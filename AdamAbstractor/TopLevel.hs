{-# LANGUAGE RecordWildCards, PolymorphicComponents, ScopedTypeVariables #-}
module AdamAbstractor.TopLevel where

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
import Data.EitherR
import Data.Text.Lazy hiding (intercalate, map, take, length)
import Text.PrettyPrint.Leijen.Text (text)

import CuddST
import CuddExplicitDeref

import AdamAbstractor.Analysis
import AdamAbstractor.AST hiding (Pred)
import AdamAbstractor.Backend as Backend
import AdamAbstractor.Parser
import AdamAbstractor.Predicate as Predicate
import AdamAbstractor.Resolve
import qualified RefineCommon
--import qualified RefineGFP
--import qualified RefineLFP
--import qualified RefineReachFair
import qualified TermiteGame as Game
import Interface

compileBin :: STDdManager s u -> VarOps pdb TheVarType s u -> BinExpr ValType -> StateT pdb (ST s) (DDNode s u)
compileBin m ops = compile m ops . fst . binExpToTSL

newtype R s u = R {unR :: forall pdb. [(VarType EqPred, [DDNode s u])] -> VarOps pdb TheVarType s u -> StateT pdb (ST s) ([DDNode s u])}

{-# NOINLINE traceST #-}
traceST :: String -> ST s ()
traceST = unsafeIOToST . putStrLn

compileUpdate :: CtrlExpr String ValType -> STDdManager s u -> Either String (R s u)
compileUpdate ce m = func <$> abstract ce <*> abstract ce
    where
    func ret dbg = R func2
        where 
        func2 preds ops = mapM (uncurry pred) preds 
            where
            pred (Pred (Predicate.EqVar v1 s1 v2 s2)) x = do
                --lift $ traceST $ show $ prettyPrint $ abs2Tsl (abs2Ret dbg v1 s1 v2 s2) (text $ pack $ "next")
                compile m ops $ abs2Tsl (abs2Ret ret v1 s1 v2 s2) x
            pred (Pred (Predicate.EqConst v s c))     x = do
                --lift $ traceST $ show $ prettyPrint $ equalityConst (abs1Ret dbg v) s c (text $ pack $ "next")
                compile m ops $ equalityConst (abs1Ret ret v) s c x
            pred (Enum var)                           x = do
                --lift $ traceST $ show $ prettyPrint $ passTSL (either (error "func") id (passRet dbg var)) (text $ pack $ "next")
                compile m ops $ passTSL (either (error "func") id (passRet ret var)) x

stdDef = emptyDef {T.reservedNames = reservedNames 
                  ,T.reservedOpNames = reservedOps
                  ,T.identStart = letter <|> char '_'
                  ,T.identLetter = alphaNum <|> char '_'
                  ,T.commentStart = "/*"
                  ,T.commentEnd = "*/"
                  ,T.commentLine = "//"
                  }

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

lexer = T.makeTokenParser (stdDef {T.reservedNames = T.reservedNames stdDef ++ ["STATE", "LABEL", "OUTCOME", "INIT", "GOAL", "TRANS", "FAIR", "CONT", "LABELCONSTRAINTS"]})

data Rels a = Rels {
    init         :: BinExpr a,
    goal         :: [BinExpr a],
    fair         :: [BinExpr a],
    cont         :: BinExpr a,
    slRel        :: BinExpr a,
    trans        :: CtrlExpr String a
}

data Spec = Spec {
    decls :: Decls,
    rels  :: Rels (Either (String, Slice) Int)
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
    <*  reserved "LABELCONSTRAINTS"
    <*> binExpr lexer
    <*  reserved "TRANS"
    <*> (AdamAbstractor.AST.Conj <$> sepEndBy (ctrlExpr lexer) semi)

spec = Spec <$> parseDecls <*> parseRels

top = whiteSpace *> spec <* eof

makeAbs :: STDdManager s u -> String -> Either String (Game.Abstractor s u (VarType EqPred) (VarType EqPred))
makeAbs m fres = do
    (Spec Decls{..} Rels{..}) <- fmapL show $ parse top "" fres
    theMap                    <- doDecls stateDecls labelDecls outcomeDecls
    resolved                  <- Rels <$> resolve theMap init 
                                      <*> mapM (resolve theMap) goal 
                                      <*> mapM (resolve theMap) fair 
                                      <*> resolve theMap cont 
                                      <*> resolve theMap slRel
                                      <*> resolve theMap trans
    theAbs m resolved

theAbs :: STDdManager s u -> Rels ValType -> Either String (Game.Abstractor s u (VarType EqPred) (VarType EqPred))
theAbs m Rels{..}  = func <$> updateAbs
    where
    func (R updateAbs)          = Game.Abstractor {..}
    fairAbs ops                 = mapM (compileBin m ops) fair
    goalAbs ops                 = mapM (compileBin m ops) goal
    initAbs ops                 = compileBin m ops init
    contAbs ops                 = compileBin m ops cont
    updateAbs                   = compileUpdate trans m
    stateLabelConstraintAbs ops = compileBin m ops slRel

