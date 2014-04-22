{-# LANGUAGE RecordWildCards, PolymorphicComponents, ScopedTypeVariables #-}
module AdamAbstractor.TopLevel where

import Control.Monad.ST
import Control.Monad.State
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Applicative

import Text.Parsec hiding ((<|>))
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import Control.Error
import Safe

import Cudd.Imperative

import AdamAbstractor.Analysis
import AdamAbstractor.AST hiding (Pred)
import AdamAbstractor.Parser
import AdamAbstractor.Predicate as Predicate
import AdamAbstractor.Resolve
import AdamAbstractor.CompileHelpers
import AdamAbstractor.Theory

import qualified RefineCommon
import qualified TermiteGame as Game
import Interface

import qualified EqSMTSimple

stdDef = emptyDef {T.reservedNames = reservedNames 
                  ,T.reservedOpNames = reservedOps
                  ,T.identStart = letter <|> char '_'
                  ,T.identLetter = alphaNum <|> char '_'
                  ,T.commentStart = "/*"
                  ,T.commentEnd = "*/"
                  ,T.commentLine = "//"
                  }

data Decls = Decls {
    stateDecls   :: [Decl],
    labelDecls   :: [Decl],
    outcomeDecls :: [Decl]
}

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

lexer = T.makeTokenParser (stdDef {T.reservedNames = T.reservedNames stdDef ++ ["STATE", "LABEL", "OUTCOME", "INIT", "GOAL", "TRANS", "FAIR", "CONT", "LABELCONSTRAINTS"]})

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

makeAbs :: STDdManager s u -> String -> String -> Either String (Game.Abstractor s u (VarType EqPred) (VarType LabEqPred) (), RefineCommon.TheorySolver s u (VarType EqPred) (VarType LabEqPred) String)
makeAbs m fres ivars = do
    (Spec Decls{..} Rels{..}) <- fmapL show $ parse top "" fres
    theMap                    <- doDecls stateDecls labelDecls outcomeDecls
    resolved                  <- Rels <$> resolve theMap init 
                                      <*> mapM (resolve theMap) goal 
                                      <*> mapM (resolve theMap) fair 
                                      <*> resolve theMap cont 
                                      <*> resolve theMap slRel
                                      <*> resolve theMap trans
    res1 <- theAbs m resolved (map (ivFunc theMap) (words ivars))
    return (res1, ts theMap m)

theAbs :: STDdManager s u -> Rels ValType -> [(VarType EqPred, Int, Maybe String)] -> Either String (Game.Abstractor s u (VarType EqPred) (VarType LabEqPred) ())
theAbs m Rels{..} ivars = func <$> updateAbs
    where
    func (R ua)          = Game.Abstractor {..}
        where
        fairAbs ops                 = lift $ mapM (compileBin m ops) fair
        goalAbs ops                 = lift $ mapM (compileBin m ops) goal
        initAbs ops                 = lift $ compileBin m ops init
        contAbs ops                 = lift $ compileBin m ops cont
        stateLabelConstraintAbs ops = lift $ compileBin m ops slRel
        updateAbs x y               = lift $ ua x y
        initialState                = ()
        initialVars                 = ivars
    updateAbs                   =  compileUpdate trans m

ivFunc :: SymTab -> String -> (VarType EqPred, Int, Maybe String)
ivFunc theMap var = case Map.lookup var theMap of
    Nothing                             -> error "ivFunc: var doesnt exist"
    Just (Right _)                      -> error "ivfunc: not a var"
    Just (Left (_, StateSection, size)) -> (Enum var, size, Nothing)
    Just (Left (_, _, _))               -> error "ivfunc: not a state var"

