module Resolve (
    resolve,
    resolveBin,
    doDecls
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Traversable

import AST
import Analysis
import Predicate

resolve :: Map String (VarAbsType, Section) -> CtrlExpr String (Either String Int) -> Either String (CtrlExpr String (Either VarInfo Int))
resolve = traverse . func 

resolveBin :: Map String (VarAbsType, Section) -> BinExpr (Either String Int) -> Either String (BinExpr (Either VarInfo Int))
resolveBin = traverse . func

func :: Map String (VarAbsType, Section) -> (Either String Int) -> Either String (Either VarInfo Int)
func mp lit = case lit of 
    Left str -> case Map.lookup str mp of
        Nothing          -> Left  $ "Var doesn't exist: " ++ str
        Just (typ, sect) -> Right $ Left $ VarInfo str typ sect
    Right x -> Right $ Right x

doDecls :: [Decl] -> [Decl] -> [Decl] -> Map String (VarAbsType, Section)
doDecls sd ld od = Map.unions [Map.fromList $ concatMap (go StateSection) sd, Map.fromList $ concatMap (go LabelSection) ld, Map.fromList $ concatMap (go OutcomeSection) od]
    where
    go sect (Decl vars typ) = map go' vars
        where
        go' var = (var, (typ, sect))
