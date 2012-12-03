module Resolve where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Traversable

import AST
import Analysis
import Predicate

resolve :: Map String (VarAbsType, Section) -> CtrlExpr String (Either String Int) -> Either String (CtrlExpr String (Either VarInfo Int))
resolve mp = traverse func 
    where
    func lit = case lit of 
        Left str -> case Map.lookup str mp of
            Nothing          -> Left  $ "Var doesn't exist: " ++ str
            Just (typ, sect) -> Right $ Left $ VarInfo str typ sect
        Right x -> Right $ Right x
