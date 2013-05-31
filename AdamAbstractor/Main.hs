module Main where

import Control.Monad
import System.Environment
import Data.Maybe
import qualified Data.Map as Map
import Data.Map (Map)

import Data.Text.Lazy hiding (intercalate, map, take, length)
import Text.PrettyPrint.Leijen.Text (putDoc, text)
import Text.Parsec hiding ((<|>))

import Parser
import Analysis
import Predicate
import Backend
import Resolve
import AST

main = do
    [fname, l, r] <- getArgs
    fres <- readFile fname
    let res =  parse top "" fres
    case res of 
        Left err -> print err
        Right (Spec sdecls ldecls init goal ress) -> do
            let theMap = doDecls sdecls ldecls
            case resolve theMap ress of
                Left err -> putStrLn err
                Right resss -> do
                    let res = abstract resss
                    case res of
                        Left err -> print err
                        Right (Return vars abs1 abs2 pass) -> do
                            print vars
                            putStrLn "\n"
                            let res = abs2 l r 
                            putDoc $ prettyPrint $ (abs2Tsl res) (text (pack ("NSPred: " ++ l ++ " == " ++ r)))
                            putStrLn "\n"
                            print $ abs2Preds res
                            let tuples = consistencyPreds $ (catMaybes $ map toVarPair $ abs2Preds res) ++ [("os_lba_hi","read_req_lba_hi_arg")]
                            print tuples
                            putDoc $ prettyPrint $ constraintSection tuples
                            let res = pass "os_st"
                            case res of
                                Left str -> print str
                                Right (PassThroughReturn tsl preds ints vars) -> do
                                    putDoc $ prettyPrint $ tsl (text (pack ("NSVar: " ++ "os_st")))
                                    print preds
                                    print ints
                                    print vars
                            
