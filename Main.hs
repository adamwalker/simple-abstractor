module Main where

import Control.Monad
import System.Environment
import Data.Maybe
import qualified Data.Map as Map
import Data.Map (Map)

import Text.PrettyPrint.Leijen.Text (putDoc)
import Text.Parsec hiding ((<|>))

import Parser
import Analysis
import Predicate
import Backend
import Resolve

main = do
    [fname, l, r] <- getArgs
    fres <- readFile fname
    let res =  parse top "" fres
    case res of 
        Left err -> print err
        Right ress -> do
            let theMap = Map.fromList [("dev_lba_low", (Abs, StateSection)), ("dev_lba_hi", (Abs, StateSection)), ("os_lba_low", (Abs, StateSection)), ("os_lba_hi", (Abs, StateSection)), ("dev_st", (NonAbs 5, StateSection)), ("os_st", (NonAbs 6, StateSection)), ("cont", (NonAbs 5, LabelSection)), ("ctag", (NonAbs 5, LabelSection)), ("addr", (NonAbs 5, LabelSection)), ("dev_sect", (Abs, StateSection)), ("class_sect_written", (NonAbs 5, LabelSection)), ("class_lba_low", (Abs, LabelSection)), ("write8_arg", (Abs, LabelSection)), ("utag", (NonAbs 5, StateSection)), ("read_req_lba_low_arg", (Abs, StateSection)), ("read_req_lba_hi_arg", (Abs, StateSection))]
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
                            putDoc $ prettyPrint $ abs2Tsl res
                            putStrLn "\n"
                            print $ abs2Preds res
                            let tuples = consistencyPreds $ (catMaybes $ map toVarPair $ abs2Preds res) ++ [("os_lba_hi","read_req_lba_hi_arg")]
                            print tuples
                            putDoc $ prettyPrint $ constraintSection tuples
                            let res = pass "os_st"
                            case res of
                                Left str -> print str
                                Right (PassThroughReturn tsl preds ints vars) -> do
                                    putDoc $ prettyPrint $ tsl
                                    print preds
                                    print ints
                                    print vars
                            
