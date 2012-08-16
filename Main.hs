module Main where

import Control.Monad
import System.Environment

import Text.PrettyPrint.Leijen.Text (putDoc)
import Text.Parsec hiding ((<|>))

import Parser
import Analysis
import TSLPP

main = do
    [fname, l, r] <- getArgs
    fres <- readFile fname
    let res =  parse top "" fres
    case res of 
        Left err -> print err
        Right ress -> do
            let res = abstract ress
            case res of
                Left err -> print err
                Right (Return vars abs1 abs2 pass) -> do
                    print vars
                    putStrLn "\n"
                    let res = abs2 l r 
                    putDoc $ prettyPrint $ abs2Tsl res
                    putStrLn "\n"
                    print $ abs2Preds res
                    let res = pass "os_st"
                    case res of
                        Left str -> print str
                        Right (PassThroughReturn tsl preds) -> do
                            putDoc $ prettyPrint $ tsl
                            print preds
                            
