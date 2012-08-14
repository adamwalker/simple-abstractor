module Main where

import Control.Monad

import Text.PrettyPrint.Leijen.Text (putDoc)
import Text.Parsec hiding ((<|>))

import Parser
import Analysis
import TSLPP

main = do
    fres <- readFile "example.tsl"
    let res =  parse top "" fres
    case res of 
        Left err -> print err
        Right ress -> do
            let res = varsAssigned ress
            case res of
                Left err -> print err
                Right (Return vars abs1 abs2) -> do
                    print vars
                    putStrLn "\n"
                    let res = abs2 "z" "v"
                    putDoc $ prettyPrint $ abs2Tsl res
                    putStrLn "\n"
                    print $ abs2Preds res
