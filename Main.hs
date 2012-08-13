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
            print ress
            let res = varsAssigned ress
            case res of
                Left err -> print err
                Right (Return vars abs1 abs2) -> do
                    print vars
                    putDoc $ prettyPrint $ abs1 "z"
                    putDoc $ prettyPrint $ abs2 "z" "v"
    fres <- readFile "exampleval.tsl"
    let res =  parse valExpr "" fres
    case res of 
        Left err -> print err
        Right ress -> do
            print ress
            let (tsl, preds) = valExprToTSL "z" ress
            putDoc $ prettyPrint tsl
            print preds