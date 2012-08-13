module Main where

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
            print $ show $ varsAssigned ress
    fres <- readFile "exampleval.tsl"
    let res =  parse valExpr "" fres
    case res of 
        Left err -> print err
        Right ress -> do
            print ress
            let (tsl, preds) = valExprToTSL "z" ress
            putDoc $ prettyPrint tsl
            print preds
