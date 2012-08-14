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
                    putDoc $ prettyPrint $ abs1Tsl $ abs1 "z"
                    putStrLn "\n"
                    putDoc $ prettyPrint $ abs2Tsl $ abs2 "z" "v"
