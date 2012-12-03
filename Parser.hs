{-# LANGUAGE RecordWildCards #-}

module Parser where

import Control.Applicative
import Text.Parsec hiding ((<|>), many)
import Text.Parsec.String
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language

import AST
import Predicate

--The lexer
reservedNames = ["case", "true", "false", "if", "abs", "nonabs", "STATE", "LABEL", "INIT", "GOAL", "TRANS"]
reservedOps   = ["!", "&&", "||", "!=", "==", ":=", "<="]

lexer = T.makeTokenParser (emptyDef {T.reservedNames = reservedNames
                                    ,T.reservedOpNames = reservedOps
                                    ,T.identStart = letter <|> char '_'
                                    ,T.identLetter = alphaNum <|> char '_'
                                    ,T.commentStart = "/*"
                                    ,T.commentEnd = "*/"
                                    ,T.commentLine = "//"
                                    })

T.TokenParser {..} = lexer

--Variable declarations

absTyp    = Abs <$ reserved "abs"
nonAbsTyp = NonAbs <$ reserved "nonabs" <*> (fromIntegral <$> natural)
absTypes  = absTyp <|> nonAbsTyp
decl      = Decl <$> (sepBy identifier comma) <* colon <*> absTypes

--Expressions

--The Bin expression parser
binExpr = buildExpressionParser table term
        <?> "expression"

predicate =   (try $ (Pred Eq)  <$> valExpr <* reservedOp "==" <*> valExpr)
          <|> (try $ (Pred Neq) <$> valExpr <* reservedOp "!=" <*> valExpr)

term =   parens binExpr
     <|> TrueE <$ reserved "true" 
     <|> FalseE <$ reserved "false"
     <|> try predicate
     <?> "simple expression"

table = [[prefix "!"  Not]
        ,[binary  "&&" (Bin And) AssocLeft]
        ,[binary  "||" (Bin Or)  AssocLeft]
        ]

binary name fun assoc = Infix  (fun <$ reservedOp name) assoc
prefix name fun       = Prefix (fun <$ reservedOp name) 

--Control expressions
assign   = Assign <$> identifier <* reservedOp ":=" <*> valExpr
signal   = Signal <$> identifier <* reservedOp "<=" <*> valExpr
ccase    = CaseC  <$  reserved "case" <*> braces (sepEndBy ((,) <$> binExpr <* colon <*> ctrlExpr) semi)
conj     = Conj   <$> braces (sepEndBy ctrlExpr semi)
ctrlExpr = conj <|> ccase <|> try assign <|> signal

--Value expressions
lit       = Lit   <$> ((Left <$> identifier) <|> ((Right . fromIntegral) <$> integer))
vcase     = CaseV <$  reserved "case" <*> braces (sepEndBy ((,) <$> binExpr <* colon <*> valExpr) semi)
valExpr   = vcase <|> lit

spec = Spec 
    <$  reserved "STATE"
    <*> sepEndBy decl semi
    <*  reserved "LABEL"
    <*> sepEndBy decl semi
    <*  reserved "INIT"
    <*> binExpr
    <*  reserved "GOAL"
    <*> binExpr
    <*  reserved "TRANS"
    <*> ctrlExpr

top = whiteSpace *> spec <* eof

