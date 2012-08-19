{-# LANGUAGE RecordWildCards #-}

module Parser where

import Control.Applicative
import Text.Parsec hiding ((<|>))
import Text.Parsec.String
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language

import AST

--The lexer
reservedNames = ["case", "true", "false", "if"]
reservedOps   = ["!", "&&", "||", "!=", "==", ":="]

lexer = T.makeTokenParser (emptyDef {T.reservedNames = reservedNames
                                    ,T.reservedOpNames = reservedOps
                                    ,T.identStart = letter <|> char '_'
                                    ,T.identLetter = alphaNum <|> char '_'
                                    ,T.commentStart = "/*"
                                    ,T.commentEnd = "*/"
                                    ,T.commentLine = "//"
                                    })

T.TokenParser {..} = lexer

--The Bin expression parser
binExpr = buildExpressionParser table term
        <?> "expression"

predicate =   (try $ (Pred Eq)  <$> valExpr <* reservedOp "==" <*> valExpr)
          <|> (try $ (Pred Neq) <$> valExpr <* reservedOp "!=" <*> valExpr)

term =   parens binExpr
     <|> TrueE <$ reserved "true" 
     <|> FalseE <$ reserved "false"
     <|> try predicate
     <|> Atom <$> identifier
     <?> "simple expression"

table = [[prefix "!"  Not]
        ,[binary  "&&" (Bin And) AssocLeft]
        ,[binary  "||" (Bin Or)  AssocLeft]
        ]

binary name fun assoc = Infix  (fun <$ reservedOp name) assoc
prefix name fun       = Prefix (fun <$ reservedOp name) 

--Control expressions
assign   = Assign <$> identifier <* reservedOp ":=" <*> valExpr
ccase    = CaseC  <$  reserved "case" <*> braces (sepEndBy ((,) <$> binExpr <* colon <*> ctrlExpr) semi)
cif      = IfC    <$  reserved "if" <*> parens binExpr <*> braces ctrlExpr <* reserved "else" <*> braces ctrlExpr
conj     = Conj   <$> braces (sepEndBy ctrlExpr semi)
ctrlExpr = conj <|> ccase <|> cif <|> assign

--Value expressions
stringLit = StringLit <$> identifier
intLit    = IntLit . fromIntegral <$> integer
vcase     = CaseV     <$ reserved "case" <*> braces (sepEndBy ((,) <$> binExpr <* colon <*> valExpr) semi)
vif       = IfV       <$ reserved "if" <*> parens binExpr <*> braces valExpr <* reserved "else" <*> braces valExpr
valExpr   = vif <|> vcase <|> intLit <|> stringLit

top = whiteSpace *> ctrlExpr <* eof

