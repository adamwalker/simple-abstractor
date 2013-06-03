{-# LANGUAGE RecordWildCards #-}

module AdamAbstractor.Parser (
    reservedNames,
    reservedOps,
    decl,
    binExpr,
    ctrlExpr
    ) where

import Control.Applicative
import Text.Parsec hiding ((<|>), many)
import Text.Parsec.String
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language

import AdamAbstractor.AST
import AdamAbstractor.Predicate hiding (Pred)

--The lexer
reservedNames = ["case", "true", "false", "if", "abs", "nonabs"]
reservedOps   = ["!", "&&", "||", "!=", "==", ":=", "<="]

--Variable declarations
absTyp    t@T.TokenParser{..} = Abs <$ reserved "abs"
nonAbsTyp t@T.TokenParser{..} = NonAbs <$ reserved "nonabs" <*> (fromIntegral <$> natural)
absTypes  t@T.TokenParser{..} = absTyp t <|> nonAbsTyp t
decl      t@T.TokenParser{..} = Decl <$> sepBy identifier comma <* colon <*> absTypes t

--Expressions

--The Bin expression parser
binExpr   t@T.TokenParser{..} =   buildExpressionParser (table t) (term t)
                              <?> "expression"

predicate t@T.TokenParser{..} =   try (Pred Eq  <$> valExpr t <* reservedOp "==" <*> valExpr t)
                              <|> try (Pred Neq <$> valExpr t <* reservedOp "!=" <*> valExpr t)

term      t@T.TokenParser{..} =   parens (binExpr t)
                              <|> TrueE <$ reserved "true" 
                              <|> FalseE <$ reserved "false"
                              <|> try (predicate t)
                              <?> "simple expression"

table     t@T.TokenParser{..} = [[prefix t "!"  Not]
                                ,[binary t  "&&" (Bin And) AssocLeft]
                                ,[binary t  "||" (Bin Or)  AssocLeft]
                                ]

binary    t@T.TokenParser{..} name fun assoc = Infix  (fun <$ reservedOp name) assoc
prefix    t@T.TokenParser{..} name fun       = Prefix (fun <$ reservedOp name) 

--Control expressions
assign    t@T.TokenParser{..} = Assign <$> identifier <* reservedOp ":=" <*> valExpr t
signal    t@T.TokenParser{..} = Signal <$> identifier <* reservedOp "<=" <*> valExpr t
ccase     t@T.TokenParser{..} = CaseC  <$  reserved "case" <*> braces (sepEndBy ((,) <$> binExpr t <* colon <*> ctrlExpr t) semi)
conj      t@T.TokenParser{..} = Conj   <$> braces (sepEndBy (ctrlExpr t) semi)
ctrlExpr  t@T.TokenParser{..} = conj t <|> ccase t <|> try (assign t) <|> signal t

--Value expressions
lit       t@T.TokenParser{..} = Lit   <$> ((Left <$> identifier) <|> ((Right . fromIntegral) <$> integer))
vcase     t@T.TokenParser{..} = CaseV <$  reserved "case" <*> braces (sepEndBy ((,) <$> binExpr t <* colon <*> valExpr t) semi)
valExpr   t@T.TokenParser{..} = vcase t <|> lit t
