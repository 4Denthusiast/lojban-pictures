module Parser

import Graph
import PreParser
import Words

import Lightyear.Combinators
import Lightyear.Core

WordParser : Type
WordParser = ParserT (List Word) Identity PictureGraph

mutual
    text : WordParser
    text = foldr maybeRootedUnionR <$> text1 <*> sequence [opt nais, opt (withFree cmenes) <|> maybeRootedUnion (opt indicators)
