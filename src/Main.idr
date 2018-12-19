module Main

import Words
import ParserUtils
import PreParser
import Graph
import Parser
import Render

import Control.Monad.Identity
import Graphics.Color
import Graphics.SDL2.SDL
import Lightyear.Core

addErr : String -> Either String a -> Either String a
addErr e' (Left e) = Left (e' ++ e)
addErr _ (Right x) = Right x

main : IO ()
main = do putStr "Enter a lojban text:\n>"
          jboText <- getLine
          let rawWords = addErr "raw word error:\n" $ runParser wordify jboText
          let words = rawWords >>= addErr "tokenizer error:\n" . runParser tokenize
          let picture = words >>= addErr "parser error:\n" . runParser wholeText
          case picture of
              Left err => putStrLn err
              Right gr => renderPicture gr
