module PreParser

import ParserUtils
import Words

import Lightyear.Combinators
import Lightyear.Core
import Lightyear.Strings

export
data RawWord = MkRawWord String String

isWordChar : Char -> Bool
isWordChar c = isAlpha c || c == ',' || c == '\''

isVowel : Char -> Bool
isVowel c = elem c (unpack "aeiouyAEIOUY")

makeRawWord : String -> RawWord
makeRawWord s = MkRawWord (pack $ map jboToLower $ unpack $ s) s
    where jboToLower : Char -> Char
          jboToLower 'h' = '\''
          jboToLower c = toLower c

export
wordify : ParserT String Identity (List RawWord)
wordify = concat <$> many (cmavoCompound <|> otherWord) <* eof
    where appendLast : List RawWord -> String -> List RawWord
          appendLast [MkRawWord n f] s = [MkRawWord n (f ++ s)]
          appendLast (w::ws) s = w :: appendLast ws s
          appendSpace : List RawWord -> ParserT String Identity (List RawWord)
          appendSpace ws = appendLast ws <$> pack <$> (some (satisfy (not . isWordChar)) <|> (eof *> pure []))
          cmavo : ParserT String Identity RawWord
          cmavo = do
            cons <- opt (satisfy (\c => isAlpha c && not (isVowel c)))
            coda <- some (satisfy (\c => isVowel c || c == '\'' || c == 'h'))
            let str = pack $ toList cons ++ coda
            pure $ makeRawWord str
          cmavoCompound : ParserT String Identity (List RawWord)
          cmavoCompound = some cmavo >>= appendSpace
          otherWord : ParserT String Identity (List RawWord)
          otherWord = ((::[]) <$> makeRawWord <$> pack <$> some (satisfy isWordChar)) >>= appendSpace

-- Make a custom WordRecord if it's cmevla form.
cmevlaRecord : String -> Maybe WordRecord
cmevlaRecord s = if cmevlaForm $ unpack s then Just $ MkWordRecord Cmevla s s else Nothing
    where cmevlaForm : List Char -> Bool
          cmevlaForm [] = False
          cmevlaForm (c::cs) = not $ isVowel $ last (c::cs)

-- Fallback implementation for brivla so that things parse without me having to make all the pictures.
brivlaRecord : String -> Maybe WordRecord
brivlaRecord s = if brivlaForm $ unpack s then Just $ MkWordRecord Brivla s s else Nothing
    where brivlaForm : List Char -> Bool
          brivlaForm cs = let cs' = map (not . isVowel) cs in foldr (flip (||) . Delay) False $ the (List Bool) $ zipWith (&&) cs' (Delay <$> drop 1 cs')

tryMaybe : Maybe a -> Lazy (Maybe a) -> Maybe a
tryMaybe (Just x) _ = Just x
tryMaybe Nothing  y = y

export
getWordRecord : String -> Maybe WordRecord
getWordRecord s = tryMaybe (findWordRecord s) $ tryMaybe (cmevlaRecord s) (brivlaRecord s)

wordRecordParser : ParserT (List RawWord) Identity WordRecord
wordRecordParser = do
    (MkRawWord s _) <- anyToken
    case getWordRecord s of
        Nothing => fail $ "Unknown word: "++s
        Just wr => pure wr

public export
Tokenizer : Type
Tokenizer = ParserT (List RawWord) Identity (List Word)

mutual
    export
    tokenize : Tokenizer
    tokenize = reverse <$> tokenize' []
    
    tokenize' : List Word -> Tokenizer
    tokenize' ws = (eof *> pure ws) <|> do
        wr <- wordRecordParser
        case selma'o wr of
            BU => tokenizeBU ws
            FAhO => tokenizeFAhO ws
            LOhU => tokenizeLOhU ws
            SI => tokenizeSI ws
            SA => tokenizeSA ws
            SU => tokenizeSU ws
            Y => tokenizeY wr ws
            ZEI => tokenizeZEI ws
            ZO => tokenizeZO ws
            ZOI => tokenizeZOI wr ws
            _ => tokenize' (MkWord wr :: ws)
    
    tokenizeBU : List Word -> Tokenizer
    tokenizeBU [] = fail "No word for BU to absorb."
    tokenizeBU (w::ws) = tokenize' (MagicWordBU w :: ws)
    
    tokenizeFAhO : List Word -> Tokenizer
    tokenizeFAhO = pure
    
    tokenizeLOhU : List Word -> Tokenizer
    tokenizeLOhU ws = do
        ws' <- manyTill (MkWord <$> wordRecordParser) (wordRecordParser >>= (\wr => if selma'o wr == LEhU then pure wr else fail "LEhU expected."))
        tokenize' (MagicWordLOhU ws' :: ws)
    
    tokenizeSI : List Word -> Tokenizer
    tokenizeSI [] = fail "No word for SI to remove."
    tokenizeSI (w::ws) = tokenize' ws
    
    tokenizeSA : List Word -> Tokenizer
    tokenizeSA ws = do
        next <- peek wordRecordParser
        tokenize' (dropWhile ((/= selma'o next) . wordSelma'o) ws)
    
    tokenizeSU : List Word -> Tokenizer
    tokenizeSU = tokenize' . dropWhile (not . flip Prelude.List.elem [NIhO, LU, TUhE, TO] . wordSelma'o)
    
    tokenizeY : WordRecord -> List Word -> Tokenizer
    tokenizeY y ws = do
        next <- peek wordRecordParser
        if selma'o next == BU
            then tokenize' (MkWord y :: ws)
            else tokenize' ws
    
    tokenizeZEI : List Word -> Tokenizer
    tokenizeZEI [] = fail "No word for ZEI to combine."
    tokenizeZEI (w::ws) = tokenize' (MagicWordZEI w (MkWord !wordRecordParser) :: ws)
    
    tokenizeZO : List Word -> Tokenizer
    tokenizeZO ws = tokenize' (MagicWordZO (MkWord !wordRecordParser) :: ws)
    
    trimZOI : String -> String
    trimZOI = pack . Prelude.List.reverse . dropWhile isSpace . dropWhile (=='.') . reverse . dropWhile isSpace . dropWhile (=='.') . dropWhile isWordChar . unpack
    
    tokenizeZOI : WordRecord -> List Word -> Tokenizer
    tokenizeZOI wr ws = do
        (MkRawWord d d') <- anyToken
        quote <- Prelude.Foldable.concat <$> map (\(MkRawWord _ t) => t) <$> manyTill anyToken (satisfy (\(MkRawWord w _) => w == d))
        tokenize' (MagicWordZOI wr (trimZOI (d' ++ quote)) :: ws)
