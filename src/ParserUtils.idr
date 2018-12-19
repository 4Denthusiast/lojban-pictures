module ParserUtils

import Control.Monad.Identity
import Lightyear.Core
import Lightyear.Position

export
peek : ParserT str m a -> ParserT str m a
peek (PT p) = PT (\r, parseOK, emptyOK, parseErr, emptyErr, state => p
        r
        (\x, state' => parseOK x state)
        (\x, state' => emptyOK x state)
        (\errs, state' => parseErr errs state)
        (\errs, state' => emptyErr errs state)
        state
    )

export
implementation Stream a (List a) where
    uncons [] = Nothing
    uncons (x::xs) = Just (x, xs)
    -- This implementation doesn't really make sense, but it isn't possible to do better in the circumstances.
    updatePos tw pos c = let pos' = record {colNo $= (+1)} pos in (pos', pos')

export
lazy : Lazy (ParserT str m a) -> ParserT str m a
lazy p = PT $ \r, us, cs, ue, ce, s => runParserT p r us cs ue ce s

-- Exactly the function from Lightyear.String, but with a trivially generalised type.
export
manyTill : Monad m => ParserT str m a
                   -> ParserT str m b
                   -> ParserT str m (List a)
manyTill p end = scan
    where
        scan : Monad m => ParserT str m (List a)
        scan = do { end; pure List.Nil } <|>
            do { x <- p; xs <- lazy scan; pure (x::xs)}

export
runParser : ParserT str Identity a -> str -> Either String a
runParser p s = getResult $ runIdentity $ execParserT p (initialState Nothing s 8)
    where getResult (MkReply _ r) = case r of
              (Failure es) => Left $ unlines $ msg <$> es
              (Success a) => Right a
