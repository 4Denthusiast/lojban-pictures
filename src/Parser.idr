module Parser

import Graph
import ParserUtils
import PreParser
import Words

import Lightyear.Combinators
import Lightyear.Core
import Lightyear.Strings

-- TODO: allow superfluous "I", as in the reference grammar.

WordParser : Type
WordParser = ParserT (List Word) Identity PictureGraph

FloatingWordParser : Type
FloatingWordParser = ParserT (List Word) Identity FloatingPictureGraph

bySelma'o : Selma'o -> WordParser
bySelma'o s = satisfyMaybe (\w => if wordSelma'o w == s then Just (pictureOf w) else Nothing)
    where pictureOf : Word -> PictureGraph
          pictureOf (MkWord wr) = pure $ picture wr
          pictureOf (MagicWordBU w) = ?pictureOfBU w
          pictureOf (MagicWordZO w) = ?pictureOfZO w
          pictureOf (MagicWordZOI wr s) = ?pictureOfZOI wr s
          pictureOf (MagicWordZEI w w') = ?pictureOfZEI w w'
          pictureOf (MagicWordLOhU ws) = ?pictureOfLOhU ws

findWordPicture : String -> PictureGraph
findWordPicture = ?findWordPicture

createNi'os : Nat -> PictureGraph
createNi'os Z = findWordPicture "i"
createNi'os (S n) = join $ lineRooted (NumberedStub 3) (NumberedStub 4) () (replicate (S n) $ findWordPicture "ni'o")

-- A shorthand for the most common case of taggedStarGraph
pictureTaggedStarGraph : PictureGraph -> List (Nat, Nat, PictureGraph) -> PictureGraph
pictureTaggedStarGraph r ls = join $ taggedStarGraph r $ map (\(a, b, l) => ((NumberedStub a**NumberedStub b**()), l)) ls

mutual
    withFree : WordParser -> WordParser
    withFree p = join <$> (starGraph FreeStub SeFreeStub () <$> p <*> many free)
    
    text : FloatingWordParser
    text = foldr (liftA2 (<+>)) (pure neutral) $ the (List _) [nais, cmeneOrFrees, emptyOnFail joikJek, emptyOnFail text1]
        where nais = emptyOnFail $ map join $ lineRooted' FreeStub SeFreeStub () <$> someWithNonempty (bySelma'o NAI)
              cmeneOrFrees = uproot <$> withFree (join <$> lineRooted' (NumberedStub 1) (NumberedStub 2) () <$> someWithNonempty (bySelma'o Cmevla)) <|> frees <|> ((<+>) <$> (uproot <$> indicators) <*> frees)
              frees : FloatingWordParser
              frees = foldr (<+>) neutral <$> (map uproot <$> many free)
              emptyOnFail p = fromMaybe neutral <$> opt (uproot <$> p)
              lineRooted' : {edgeType : stubType -> stubType -> Type} -> (a:stubType) -> (b:stubType) -> edgeType a b -> (l:List nodeType ** NonEmpty l) -> RootedGraph stubType edgeType nodeType
              lineRooted' x y e (ns**ok) = lineRooted x y e ns {ok}
              someWithNonempty : Monad m => ParserT str m a -> ParserT str m (l:List a ** NonEmpty l)
              someWithNonempty p = (\(x::xs) => ((x::xs)**IsNonEmpty)) <$> some p
    
    -- varied in structure from the source to account for paragraph levels.
    text1 : WordParser
    text1 = (withFree (bySelma'o I) >>= anyParagraphs 0) <|> (ni'os >>= uncurry anyParagraphs) <|> anyParagraphs 0 (findWordPicture "i")
    
    -- a sequence of paragraphs starting at a given NIhO level, but possibly going higher.
    anyParagraphs : Nat -> PictureGraph -> WordParser
    anyParagraphs n init =
        do par <- paragraphs n init
           anyParagraphs' n par
    
    anyParagraphs' : Nat -> PictureGraph -> WordParser
    anyParagraphs' n par0 =
        do ni'o' <- opt $ ni'os
           case ni'o' of
               Nothing => pure par0
               (Just (l, ni'o)) => do
                   par <- paragraphs l ni'o
                   anyParagraphs' l $ pictureTaggedStarGraph (upgradeNi'o l) [(1,0,par)]
        where upgradeNi'o : Nat -> PictureGraph
              upgradeNi'o l with (l <= n)
                  | True  = par0
                  | False with (l)
                      | S l' = pictureTaggedStarGraph (createNi'os l) [(2,0, upgradeNi'o l')]
    
    -- a sequence of paragraphs with no more than n NIhO
    paragraphs : Nat -> PictureGraph -> WordParser
    paragraphs n init = case n of
        Z    => paragraph
        S n' => do par <- paragraphs n' (createNi'os n')
                   (pictureTaggedStarGraph init . ((2,0,par)::)) <$> (
                       do (l, init') <- ni'os
                          if l > n then fail "high level paragraph inside a lower-level one" else pure ()
                          next <- paragraphs n init'
                          pure [(1,0,next)]
                       <|> pure []
                    )
    
    ni'os : ParserT (List Word) Identity (Nat, PictureGraph)
    ni'os = chainr1 ((\n => (1,n)) <$> bySelma'o NIhO) (pure (\(a,n), (b,ns) => (a+b,pictureTaggedStarGraph n [(4,3,ns)])))
    
    paragraph : WordParser
    paragraph = ?paragraph
    
    joikJek : WordParser
    joikJek = ?joikJek
    
    free : WordParser
    free = ?free
    
    indicators : WordParser
    indicators = ?indicators
