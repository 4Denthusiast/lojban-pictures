module Parser

import Graph
import ParserUtils
import PreParser
import Words

import Lightyear.Combinators
import Lightyear.Core
import Lightyear.Strings

WordParser : Type
WordParser = ParserT (List Word) Identity PictureGraph

FloatingWordParser : Type
FloatingWordParser = ParserT (List Word) Identity FloatingPictureGraph

bySelma'o : Selma'o -> WordParser
bySelma'o s = satisfyMaybe (\w => if wordSelma'o w == s then Just (?pictureOf w) else Nothing)

mutual
    withFree : WordParser -> WordParser
    withFree = ?withFree
    
    text : WordParser
    text = foldr (liftA2 graphRootUnion) text1 $ the (List FloatingWordParser) [nais, cmeneOrFrees, emptyOnFail joikJek]
        where nais = emptyOnFail $ map join $ lineRooted' FreeStub SeFreeStub () <$> someWithNonempty (bySelma'o NAI)
              cmeneOrFrees = uproot <$> withFree (join <$> lineRooted' (NumberedStub 1) (NumberedStub 2) () <$> someWithNonempty (bySelma'o Cmevla)) <|> frees <|> ((<+>) <$> (uproot <$> indicators) <*> frees)
              frees : FloatingWordParser
              frees = foldr (<+>) neutral <$> (map uproot <$> many free)
              emptyOnFail p = fromMaybe neutral <$> opt (uproot <$> p)
              lineRooted' : {edgeType : stubType -> stubType -> Type} -> (a:stubType) -> (b:stubType) -> edgeType a b -> (l:List nodeType ** NonEmpty l) -> RootedGraph stubType edgeType nodeType
              lineRooted' x y e (ns**ok) = lineRooted x y e ns {ok}
              someWithNonempty : Monad m => ParserT str m a -> ParserT str m (l:List a ** NonEmpty l)
              someWithNonempty p = (\(x::xs) => ((x::xs)**IsNonEmpty)) <$> some p
    
    text1 : WordParser
    text1 = ?text1
    
    joikJek : WordParser
    joikJek = ?joikJek
    
    free : WordParser
    free = ?free
    
    indicators : WordParser
    indicators = ?indicators
