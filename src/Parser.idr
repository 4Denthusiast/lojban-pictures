module Parser

import Graph
import ParserUtils
import PreParser
import Words

import Lightyear.Combinators
import Lightyear.Core
import Lightyear.Strings

WordParser : Nat -> Type
WordParser i = ParserT (List Word) Identity (PictureGraph i)

bySelma'o : Selma'o -> WordParser 1
bySelma'o s = satisfyMaybe (\w => if wordSelma'o w == s then Just (pictureOf w) else Nothing)
    where pictureOf : Word -> PictureGraph 1
          pictureOf (MkWord wr) = pure $ picture wr
          pictureOf (MagicWordBU w) = ?pictureOfBU w
          pictureOf (MagicWordZO w) = ?pictureOfZO w
          pictureOf (MagicWordZOI wr s) = ?pictureOfZOI wr s
          pictureOf (MagicWordZEI w w') = ?pictureOfZEI w w'
          pictureOf (MagicWordLOhU ws) = ?pictureOfLOhU ws

findWordPicture : String -> PictureGraph 1
findWordPicture = ?findWordPicture

-- junction to indicate multiple nodes in the same place
confluencePicture : PictureGraph 1
confluencePicture = pure ()

-- sort of like CU, a circle enclosing the main selbri of a sentence.
bridiCircle : PictureGraph 1
bridiCircle = pure ()

createNi'os : Nat -> PictureGraph 1
createNi'os Z = findWordPicture "i"
createNi'os (S n) = join $ the (Graph 1 _ _ _) $ uproot $ lineGraph (NumberedStub 3) (NumberedStub 4) () (replicate (S n) $ findWordPicture "ni'o")

-- For each term, a record of how it relates to the place structure
data TagType = MiscTag | PlainTag | FaTag Nat | NaTag

-- The place corresponding to a given FA cmavo
faTagType : PictureGraph 1 -> TagType
faTagType = faTagType' . getRoot 0
    where faTagType' () = FaTag 0

-- A shorthand for the most common case of taggedStarGraph
pictureTaggedStarGraph : {n:Nat} -> PictureGraph (S n) -> List (Nat, Nat, PictureGraph 1) -> PictureGraph (S n)
pictureTaggedStarGraph = foldr addLeaf
    where addLeaf : {n:Nat} -> (Nat, Nat, PictureGraph 1) -> PictureGraph (S n) -> PictureGraph (S n)
          addLeaf {n} (a,b,l) r = permuteRoots init $ replace {P=PictureGraph} (plusCommutative (S n) 1) $ addEdge 0 last (NumberedStub a) (NumberedStub b) () $ graphUnion r l

formBridi : PictureGraph 1 -> List (TagType, Maybe (PictureGraph 1)) -> PictureGraph 1
formBridi s ts = permuteRoots (\[b,a] => [a]) $ flip (pictureTaggedStarGraph {n=1}) (fst $ snd processedTerms) $ permuteRoots (\[a,b] => [b,a]) $ enclosePicture (pictureTaggedStarGraph bridiCircle (fst processedTerms)) s
    where add : Maybe a -> Nat -> Nat -> List (Nat,Nat,a) -> List (Nat,Nat,a)
          add Nothing _ _ xs = xs
          add (Just x) n n' xs = (n,n',x)::xs
          processedTerms : (List (Nat, Nat, PictureGraph 1), List (Nat, Nat, PictureGraph 1), Nat)
          processedTerms = foldr (\(tt, t), (mtags, ntags, n) => case tt of
              MiscTag => (add t 1 0 mtags, ntags, n)
              PlainTag => (mtags, add t n 0 ntags, n+1)
              FaTag n' => (mtags, add t n' 0 ntags, n'+1)
              NaTag => ?dealWithNaTagType
          ) ([],[],0) ts

mutual
    withFree : WordParser 1 -> WordParser 1
    withFree p = join <$> (starGraph FreeStub SeFreeStub () <$> p <*> many free)
    
    -- TODO: allow superfluous "I", as in the reference grammar.
    text : WordParser 0
    text = foldr (liftA2 (<+>)) (pure neutral) $ the (List _) [nais, cmeneOrFrees, emptyOnFail joikJek, emptyOnFail text1]
        where nais = emptyOnFail $ map join $ lineGraph' FreeStub SeFreeStub () <$> someWithNonempty (bySelma'o NAI)
              cmeneOrFrees = uproot <$> withFree (join <$> lineGraph' (NumberedStub 1) (NumberedStub 2) () <$> someWithNonempty (bySelma'o Cmevla)) <|> frees <|> ((<+>) <$> (uproot <$> indicators) <*> frees)
              frees : WordParser 0
              frees = foldr (<+>) neutral <$> (map uproot <$> many free)
              emptyOnFail p = fromMaybe neutral <$> opt (uproot <$> p)
              lineGraph' : {edgeType : stubType -> stubType -> Type} -> (a:stubType) -> (b:stubType) -> edgeType a b -> (l:List nodeType ** NonEmpty l) -> Graph 1 stubType edgeType nodeType
              lineGraph' x y e (ns**ok) = uproot $ lineGraph x y e ns {ok}
              someWithNonempty : Monad m => ParserT str m a -> ParserT str m (l:List a ** NonEmpty l)
              someWithNonempty p = (\(x::xs) => ((x::xs)**IsNonEmpty)) <$> some p
    
    -- varied in structure from the source to account for paragraph levels.
    text1 : WordParser 1
    text1 = (withFree (bySelma'o I) >>= anyParagraphs 0) <|> (ni'os >>= uncurry anyParagraphs) <|> anyParagraphs 0 (findWordPicture "i")
    
    -- a sequence of paragraphs starting at a given NIhO level, but possibly going higher.
    anyParagraphs : Nat -> PictureGraph 1 -> WordParser 1
    anyParagraphs n init =
        do par <- paragraphs n init
           anyParagraphs' n par
    
    anyParagraphs' : Nat -> PictureGraph 1 -> WordParser 1
    anyParagraphs' n par0 =
        do ni'o' <- opt $ ni'os
           case ni'o' of
               Nothing => pure par0
               (Just (l, ni'o)) => do
                   par <- paragraphs l ni'o
                   anyParagraphs' l $ pictureTaggedStarGraph (upgradeNi'o l) [(1,0,par)]
        where upgradeNi'o : Nat -> PictureGraph 1
              upgradeNi'o l with (l <= n)
                  | True  = par0
                  | False with (l)
                      | S l' = pictureTaggedStarGraph (createNi'os l) [(2,0, upgradeNi'o l')]
    
    -- a sequence of paragraphs with no more than n NIhO
    paragraphs : Nat -> PictureGraph 1 -> WordParser 1
    paragraphs n init = case n of
        Z    => paragraph init
        S n' => do par <- paragraphs n' (createNi'os n')
                   (pictureTaggedStarGraph init . ((2,0,par)::)) <$> (
                       do (l, init') <- ni'os
                          if l > n then fail "high level paragraph inside a lower-level one" else pure ()
                          next <- paragraphs n init'
                          pure [(1,0,next)]
                       <|> pure []
                    )
    
    ni'os : ParserT (List Word) Identity (Nat, PictureGraph 1)
    ni'os = chainr1 ((\n => (1,n)) <$> bySelma'o NIhO) (pure (\(a,n), (b,ns) => (a+b,pictureTaggedStarGraph n [(4,3,ns)])))
    
    paragraph : PictureGraph 1 -> WordParser 1
    paragraph init = do
        st <- statement <|> fragment
        (pictureTaggedStarGraph init . ((2,0,st)::)) <$> (
            do i <- withFree (bySelma'o I)
               par <- paragraph i
               pure [(1,0,par)]
            <|> pure []
        )
    
    statement : WordParser 1
    statement = flip (foldr (\px, st => pictureTaggedStarGraph px [(1,0,st)])) <$> many prenex <*> statement1
    
    statement1 : WordParser 1
    statement1 = chainl1 statement2 ((\j, sl, sr => pictureTaggedStarGraph j [(1,0,sl),(2,0,sl)]) <$> (bySelma'o I *> joikJek))
    
    -- TODO: fix "co'e .i je bai je bai bo co'e"
    statement2 : WordParser 1
    statement2 = chainr1 statement3 (f <$> (bySelma'o I) <*> (jek <|> joik <|> pure (findWordPicture "ju'e")) <*> opt stag <*> bySelma'o BO)
        where f i j s b sl sr = pictureTaggedStarGraph j ([(1,0,sl),(2,0,sr)] ++ catMaybes [(\s => (3,3,s)) <$> s])
    
    statement3 : WordParser 1
    statement3 = sentence <|> do
        bySelma'o TUhE
        fs <- many free
        t <- text1
        fe <- fromMaybe [] <$> opt (bySelma'o TUhU *> many free)
        pure $ join $ (starGraph FreeStub SeFreeStub () t (fs ++ fe))
    
    fragment : WordParser 1
    fragment =
        withFree ek
        <|> withFree gihek
        <|> quantifier
        <|> withFree (bySelma'o NA)
        <|> (joinedTerms <* bySelma'o VAU) --TODO: work out what to do with the free modifiers here.
        <|> prenex
        <|> relativeClauses
        <|> links
        <|> linkArgs
    
    prenex : WordParser 1
    prenex = do
        t <- joinedTerms
        z <- withFree (bySelma'o ZOhU)
        pure $ pictureTaggedStarGraph z [(2,0,t)]
    
    sentence : WordParser 1
    sentence = do
        ts <- fromMaybe [] <$> opt (terms <* opt (bySelma'o CU))
        bridiTail ts
    
    subsentence : WordParser 1
    subsentence = flip (foldr (\px, ss => pictureTaggedStarGraph px [(1,0,ss)])) <$> many prenex <*> sentence
    
    -- TODO: bridi-tail conjunctions
    bridiTail : List (TagType, Maybe (PictureGraph 1)) -> WordParser 1
    bridiTail ts0 = do
        s <- selbri
        ts1 <- tailTerms
        pure $ formBridi s (ts0 ++ ts1)
    
    -- Multiple terms as a single node, for uses other than sentences.
    joinedTerms : WordParser 1
    joinedTerms = pictureTaggedStarGraph confluencePicture <$> map (\s => (1,0,s)) <$> catMaybes <$> map snd <$> terms
    
    tailTerms : ParserT (List Word) Identity (List (TagType, Maybe (PictureGraph 1)))
    tailTerms = fail "tailTerms not yet implemented."
    
    -- TODO: termsets
    terms : ParserT (List Word) Identity (List (TagType, Maybe (PictureGraph 1)))
    terms = some $
            map (\s => (PlainTag, Just s)) sumti
            <|> ((\t, s => (MiscTag, s)) <$> tag <*> maybeSumti)
            <|> ((\t, s => (faTagType t, s)) <$> bySelma'o FA <*> maybeSumti)
            <|> ((\n => (NaTag, Just n)) <$> (withFree $ bySelma'o NA <* bySelma'o KU))
        where maybeSumti = (Just <$> sumti) <|> (bySelma'o KU *> pure Nothing)
    
    sumti : WordParser 1
    sumti = fail "sumti not yet implemented."
    
    relativeClauses : WordParser 1
    relativeClauses = fail "relativeClauses not yet implemented."
    
    selbri : WordParser 1
    selbri = fail "selbri not yet implemented."
    
    linkArgs : WordParser 1
    linkArgs = fail "linkArgs not yet implemented."
    
    links : WordParser 1
    links = fail "links not yet implemented."
    
    quantifier : WordParser 1
    quantifier = fail "quantifier not yet implemented."
    
    ek : WordParser 1
    ek = fail "ek not yet implemented."
    
    gihek : WordParser 1
    gihek = fail "gihek not yet implemented."
    
    jek : WordParser 1
    jek = fail "jek not yet implemented."
    
    joik : WordParser 1
    joik = fail "joik not yet implemented."
    
    joikJek : WordParser 1
    joikJek = fail "joikJek not yet implemented."
    
    tag : WordParser 1
    tag = fail "tag not yet implemented."
    
    stag : WordParser 1
    stag = fail "stag not yet implemented."
    
    free : WordParser 1
    free = fail "free not yet implemented."
    
    indicators : WordParser 1
    indicators = fail "indicators not yet implemented."
