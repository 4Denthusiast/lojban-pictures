module Parser

import Graph
import ParserUtils
import PreParser
import Words

import Control.Monad.Identity
import Data.Fin
import Data.Vect
import Lightyear.Combinators
import Lightyear.Core

public export
Parser : Type -> Type
Parser = ParserT (List Word) Identity

public export
WordParser : Nat -> Type
WordParser i = Parser (PictureGraph i)

findWordPicture : String -> WordParser 1
findWordPicture w = case getWordRecord w of
    Nothing => fail ("No such word: "++w)
    Just wr => pure $ pure $ picture wr

-- junction to indicate multiple nodes in the same place
confluencePicture : PictureGraph 1
confluencePicture = pure $ MkWordPicture "" $ \_, s => case s of
    NumberedStub    Z  => Just $ MkStubPos [0,0] [0,1]
    NumberedStub (S Z) => Just $ MkStubPos [0,0] [0,-1]
    _ => Nothing

quantifierPicture : PictureGraph 1
quantifierPicture = pure $ MkWordPicture "│├" $ \_, s => case s of
    NumberedStub       Z   => Just $ MkStubPos [0, 0.5] [0,1]
    NumberedStub    (S Z)  => Just $ MkStubPos [0,-0.5] [0,-1]
    NumberedStub (S (S Z)) => Just $ MkStubPos [0.2,0] [1,0]
    _ => Nothing

-- sort of like CU, a circle enclosing the main selbri of a sentence.
bridiCircle : PictureGraph 1
bridiCircle = pure $ MkWordPicture "○" $ \_, s => case s of
    NumberedStub Z => Just $ MkStubPos [0,1] [0,1]
    _ => Nothing

createNi'os : Nat -> WordParser 1
createNi'os Z = findWordPicture "i"
createNi'os (S n) = (\ni'o => join $ uproot {i'=1} $ lineGraph (NumberedStub 3) (NumberedStub 4) () $ replicate (S n) ni'o) <$> findWordPicture "ni'o"

-- For each term, a record of how it relates to the place structure
data TagType = MiscTag | PlainTag | FaTag Nat | NaTag

Terms : Type
Terms = List (TagType, Maybe (PictureGraph 1))

-- The place corresponding to a given FA cmavo
faTagType : PictureGraph 1 -> TagType
faTagType = faTagType' . getRoot 0
    where faTagType' f = FaTag $ case string f of
              "fa" => 0
              "fe" => 1
              "fi" => 2
              "fo" => 3
              "fu" => 4

-- A shorthand for the most common case of taggedStarGraph
pictureTaggedStarGraph : {n:Nat} -> PictureGraph (S n) -> List (Nat, Nat, PictureGraph 1) -> PictureGraph (S n)
pictureTaggedStarGraph = foldr addLeaf
    where addLeaf : {n:Nat} -> (Nat, Nat, PictureGraph 1) -> PictureGraph (S n) -> PictureGraph (S n)
          addLeaf {n} (a,b,l) r = permuteRoots init $ replace {P=PictureGraph} (plusCommutative (S n) 1) $ addEdge 0 last (NumberedStub a) (NumberedStub b) () $ graphUnion r l

freeJoin : PictureGraph 1 -> PictureGraph 1 -> PictureGraph 1
freeJoin x f = uproot {i=2} $ addEdge 0 1 FreeStub SeFreeStub () $ graphUnion x f

tanruJoin : PictureGraph 1 -> PictureGraph 1 -> PictureGraph 1
tanruJoin s0 s1 = uproot {i=2} $ addEdge 1 0 TertauStub SeltauStub () $ graphUnion s1 s0

relativeClauseJoin : PictureGraph 1 -> PictureGraph 2 -> PictureGraph 1
relativeClauseJoin m r = uproot {i=3} $ addEdge 1 2 (NumberedStub 1) (NumberedStub 0) () $ graphUnion r m

maybeRelativeClauseJoin : PictureGraph 1 -> Maybe (PictureGraph 2) -> PictureGraph 1
maybeRelativeClauseJoin m (Just r) = relativeClauseJoin m r
maybeRelativeClauseJoin m Nothing  = m

simpleStar : {n:Nat} -> Nat -> Nat -> PictureGraph (S n) -> PictureGraph 1 -> PictureGraph (S n)
simpleStar a b h t = pictureTaggedStarGraph h [(a,b,t)]

bySelma'o : Selma'o -> WordParser 1
bySelma'o s = join $ satisfyMaybe (\w => if wordSelma'o w == s then Just (pictureOf w) else Nothing)
    where pictureOf : Word -> WordParser 1
          pictureOf (MkWord wr) = pure $ pure $ picture wr
          pictureOf (MagicWordBU w) = uproot {i=2} {i'=1} <$> (enclosePicture <$> findWordPicture "bu" <*> pictureOf w)
          pictureOf (MagicWordZO w) = simpleStar 1 0 <$> findWordPicture "zo" <*> pictureOf w
          pictureOf (MagicWordZOI wr s) = ?pictureOfZOI wr s
          pictureOf (MagicWordZEI w w') = ?pictureOfZEI w w'
          pictureOf (MagicWordLOhU ws) = ?pictureOfLOhU ws

formBridi : PictureGraph 1 -> Terms -> PictureGraph 1
formBridi s ts = permuteRoots (\[b,a] => [a]) $ flip (pictureTaggedStarGraph {n=1}) (fst $ snd processedTerms) $ permuteRoots (\[a,b] => [b,a]) $ enclosePicture (pictureTaggedStarGraph bridiCircle (fst processedTerms)) s
    where add : Maybe a -> Nat -> Nat -> List (Nat,Nat,a) -> List (Nat,Nat,a)
          add Nothing _ _ xs = xs
          add (Just x) n n' xs = (n,n',x)::xs
          processedTerms : (List (Nat, Nat, PictureGraph 1), List (Nat, Nat, PictureGraph 1), Nat)
          processedTerms = foldl (\(mtags, ntags, n), (tt, t) => case tt of
              MiscTag => (add t 1 0 mtags, ntags, n)
              PlainTag => (mtags, add t n 0 ntags, n+1)
              FaTag n' => (mtags, add t n' 0 ntags, n'+1)
              NaTag => ?dealWithNaTagType
          ) ([],[],0) ts

mutual
    export
    wholeText : WordParser 0
    wholeText = (<?> "whole text") $ text <* eof
    
    withFree : WordParser 1 -> WordParser 1
    withFree p = join <$> (starGraph FreeStub SeFreeStub () <$> p <*> many free)
    
    -- TODO: allow superfluous "I", as in the reference grammar.
    text : WordParser 0
    text = (<?> "text") $ foldr (liftA2 (<+>)) (pure neutral) $ the (List _) [nais, cmeneOrFrees, emptyOnFail joikJek, emptyOnFail text1]
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
    text1 = (<?> "text1") $ (withFree (bySelma'o I) >>= anyParagraphs 0) <|> (ni'os >>= uncurry anyParagraphs) <|> (findWordPicture "i" >>= anyParagraphs 0)
    
    -- a sequence of paragraphs starting at a given NIhO level, but possibly going higher.
    anyParagraphs : Nat -> PictureGraph 1 -> WordParser 1
    anyParagraphs n init = (<?> ("anyParagraphs "++cast n)) $
        do par <- paragraphs n init
           anyParagraphs' n par
    
    anyParagraphs' : Nat -> PictureGraph 1 -> WordParser 1
    anyParagraphs' n par0 = (<?> ("anyParagraphs' "++cast n)) $
        do ni'o' <- opt $ ni'os
           case ni'o' of
               Nothing => pure par0
               (Just (l, ni'o)) => do
                   par <- paragraphs l ni'o
                   par0' <- upgradeNi'o l
                   anyParagraphs' l $ simpleStar 1 0 par0' par
        where upgradeNi'o : Nat -> WordParser 1
              upgradeNi'o l with (l <= n)
                  | True  = pure $ par0
                  | False with (l)
                      | S l' = simpleStar 2 0 <$> (createNi'os l) <*> upgradeNi'o l'
    
    -- a sequence of paragraphs with no more than n NIhO
    paragraphs : Nat -> PictureGraph 1 -> WordParser 1
    paragraphs n init =  (<?> ("paragraphs "++cast n)) $case n of
        Z    => paragraph init
        S n' => do par <- createNi'os n' >>= paragraphs n'
                   (pictureTaggedStarGraph init . ((2,0,par)::)) <$> (
                       do (l, init') <- ni'os
                          if l > n then fail "high level paragraph inside a lower-level one" else pure ()
                          next <- lazy $ paragraphs n init'
                          pure [(1,0,next)]
                       <|> pure []
                    )
    
    ni'os : Parser (Nat, PictureGraph 1)
    ni'os = (<?> "ni'o string") $ chainr1 ((\n => (1,n)) <$> bySelma'o NIhO) (pure (\(a,n), (b,ns) => (a+b,simpleStar 4 3 n ns)))
    
    paragraph : PictureGraph 1 -> WordParser 1
    paragraph init = (<?> "paragraph") $ do
        st <- statement <|> fragment
        (pictureTaggedStarGraph init . ((2,0,st)::)) <$> (
            do i <- withFree (bySelma'o I)
               par <- lazy $ paragraph i
               pure [(1,0,par)]
            <|> pure []
        )
    
    statement : WordParser 1
    statement = (<?> "statement") $ flip (foldr (simpleStar 1 0)) <$> many prenex <*> statement1
    
    statement1 : WordParser 1
    statement1 = (<?> "statement1") $ chainl1 statement2 ((\j, sl, sr => pictureTaggedStarGraph j [(1,0,sl),(2,0,sl)]) <$> (bySelma'o I *> joikJek))
    
    -- TODO: fix "co'e .i je bai je bai bo co'e"
    statement2 : WordParser 1
    statement2 = (<?> "statement2") $ chainr1 statement3 (f <$> (bySelma'o I) <*> (jek <|> joik <|> findWordPicture "ju'e") <*> opt stag <*> bySelma'o BO)
        where f i j s b sl sr = pictureTaggedStarGraph j ([(1,0,sl),(2,0,sr)] ++ catMaybes [(\s => (3,3,s)) <$> s])
    
    statement3 : WordParser 1
    statement3 = (<?> "statement3") $ sentence <|> do
        bySelma'o TUhE
        fs <- many free
        t <- lazy text1
        fe <- fromMaybe [] <$> opt (bySelma'o TUhU *> many free)
        pure $ join $ (starGraph FreeStub SeFreeStub () t (fs ++ fe))
    
    fragment : WordParser 1
    fragment = (<?> "fragment") $
        withFree ek
        <|> withFree gihek
        <|> quantifier
        <|> withFree (bySelma'o NA)
        <|> (joinedTerms <* opt (bySelma'o VAU)) --TODO: work out what to do with the free modifiers here.
        <|> prenex
        <|> uproot {i=2} {i'=1} <$> relativeClauses
        <|> links
        <|> linkArgs
    
    prenex : WordParser 1
    prenex = (<?> "prenex") $ flip (simpleStar 2 0) <$> withFree (bySelma'o ZOhU) <*> joinedTerms
    
    sentence : WordParser 1
    sentence = (<?> "sentence") $ do
        ts <- fromMaybe [] <$> opt (terms <* opt (bySelma'o CU))
        bridiTail ts
    
    subsentence : WordParser 1
    subsentence = (<?> "subsentence") $ flip (foldr (simpleStar 1 0)) <$> many (lazy prenex) <*> (lazy sentence)
    
    -- TODO: bridi-tail conjunctions
    bridiTail : Terms -> WordParser 1
    bridiTail ts0 = (<?> "bridi-tail") $ do
        (s, ts1) <- selbri
        ts2 <- tailTerms
        pure $ formBridi s (ts0 ++ ts1 ++ ts2)
    
    -- Multiple terms as a single node, for uses other than sentences.
    joinedTerms : WordParser 1
    joinedTerms = pictureTaggedStarGraph confluencePicture <$> map (\s => (1,0,s)) <$> catMaybes <$> map snd <$> terms
    
    tailTerms : Parser Terms
    tailTerms = (terms <|> pure []) <* opt (bySelma'o VAU)
    
    -- TODO: termsets
    terms : Parser Terms
    terms = (<?> "terms") $ some $ term
    
    term : Parser (TagType, Maybe (PictureGraph 1))
    term =
            map (\s => (PlainTag, Just s)) sumti
            <|> ((\t, s => (MiscTag, s)) <$> tag <*> maybeSumti)
            <|> ((\t, s => (faTagType t, s)) <$> bySelma'o FA <*> maybeSumti)
            <|> ((\n => (NaTag, Just n)) <$> (withFree $ bySelma'o NA <* bySelma'o KU))
        where maybeSumti = (Just <$> sumti) <|> (bySelma'o KU *> pure Nothing)
    
    -- TODO
    sumti : WordParser 1
    sumti = (<?> "sumti") $ sumti1
    
    -- TODO
    sumti1 : WordParser 1
    sumti1 = sumti2
    
    -- TODO
    sumti2 : WordParser 1
    sumti2 = sumti3
    
    -- TODO
    sumti3 : WordParser 1
    sumti3 = sumti4
    
    -- TODO
    sumti4 : WordParser 1
    sumti4 = sumti5
    
    sumti5 : WordParser 1
    sumti5 = maybeRelativeClauseJoin <$>
        (
            do q <- opt quantifier
               s <- sumti6
               pure $ maybe s (\q' => pictureTaggedStarGraph quantifierPicture [(1,0,s),(2,0,q')]) q
            <|>
            do q <- quantifier
               s <- selbri2
               pure $ pictureTaggedStarGraph quantifierPicture [(1,0,s),(2,0,q)]
        ) <*> opt relativeClauses
    
    sumti6 : WordParser 1
    sumti6 = (simpleStar 1 0 <$> (withFree $ bySelma'o LAhE <|> (bySelma'o NAhE <* bySelma'o BO)) <*> ((flip maybeRelativeClauseJoin <$> opt relativeClauses <*> lazy sumti) <* opt (bySelma'o LUhU)))
            <|> withFree (bySelma'o KOhA)
            <|> (lerfuString <* opt (bySelma'o BOI))
            <|> (simpleStar 1 0 <$> withFree (bySelma'o LA) <*> (flip maybeRelativeClauseJoin <$> opt relativeClauses <*> withFree cmeneString))
            <|> (simpleStar 1 0 <$> withFree (bySelma'o LA <|> bySelma'o LE) <*> sumtiTail <* opt (bySelma'o KU))
            <|> (simpleStar 1 0 <$> withFree (bySelma'o LI) <*> mex <* opt (bySelma'o LOhO))
            <|> (enclosePicture <$> bySelma'o LU <*> lazy text)
    
    sumtiTail : WordParser 1
    sumtiTail =
        flip relativeClauseJoin <$> relativeClauses <*> sumtiTail1
        <|> ((\pe, p, s => pictureTaggedStarGraph pe [(1,0,s),(2,0,p)]) <$> findWordPicture "pe" <*> (maybeRelativeClauseJoin <$> lazy sumti6 <*> opt relativeClauses) <|> pure id) <*> sumtiTail1
    
    sumtiTail1 : WordParser 1
    sumtiTail1 =
        ((\q, s => pictureTaggedStarGraph quantifierPicture [(1,0,s),(2,0,q)]) <$> quantifier <|> pure id) <*> (maybeRelativeClauseJoin <$> selbri2 <*> opt relativeClauses)
        <|> (\q, s => pictureTaggedStarGraph quantifierPicture [(1,0,s),(2,0,q)]) <$> quantifier <*> lazy sumti
    
    relativeClauses : WordParser 2
    relativeClauses = chainl1 (permuteRoots (\[r] => [r,r]) <$> relativeClause) $ bySelma'o ZIhE *> pure (\r0, r1 => permuteRoots (\[s,i,i',e] => [s,e]) $ addEdge 1 2 (NumberedStub 1) (NumberedStub 0) () $ graphUnion r0 r1)
    
    relativeClause : WordParser 1
    relativeClause =
        simpleStar 2 0 <$> withFree (bySelma'o GOI) <*> lazy sumti <* opt (bySelma'o GEhU)
        <|> simpleStar 2 0 <$> withFree (bySelma'o NOI) <*> lazy subsentence <* opt (bySelma'o KUhO)
    
    selbri : Parser (PictureGraph 1, Terms)
    selbri = do
        t <- opt tag
        (s,ts) <- selbri1
        pure (s, map (\t' => (MiscTag, Just t')) (toList t) ++ ts)
    
    selbri1 : Parser (PictureGraph 1, Terms)
    selbri1 = ((\s => (s,[])) <$> selbri2) <|> do
        t <- withFree $ bySelma'o NA
        (s, ts) <- lazy selbri
        pure (s, (NaTag, Just t) :: ts)
    
    -- TODO
    selbri2 : WordParser 1
    selbri2 = selbri3
    
    selbri3 : WordParser 1
    selbri3 = chainl1 selbri4 (pure $ tanruJoin)
    
    -- TODO
    selbri4 : WordParser 1
    selbri4 = selbri5
    
    -- TODO
    selbri5 : WordParser 1
    selbri5 = selbri6
    
    selbri6 : WordParser 1
    selbri6 = do
            s <- tanruUnit
            t <- opt (bySelma'o BO *> lazy selbri6)
            pure $ maybe s (flip tanruJoin s) t
        <|> do na'e <- opt $ withFree $ bySelma'o NAhE
               j <- guhek
               s0 <- lazy selbri2 --The grammar says this should be (selbri), but that seems silly (and awkward to implement).
               j' <- gik j
               s1 <- lazy selbri6
               pure $ (case na'e of
                   Nothing => id
                   Just na'e' => flip freeJoin na'e'
               ) $ pictureTaggedStarGraph j' [(1,0,s0),(2,0,s1)]
    
    -- TODO
    tanruUnit : WordParser 1
    tanruUnit = tanruUnit1
    
    -- TODO
    tanruUnit1 : WordParser 1
    tanruUnit1 = tanruUnit2
    
    tanruUnit2 : WordParser 1
    tanruUnit2 = (<?> "tanru-unit-2") $
        withFree (bySelma'o Brivla)
        <|> withFree (bySelma'o GOhA >>= (\g => maybe g (flip freeJoin g) <$> (opt $ bySelma'o RAhO)))
        <|> (bySelma'o KE *> lazy selbri3 <* opt (bySelma'o KEhE))
        <|> (simpleStar 1 0 <$> withFree (bySelma'o ME) <*> lazy sumti <* opt (bySelma'o MEhU))
        <|> (simpleStar 1 0 <$> (number <|> lerfuString) <*> withFree (bySelma'o MOI))
        <|> (simpleStar 1 0 <$> withFree (bySelma'o NUhA) <*> mexOperator)
        <|> (tanruJoin <$> withFree (bySelma'o SE) <*> lazy tanruUnit2)
        <|> fail "rule for jai not yet implemented."
        <|> (flip freeJoin <$> withFree (bySelma'o NAhE) <*> lazy tanruUnit2)
        <|> (simpleStar 1 0 <$> withFree (bySelma'o NU) <*> lazy subsentence <* bySelma'o KEI) --TODO
    
    linkArgs : WordParser 1
    linkArgs = fail "linkArgs not yet implemented."
    
    links : WordParser 1
    links = fail "links not yet implemented."
    
    quantifier : WordParser 1
    quantifier = (<?> "quantifier") $
        number <* bySelma'o BOI
        <|> bySelma'o VEI *> mex <* opt (bySelma'o VEhO)
    
    mex : WordParser 1
    mex = fail "mex not yet implemented."
    
    mexOperator : WordParser 1
    mexOperator = fail "mex-operator not yet implemented."
    
    -- Numbers are expected here in little-endian order, contrary to normal Lojban. The conversion is non-trivial, due to the presence of things other than digits in PA
    number : WordParser 1
    number = bySelma'o PA
        <|> simpleStar 1 0 <$> bySelma'o PA <*> (lazy number <|> lerfuString)
    
    lerfuString : WordParser 1
    lerfuString = lerfuWord
        <|> simpleStar 1 0 <$> lerfuWord <*> (lazy number <|> lazy lerfuString)
    
    lerfuWord : WordParser 1
    lerfuWord =
        bySelma'o BY
        <|> simpleStar 2 0 <$> bySelma'o LAU <*> lazy lerfuWord
        <|> simpleStar 2 0 <$> bySelma'o TEI <*> lazy lerfuString <* bySelma'o FOI
    
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
    
    guhek : WordParser 1
    guhek = fail "guhek not yet implemented."
    
    -- Takes the first part of the conjunction (gihek/guhek), and returns the completed picture.
    gik : PictureGraph 1 -> WordParser 1
    gik ge = fail "gik not yet implemented."
    
    -- TODO
    tag : WordParser 1
    tag = tenseModal
    
    -- TODO
    stag : WordParser 1
    stag = simpleTenseModal
    
    tenseModal : WordParser 1
    tenseModal = withFree simpleTenseModal <|>
        (\f, s => permuteRoots (\[r0,r1] => [r0]) $ addEdge 0 1 (NumberedStub 2) (NumberedStub 0) () $ enclosePicture f s) <$> withFree (bySelma'o FIhO) <*> selbri2 <* opt (bySelma'o FEhU)
    
    simpleTenseModal : WordParser 1
    simpleTenseModal = fail "simple-tense-modal not yet implemented."
    
    free : WordParser 1
    free = fail "free not yet implemented."
    
    indicators : WordParser 1
    indicators = fail "indicators not yet implemented."
    
    cmeneString : WordParser 1
    cmeneString = fail "cmeneString not yet implemented."
