module Words

import Picture

import Control.Algebra
import Data.SortedMap
import Data.Vect

public export
data Selma'o =
    A    |
    BAI  |
    BAhE |
    BE   |
    BEI  |
    BEhO |
    BIhI |
    BO   |
    BOI  |
    BU   |
    BY   |
    CAI  |
    CAhA |
    CEI  |
    CEhE |
    CO   |
    COI  |
    CU   |
    CUhE |
    DAhO |
    DOI  |
    DOhU |
    FA   |
    FAhA |
    FAhO |
    FEhE |
    FEhU |
    FIhO |
    FOI  |
    FUhA |
    FUhE |
    FUhO |
    GA   |
    GAhO |
    GEhU |
    GI   |
    GIhA |
    GOI  |
    GOhA |
    GUhA |
    I    | -- [prev I, next I, sentence]
    JA   | -- [head, left opt, right opt, simultaneous tag e.g. .ijoibaibo]
    JAI  |
    JOI  | -- [head, left opt, right opt, simultaneous tag e.g. .ijoibaibo]
    JOhE |
    JOhI |
    KE   |
    KEI  |
    KEhE |
    KI   |
    KOhA |
    KU   |
    KUhE |
    KUhO |
    LA   |
    LAU  |
    LAhE |
    LE   |
    LEhU |
    LI   |
    LIhU |
    LOhO |
    LOhU |
    LU   |
    LUhU |
    MAI  |
    MAhO |
    ME   |
    MEhU |
    MOI  |
    MOhE |
    MOhI |
    NA   |
    NAI  |
    NAhE |
    NAhU |
    NIhE |
    NIhO | -- [prev NIhO, next NIhO, paragraph, prev NIhO repetition (e.g. ni'oni'o), next NIhO repetition]
    NOI  |
    NU   |
    NUhA |
    NUhI |
    NUhU |
    PA   |
    PEhE |
    PEhO |
    PU   |
    RAhO |
    ROI  |
    SA   |
    SE   |
    SEI  |
    SEhU |
    SI   |
    SOI  |
    SU   |
    TAhE |
    TEI  |
    TEhU |
    TO   |
    TOI  |
    TUhE |
    TUhU |
    UI   |
    VA   |
    VAU  |
    VEI  |
    VEhA |
    VEhO |
    VIhA |
    VUhO |
    VUhU |
    XI   |
    Y    |
    ZAhO |
    ZEI  |
    ZEhA |
    ZI   |
    ZIhE |
    ZO   |
    ZOI  |
    ZOhU | -- [outer sentence, inner sentence, prenex terms]
    Brivla |
    Cmevla -- [head, prev name in string, next name in string]

public export
implementation Eq Selma'o where
    (==) A    A    = True
    (==) BAI  BAI  = True
    (==) BAhE BAhE = True
    (==) BE   BE   = True
    (==) BEI  BEI  = True
    (==) BEhO BEhO = True
    (==) BIhI BIhI = True
    (==) BO   BO   = True
    (==) BOI  BOI  = True
    (==) BU   BU   = True
    (==) BY   BY   = True
    (==) CAI  CAI  = True
    (==) CAhA CAhA = True
    (==) CEI  CEI  = True
    (==) CEhE CEhE = True
    (==) CO   CO   = True
    (==) COI  COI  = True
    (==) CU   CU   = True
    (==) CUhE CUhE = True
    (==) DAhO DAhO = True
    (==) DOI  DOI  = True
    (==) DOhU DOhU = True
    (==) FA   FA   = True
    (==) FAhA FAhA = True
    (==) FAhO FAhO = True
    (==) FEhE FEhE = True
    (==) FEhU FEhU = True
    (==) FIhO FIhO = True
    (==) FOI  FOI  = True
    (==) FUhA FUhA = True
    (==) FUhE FUhE = True
    (==) FUhO FUhO = True
    (==) GA   GA   = True
    (==) GAhO GAhO = True
    (==) GEhU GEhU = True
    (==) GI   GI   = True
    (==) GIhA GIhA = True
    (==) GOI  GOI  = True
    (==) GOhA GOhA = True
    (==) GUhA GUhA = True
    (==) I    I    = True
    (==) JA   JA   = True
    (==) JAI  JAI  = True
    (==) JOI  JOI  = True
    (==) JOhE JOhE = True
    (==) JOhI JOhI = True
    (==) KE   KE   = True
    (==) KEI  KEI  = True
    (==) KEhE KEhE = True
    (==) KI   KI   = True
    (==) KOhA KOhA = True
    (==) KU   KU   = True
    (==) KUhE KUhE = True
    (==) KUhO KUhO = True
    (==) LA   LA   = True
    (==) LAU  LAU  = True
    (==) LAhE LAhE = True
    (==) LE   LE   = True
    (==) LEhU LEhU = True
    (==) LI   LI   = True
    (==) LIhU LIhU = True
    (==) LOhO LOhO = True
    (==) LOhU LOhU = True
    (==) LU   LU   = True
    (==) LUhU LUhU = True
    (==) MAI  MAI  = True
    (==) MAhO MAhO = True
    (==) ME   ME   = True
    (==) MEhU MEhU = True
    (==) MOI  MOI  = True
    (==) MOhE MOhE = True
    (==) MOhI MOhI = True
    (==) NA   NA   = True
    (==) NAI  NAI  = True
    (==) NAhE NAhE = True
    (==) NAhU NAhU = True
    (==) NIhE NIhE = True
    (==) NIhO NIhO = True
    (==) NOI  NOI  = True
    (==) NU   NU   = True
    (==) NUhA NUhA = True
    (==) NUhI NUhI = True
    (==) NUhU NUhU = True
    (==) PA   PA   = True
    (==) PEhE PEhE = True
    (==) PEhO PEhO = True
    (==) PU   PU   = True
    (==) RAhO RAhO = True
    (==) ROI  ROI  = True
    (==) SA   SA   = True
    (==) SE   SE   = True
    (==) SEI  SEI  = True
    (==) SEhU SEhU = True
    (==) SI   SI   = True
    (==) SOI  SOI  = True
    (==) SU   SU   = True
    (==) TAhE TAhE = True
    (==) TEI  TEI  = True
    (==) TEhU TEhU = True
    (==) TO   TO   = True
    (==) TOI  TOI  = True
    (==) TUhE TUhE = True
    (==) TUhU TUhU = True
    (==) UI   UI   = True
    (==) VA   VA   = True
    (==) VAU  VAU  = True
    (==) VEI  VEI  = True
    (==) VEhA VEhA = True
    (==) VEhO VEhO = True
    (==) VIhA VIhA = True
    (==) VUhO VUhO = True
    (==) VUhU VUhU = True
    (==) XI   XI   = True
    (==) Y    Y    = True
    (==) ZAhO ZAhO = True
    (==) ZEI  ZEI  = True
    (==) ZEhA ZEhA = True
    (==) ZI   ZI   = True
    (==) ZIhE ZIhE = True
    (==) ZO   ZO   = True
    (==) ZOI  ZOI  = True
    (==) ZOhU ZOhU = True
    (==) Brivla Brivla = True
    (==) Cmevla Cmevla = True
    (==) _ _ = False

public export
data PictureStubLabel = FreeStub | SeFreeStub | NumberedStub Nat | Inside | Around | Around' | SeltauStub | TertauStub

pictureStubNumeral : PictureStubLabel -> (Bool, Nat)
pictureStubNumeral FreeStub = (False, 0)
pictureStubNumeral SeFreeStub = (False, 1)
pictureStubNumeral (NumberedStub n) = (False, 2+n)
pictureStubNumeral Inside = (True, 0)
pictureStubNumeral Around = (True, 1)
pictureStubNumeral Around' = (True, 2)
pictureStubNumeral SeltauStub = (True, 3)
pictureStubNumeral TertauStub = (True, 4)

export
implementation Eq PictureStubLabel where
    (==) s s' = pictureStubNumeral s == pictureStubNumeral s'

export
implementation Ord PictureStubLabel where
    compare s s' = compare (pictureStubNumeral s) (pictureStubNumeral s')

public export
PictureEdgeLabel : Type
PictureEdgeLabel = (PictureStubLabel, PictureStubLabel)

public export
StubPositions : Type
StubPositions = PictureStubLabel -> Maybe Position

public export
record WordPicture' where
    constructor MkWordPicture
    string : String
    picture : Picture
    stubs : StubPositions

public export
record WordContext where
    constructor MkWordContext
    aroundShape : ConvexHull
    aroundShape' : ConvexHull
    stubs : List PictureStubLabel

public export
emptyContext : List PictureStubLabel -> WordContext
emptyContext = MkWordContext emptyHull emptyHull

public export
WordPicture : Type
WordPicture = WordContext -> WordPicture'

public export
record WordRecord where
    constructor MkWordRecord
    selma'o : Selma'o
    string : String
    picture : WordPicture

public export
data Word = MkWord WordRecord | MagicWordBU Word | MagicWordZO Word | MagicWordZOI WordRecord String | MagicWordZEI Word Word | MagicWordLOhU (List Word)

export
wordSelma'o : Word -> Selma'o
wordSelma'o (MkWord wr) = selma'o wr
wordSelma'o (MagicWordZEI _ _) = Brivla
wordSelma'o (MagicWordBU _) = BY
wordSelma'o _ = KOhA --The other magic word things are all sumti

-- terminators, Y
emptyStubPositions : StubPositions
emptyStubPositions _ = Nothing

cmavrxavoStubPositions : StubPositions
cmavrxavoStubPositions (NumberedStub       Z  ) = Just $ MkPosition [ 0  , 0.5] neutral
cmavrxavoStubPositions (NumberedStub    (S Z) ) = Just $ MkPosition [ 0.5,-0.5] back
cmavrxavoStubPositions (NumberedStub (S (S Z))) = Just $ MkPosition [-0.5,-0.5] back
cmavrxavoStubPositions _ = Nothing

cmavrxivoStubPositions : StubPositions
cmavrxivoStubPositions (NumberedStub       Z  ) = Just $ MkPosition [-0.5,0] left
cmavrxivoStubPositions (NumberedStub    (S Z) ) = Just $ MkPosition [ 0.5,0] right
cmavrxivoStubPositions (NumberedStub (S (S Z))) = Just $ MkPosition [ 0  ,0] back
cmavrxivoStubPositions _ = Nothing

cmavrko'aStubPositions : StubPositions
cmavrko'aStubPositions (NumberedStub Z) = Just $ MkPosition [0,0] neutral
cmavrko'aStubPositions _ = Nothing

cmavrleStubPositions : StubPositions
cmavrleStubPositions (NumberedStub    Z ) = Just $ MkPosition [0,0.5] neutral
cmavrleStubPositions (NumberedStub (S Z)) = Just $ MkPosition [0,-1 ] back
cmavrleStubPositions _ = Nothing

cmavrpaStubPositions : StubPositions
cmavrpaStubPositions (NumberedStub    Z ) = Just $ MkPosition [ 0.5,0] right
cmavrpaStubPositions (NumberedStub (S Z)) = Just $ MkPosition [-0.5,0] left
cmavrpaStubPositions _ = Nothing

cmavruiStubPositions : StubPositions
cmavruiStubPositions SeFreeStub = Just $ MkPosition [0,0] back
cmavruiStubPositions _ = Nothing

brodaStubPositions : StubPositions
brodaStubPositions (NumberedStub n) = let a = angle (cast n * pi * (1 - sqrt 5)) in Just $ rotatePosition a $ MkPosition [0,1.3] neutral
brodaStubPositions _ = Nothing

defaultBrivlaStubPositions : StubPositions
defaultBrivlaStubPositions (NumberedStub n) = let a = angle (cast n * pi * 2/5) in Just $ rotatePosition a $ MkPosition [0,1] neutral
defaultBrivlaStubPositions _ = Nothing

cmevlaStubPositions : StubPositions
cmevlaStubPositions (NumberedStub       Z  ) = Just $ MkPosition [0, 1] neutral
cmevlaStubPositions (NumberedStub    (S Z) ) = Just $ MkPosition [0,-1] back
cmevlaStubPositions (NumberedStub (S (S Z))) = Just $ MkPosition [0, 1] neutral
cmevlaStubPositions _ = Nothing

stubPositionsBySelma'o : Selma'o -> StubPositions
stubPositionsBySelma'o A    = cmavrxavoStubPositions
stubPositionsBySelma'o BU   = cmavrpaStubPositions
stubPositionsBySelma'o I    = cmavrxivoStubPositions
stubPositionsBySelma'o KOhA = cmavrko'aStubPositions
stubPositionsBySelma'o KU   = emptyStubPositions
stubPositionsBySelma'o LE   = cmavrleStubPositions
stubPositionsBySelma'o NA   = cmavruiStubPositions
stubPositionsBySelma'o NAI  = cmavruiStubPositions
stubPositionsBySelma'o NIhO = cmavrxivoStubPositions
stubPositionsBySelma'o Y    = emptyStubPositions
stubPositionsBySelma'o ZOI  = cmavrko'aStubPositions
stubPositionsBySelma'o Brivla = defaultBrivlaStubPositions
stubPositionsBySelma'o Cmevla = cmevlaStubPositions

export
makeWordRecord : Selma'o -> String -> WordRecord
makeWordRecord sm s = MkWordRecord sm s $ const $ MkWordPicture s (Text s) (stubPositionsBySelma'o sm)

export
makeWordRecord' : Selma'o -> String -> Picture -> WordRecord
makeWordRecord' sm s p = MkWordRecord sm s $ const $ MkWordPicture s p (stubPositionsBySelma'o sm)

-- force the compiler to not expand an expression
partial
partialId : List a -> List a
partialId (x::xs) = (x::xs)

namespace pictureLib
    KOhAleft : Picture
    KOhAleft = Bezier [[0,0],[0,-1.5],[-1.5,0],[0,0]]
    
    KOhA3_1st : Picture
    KOhA3_1st = Line [-0.3,0] [-0.3,0.5]
    
    KOhA3_2nd : Picture
    KOhA3_2nd = Line [-0.5625,-0.5625] [-0.9,-0.9]
    
    KOhA3_3rd : Picture
    KOhA3_3rd = Line [0,-0.3] [0.5,-0.3]
    
    lo : Picture
    lo = Bezier [[0,-1],[-0.7,-0.3],[-0.7,0.5],[0,0.5]]
     <+> Bezier [[0,-1],[ 0.7,-0.3],[ 0.7,0.5],[0,0.5]] --Bezier [[0,-1],[-1,1],[1,1],[0,-1]]
    
    le : Picture
    le = lo <+> Dot [0,0]
    
    brodV : Picture
    brodV = Bezier [[0,1],[4/3,1],[4/3,-1],[0,-1]]
        <+> Bezier [[-0.5,sqrt(3/4)],[-1.3,0.3],[-1,-1],[0,-1]]
        <+> Line [0,1] [0,-0.3]

wordRecords : SortedMap String WordRecord
wordRecords = foldr (\w, t => insert (string w) w t) empty $ partialId [
        makeWordRecord  A    "a",
        makeWordRecord  BU   "bu",
        makeWordRecord  FA   "fa",
        makeWordRecord  FA   "fe",
        makeWordRecord  FA   "fi",
        makeWordRecord  FA   "fo",
        makeWordRecord  FA   "fu",
        makeWordRecord' I    "i" $ Line [-0.5,0] [0.5,0],
        makeWordRecord  KU   "ku",
        makeWordRecord' LE   "le" $ le,
        makeWordRecord' LE   "lo" $ lo,
        makeWordRecord' KOhA "mi" $ KOhAleft <+> KOhA3_1st,
        makeWordRecord' KOhA "do" $ KOhAleft <+> KOhA3_2nd,
        makeWordRecord' KOhA "mi'o" $ KOhAleft <+> KOhA3_1st <+> KOhA3_2nd,
        makeWordRecord' KOhA "ma'a" $ KOhAleft <+> KOhA3_1st <+> KOhA3_2nd <+> KOhA3_3rd,
        makeWordRecord  NAI  "nai",
        makeWordRecord  NA   "na",
        makeWordRecord' NIhO "ni'o" $
            Line [-0.5,0] [0.5,0] <+>
            Bezier [[0,0],[0,-0.5],[-0.7,0],[-0.7,-0.5]] <+>
            Bezier [[0,0],[0,-0.5],[ 0.7,0],[ 0.7,-0.5]],
        makeWordRecord  NIhO "no'i",
        makeWordRecord  Y    "y",
        makeWordRecord  ZOI  "zoi",
        MkWordRecord Brivla "broda" $ const $ MkWordPicture "broda" brodV brodaStubPositions
    ]

tryMaybe : Maybe a -> Lazy (Maybe a) -> Maybe a
tryMaybe Nothing x = x
tryMaybe x _ = x

-- Get a word record in the case that it's a known word.
export
findWordRecord : String -> Maybe WordRecord
findWordRecord s = lookup s wordRecords

export
Show PictureStubLabel where
    show FreeStub = "F"
    show SeFreeStub = "f"
    show (NumberedStub n) = show n
    show Inside = "i"
    show Around = "I"
    show Around' = "I'"
    show SeltauStub = "st"
    show TertauStub = "tt"

export
Show WordPicture where
    show w = string $ w (emptyContext [])
