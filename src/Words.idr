module Words

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
    Cmevla

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

implementation Eq PictureStubLabel where
    (==) s s' = pictureStubNumeral s == pictureStubNumeral s'

implementation Ord PictureStubLabel where
    compare s s' = compare (pictureStubNumeral s) (pictureStubNumeral s')

public export
data StubPos = MkStubPos (Vect 2 Double) (Vect 2 Double)

public export
StubPositions : Type
StubPositions = List PictureStubLabel -> PictureStubLabel -> Maybe StubPos

public export
record WordPicture where
    constructor MkWordPicture
    string : String
    stubs : StubPositions

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
emptyStubPositions _ _ = Nothing

cmavrxavoStubPositions : StubPositions
cmavrxavoStubPositions _ (NumberedStub       Z  ) = Just $ MkStubPos [ 0  , 0.5] [0, 1]
cmavrxavoStubPositions _ (NumberedStub    (S Z) ) = Just $ MkStubPos [ 0.5,-0.5] [0,-1]
cmavrxavoStubPositions _ (NumberedStub (S (S Z))) = Just $ MkStubPos [-0.5,-0.5] [0,-1]
cmavrxavoStubPositions _ _ = Nothing

cmavrxivoStubPositions : StubPositions
cmavrxivoStubPositions _ (NumberedStub       Z  ) = Just $ MkStubPos [0,0] [-1,0]
cmavrxivoStubPositions _ (NumberedStub    (S Z) ) = Just $ MkStubPos [0,0] [ 1,0]
cmavrxivoStubPositions _ (NumberedStub (S (S Z))) = Just $ MkStubPos [0,0] [0,-1]
cmavrxivoStubPositions _ _ = Nothing

cmavrko'aStubPositions : StubPositions
cmavrko'aStubPositions _ (NumberedStub Z) = Just $ MkStubPos [0,0] [0,1]
cmavrko'aStubPositions _ _ = Nothing

cmavrleStubPositions : StubPositions
cmavrleStubPositions _ (NumberedStub    Z ) = Just $ MkStubPos [0,0.5] [0, 1]
cmavrleStubPositions _ (NumberedStub (S Z)) = Just $ MkStubPos [0,-1 ] [0,-1]
cmavrleStubPositions _ _ = Nothing

cmavrpaStubPositions : StubPositions
cmavrpaStubPositions _ (NumberedStub    Z ) = Just $ MkStubPos [ 0.5,0] [ 1,0]
cmavrpaStubPositions _ (NumberedStub (S Z)) = Just $ MkStubPos [-0.5,0] [-1,0]
cmavrpaStubPositions _ _ = Nothing

cmavruiStubPositions : StubPositions
cmavruiStubPositions _ SeFreeStub = Just $ MkStubPos [0,0] [0,-1]
cmavruiStubPositions _ _ = Nothing

cossin : Double -> Vect 2 Double
cossin x = [cos x, sin x]

brodaStubPositions : StubPositions
brodaStubPositions _ (NumberedStub n) = let d = cossin (cast n * pi * (sqrt 5 - 1)) in Just $ MkStubPos d d
brodaStubPositions _ _ = Nothing

defaultBrivlaStubPositions : StubPositions
defaultBrivlaStubPositions _ (NumberedStub n) = let d = cossin (cast n * pi * 2/5) in Just $ MkStubPos d d
defaultBrivlaStubPositions _ _ = Nothing

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
stubPositionsBySelma'o Cmevla = cmavrpaStubPositions

export
makeWordRecord : Selma'o -> String -> WordRecord
makeWordRecord sm s = MkWordRecord sm s $ MkWordPicture s (stubPositionsBySelma'o sm)

-- force the compiler to not expand an expression
partial
partialId : List a -> List a
partialId (x::xs) = (x::xs)

wordRecords : SortedMap String WordRecord
wordRecords = foldr (\w, t => insert (string w) w t) empty $ partialId [
        makeWordRecord A    "a",
        makeWordRecord BU   "bu",
        makeWordRecord I    "i",
        makeWordRecord KU   "ku",
        makeWordRecord LE   "le",
        makeWordRecord LE   "lo",
        makeWordRecord KOhA "mi",
        makeWordRecord NAI  "nai",
        makeWordRecord NA   "na",
        makeWordRecord NIhO "ni'o",
        makeWordRecord NIhO "no'i",
        makeWordRecord Y    "y",
        makeWordRecord ZOI  "zoi",
        MkWordRecord Brivla "broda" $ MkWordPicture "broda" brodaStubPositions
    ]

tryMaybe : Maybe a -> Lazy (Maybe a) -> Maybe a
tryMaybe Nothing x = x
tryMaybe x _ = x

-- Get a word record in the case that it's a known word.
export
findWordRecord : String -> Maybe WordRecord
findWordRecord s = lookup s wordRecords
