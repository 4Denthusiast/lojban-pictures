module Words

import Picture

import Control.Algebra
import Data.SortedMap
import Data.Vect
import Debug.Trace

public export
data Selma'o =
    A    |
    BAI  |
    BAhE |
    BE   |
    BEI  |
    BEhO |
    BIhE |
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
    (==) BIhE BIhE = True
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
data PictureStubLabel = FreeStub | SeFreeStub | NumberedStub Nat | Inside | Around | Around' | SeltauStub | TertauStub | RerouteAny | SeRerouteAny | Reroute PictureStubLabel

total
pictureStubNumeral : PictureStubLabel -> (Nat, Nat)
pictureStubNumeral FreeStub = (0, 0)
pictureStubNumeral SeFreeStub = (0, 1)
pictureStubNumeral (NumberedStub n) = (0, 2+n)
pictureStubNumeral Inside = (1, 0)
pictureStubNumeral Around = (1, 1)
pictureStubNumeral Around' = (1, 2)
pictureStubNumeral SeltauStub = (1, 3)
pictureStubNumeral TertauStub = (1, 4)
pictureStubNumeral RerouteAny = (1, 5)
pictureStubNumeral SeRerouteAny = (1, 6)
pictureStubNumeral (Reroute s) = let (x,y) = pictureStubNumeral s in (2+x, y)

export
implementation Eq PictureStubLabel where
    (==) s s' = pictureStubNumeral s == pictureStubNumeral s'

export
implementation Ord PictureStubLabel where
    compare s s' = compare (pictureStubNumeral s) (pictureStubNumeral s')

-- The part of the word to connect to on each end, and whether it'a a fixed attachment (True) or there's a line (False).
public export
PictureEdgeLabel : Type
PictureEdgeLabel = (PictureStubLabel, Bool, PictureStubLabel)

-- Common cases, for convenience.
export
NumberedEdge : Nat -> Nat -> PictureEdgeLabel
NumberedEdge n0 n1 = (NumberedStub n0, False, NumberedStub n1)
export
FixedEdge : Nat -> Nat -> PictureEdgeLabel
FixedEdge n0 n1 = (NumberedStub n0, True, NumberedStub n1)
export
RerouteEdge : Nat -> Nat -> PictureEdgeLabel
RerouteEdge n0 n1 = (Reroute (NumberedStub n0), False, NumberedStub n1)
export
RerouteAnyEdge : PictureEdgeLabel
RerouteAnyEdge = (RerouteAny, False, SeRerouteAny)
export
FreeEdge : PictureEdgeLabel
FreeEdge = (FreeStub, False, SeFreeStub)

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
cmavrxavoStubPositions (NumberedStub       Z  ) = Just $ MkPosition [ 0  , 0] neutral
cmavrxavoStubPositions (NumberedStub    (S Z) ) = Just $ MkPosition [-0.4,-1] back
cmavrxavoStubPositions (NumberedStub (S (S Z))) = Just $ MkPosition [ 0.4,-1] back
cmavrxavoStubPositions _ = Nothing

-- ne, pe, po and po'e, not po'u, no'u or goi.
cmavrgoiStubPositions : StubPositions
cmavrgoiStubPositions (NumberedStub       Z  ) = Just $ MkPosition [0,0] neutral
cmavrgoiStubPositions (NumberedStub    (S Z) ) = Just $ MkPosition [0,-1] back
cmavrgoiStubPositions (NumberedStub (S (S Z))) = Just $ MkPosition [1,0] right
cmavrgoiStubPositions _ = Nothing

cmavrko'aStubPositions : StubPositions
cmavrko'aStubPositions (NumberedStub Z) = Just $ MkPosition [0,0] neutral
cmavrko'aStubPositions _ = Nothing

cmavrleStubPositions : StubPositions
cmavrleStubPositions (NumberedStub    Z ) = Just $ MkPosition [0,0.25] neutral
cmavrleStubPositions (NumberedStub (S Z)) = Just $ MkPosition [0,-1 ] back
cmavrleStubPositions _ = Nothing

cmavrni'oStubPositions : StubPositions
cmavrni'oStubPositions (NumberedStub       Z  ) = Just $ MkPosition [-0.5,0] left
cmavrni'oStubPositions (NumberedStub    (S Z) ) = Just $ MkPosition [ 0.5,0] right
cmavrni'oStubPositions (NumberedStub (S (S Z))) = Just $ MkPosition [ 0  ,0] back
cmavrni'oStubPositions (NumberedStub (S(S(S Z)))) = Just $ MkPosition [0,0.3] neutral
cmavrni'oStubPositions (NumberedStub (S(S(S(S Z))))) = Just $ MkPosition [0,0] back
cmavrni'oStubPositions _ = Nothing

cmavrnoiStubPositions : StubPositions
cmavrnoiStubPositions (NumberedStub       Z  ) = Just $ MkPosition [0,0.5] neutral
cmavrnoiStubPositions (NumberedStub    (S Z) ) = Just $ MkPosition [0,0] back
cmavrnoiStubPositions (NumberedStub (S (S Z))) = Just $ MkPosition [0.4,-0.4] (angle (3*pi/4))
cmavrnoiStubPositions _ = Nothing

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
stubPositionsBySelma'o FA   = emptyStubPositions
stubPositionsBySelma'o GA   = cmavrxavoStubPositions
stubPositionsBySelma'o GI   = emptyStubPositions
stubPositionsBySelma'o GOI  = cmavrgoiStubPositions
stubPositionsBySelma'o I    = cmavrni'oStubPositions
stubPositionsBySelma'o KOhA = cmavrko'aStubPositions
stubPositionsBySelma'o KU   = emptyStubPositions
stubPositionsBySelma'o LE   = cmavrleStubPositions
stubPositionsBySelma'o LI   = cmavrleStubPositions
stubPositionsBySelma'o NA   = cmavruiStubPositions
stubPositionsBySelma'o NAI  = cmavruiStubPositions
stubPositionsBySelma'o NIhO = cmavrni'oStubPositions
stubPositionsBySelma'o NOI  = cmavrnoiStubPositions
stubPositionsBySelma'o PA   = cmavrpaStubPositions
stubPositionsBySelma'o SE   = emptyStubPositions
stubPositionsBySelma'o Y    = emptyStubPositions
stubPositionsBySelma'o ZOI  = cmavrko'aStubPositions
stubPositionsBySelma'o Brivla = defaultBrivlaStubPositions
stubPositionsBySelma'o Cmevla = cmevlaStubPositions
stubPositionsBySelma'o _ = ?otherSelma'oStubPositions

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
    
    -- A
    
    a : Picture
    a =  Bezier [[0,0],[ 0.4,-0.3],[ 0.4,-0.4],[ 0.4,-1]]
     <+> Bezier [[0,0],[-0.4,-0.3],[-0.4,-0.4],[-0.4,-1]]
     <+> Bezier [[-0.4,-1],[-0.2,-0.7],[0.2,-0.7],[0.4,-1]]
    
    e : Picture
    e =  Line [-0.4,-0.3] [-0.4,-1]
     <+> Line [-0.4,-1] [0.4,-1]
     <+> Line [0.4,-1] [0.4,-0.3]
     <+> Bezier [[-0.4,-0.3],[-0.4,0.1],[0.4,0.1],[0.4,-0.3]]
    
    o : Picture
    o = a <+> Bezier [[-0.3,-1.1],[-0.1,-0.8],[0.1,-0.8],[0.3,-1.1]]
    
    u : Picture
    u =  Line [-0.4,-0.3] [-0.4,-1]
     <+> Line [-0.1,-1] [0.4,-1]
     <+> Line [0.4,-1] [0.4,-0.6]
     <+> Bezier [[-0.4,-0.3],[-0.4,0.1],[0.4,0.1],[0.4,-0.3]]
    
    -- GOI
    
    pe : Picture
    pe = Line [0,0] [1,0]
     <+> Line [0,0] [0,-1]
     <+> Bezier [[1,0],[1,-0.5],[0.7,-0.85],[0.2,-0.9]]
     <+> Line [0.95,-0.3] [1.6,-0.3]
    
    -- KOhA
    
    KOhAleft : Picture
    KOhAleft = Bezier [[0,0],[0,-1.5],[-1.5,0],[0,0]]
    
    KOhA3_1st : Picture
    KOhA3_1st = Line [-0.3,0] [-0.3,0.5]
    
    KOhA3_2nd : Picture
    KOhA3_2nd = Line [-0.5625,-0.5625] [-0.9,-0.9]
    
    KOhA3_3rd : Picture
    KOhA3_3rd = Line [0,-0.3] [0.5,-0.3]
    
    -- LE
    
    lo : Picture
    lo = Beziers [(Corner,[0,-1]),(Control,[-1,0]),(Control,[0,1]),(Control,[1,0])]
    
    le : Picture
    le = lo <+> Dot [0,-0.2]
    
    -- NIhO
    
    ni'o : Picture
    ni'o = Bezier [[0,0],[0,-0.5],[-0.7,0],[-0.7,-0.5]] <+>
           Bezier [[0,0],[0,-0.5],[ 0.7,0],[ 0.7,-0.5]]
    
    ni'oBase : Picture
    ni'oBase = Line [-0.5,0] [0.5,0] <+> ni'o
    
    ni'oMod : Picture
    ni'oMod = Line [0,0] [0,0.3] <+> ni'o
    
    -- NOI
    
    poi : Picture
    poi = Line [0,0] [0,0.5]
      <+> Line [0,0] [0.4,-0.4]
      <+> Bezier [[0,0.5],[0.4,0.1],[0.4,0.1],[0.4,-0.4]]
    
    -- PA
    
    no : Picture
    no = Line [-0.5,0] [0.5,0]
     <+> Line [0,0] [0,-0.6]
    
    re : Picture
    re = Line [-0.5,0] [0.5,0]
     <+> Bezier [[0,0],[0,-0.6],[0,-0.6],[0.2,-0.6]]
    
    vo : Picture
    vo = Line [-0.5,0] [0.5,0]
     <+> Bezier [[0,0],[0,-0.6],[0,-0.6],[-0.2,-0.6]]
    
    xa : Picture
    xa = no <+> Line [-0.2,-0.6] [0.2,-0.6]
    
    PA_0001b : Picture
    PA_0001b = Line [0,-0.3] [0.2,-0.3]
    
    PA_1000b : Picture
    PA_1000b = Line [0,-0.3] [-0.2,-0.3]
    
    -- broda
    
    brodV : Picture
    brodV = Bezier [[0,1],[4/3,1],[4/3,-1],[0,-1]]
        <+> Bezier [[-0.5,sqrt(3/4)],[-1.3,0.3],[-1,-1],[0,-1]]
        <+> Line [0,1] [0,-0.3]

wordRecords : SortedMap String WordRecord
wordRecords = foldr (\w, t => insert (string w) w t) empty $ partialId [
        makeWordRecord' A    "a" $ a,
        makeWordRecord' A    "e" $ e,
        makeWordRecord  A    "o", -- The default of this includes a negation bubble.
        makeWordRecord' A    "o'" $ o,
        makeWordRecord' A    "u" $ u,
        makeWordRecord  BU   "bu",
        makeWordRecord  FA   "fa",
        makeWordRecord  FA   "fe",
        makeWordRecord  FA   "fi",
        makeWordRecord  FA   "fo",
        makeWordRecord  FA   "fu",
        makeWordRecord  GA   "ga",
        makeWordRecord  GA   "ge",
        makeWordRecord  GA   "go",
        makeWordRecord  GA   "gu",
        makeWordRecord  GI   "gi",
        makeWordRecord  GIhA "gi'a",
        makeWordRecord  GIhA "gi'e",
        makeWordRecord  GIhA "gi'o",
        makeWordRecord  GIhA "gi'u",
        makeWordRecord' GOI  "pe" $ pe,
        makeWordRecord' I    "i" $ Line [-0.5,0] [0.5,0],
        makeWordRecord  KU   "ku",
        makeWordRecord' KOhA "mi" $ KOhAleft <+> KOhA3_1st,
        makeWordRecord' KOhA "do" $ KOhAleft <+> KOhA3_2nd,
        makeWordRecord' KOhA "mi'o" $ KOhAleft <+> KOhA3_1st <+> KOhA3_2nd,
        makeWordRecord' KOhA "ma'a" $ KOhAleft <+> KOhA3_1st <+> KOhA3_2nd <+> KOhA3_3rd,
        makeWordRecord  KUhO "ku'o",
        makeWordRecord' LE   "le" $ le,
        makeWordRecord' LE   "lo" $ lo,
        makeWordRecord' LI   "li" $
            Line [-0.5,-1] [0.5,-1] <+> Beziers [
                (Smooth,[0.3,-0.8]),
                (Smooth,[-0.3,-0.8]),(Control,[-0.5,-0.8]),(Control,[-0.7,-0.6]),
                (Smooth,[-0.7,-0.4]),(Control,[-0.7,0.8]),(Control,[0.7,0.8]),
                (Smooth,[0.7,-0.4]),(Control,[0.7,-0.6]),(Control,[0.5,-0.8])
            ],
        makeWordRecord  NAI  "nai",
        makeWordRecord  NA   "na",
        MkWordRecord NIhO "ni'o" $ (\(MkWordContext _ _ ss) => MkWordPicture "ni'o" (if elem (NumberedStub 3) ss then ni'oMod else ni'oBase) cmavrni'oStubPositions),
        makeWordRecord  NIhO "no'i",
        makeWordRecord' NOI  "poi" $ poi,
        makeWordRecord' PA   "no"  $ no,
        makeWordRecord' PA   "pa"  $ no <+> PA_0001b,
        makeWordRecord' PA   "re"  $ re,
        makeWordRecord' PA   "ci"  $ re <+> PA_0001b,
        makeWordRecord' PA   "vo"  $ vo,
        makeWordRecord' PA   "mu"  $ vo <+> PA_0001b,
        makeWordRecord' PA   "xa"  $ xa,
        makeWordRecord' PA   "ze"  $ xa <+> PA_0001b,
        makeWordRecord' PA   "bi"  $ no <+> PA_1000b,
        makeWordRecord' PA   "so"  $ no <+> PA_1000b <+> PA_0001b,
        makeWordRecord' PA   "dau" $ re <+> PA_1000b,
        makeWordRecord' PA   "fei" $ re <+> PA_1000b <+> PA_0001b,
        makeWordRecord' PA   "gai" $ vo <+> PA_1000b,
        makeWordRecord' PA   "jau" $ vo <+> PA_1000b <+> PA_0001b,
        makeWordRecord' PA   "rei" $ xa <+> PA_1000b,
        makeWordRecord' PA   "vai" $ xa <+> PA_1000b <+> PA_0001b,
        makeWordRecord  SE   "se",
        makeWordRecord  SE   "te",
        makeWordRecord  SE   "ve",
        makeWordRecord  SE   "xe",
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
    show (Reroute s) = "rr:"++show s
    show RerouteAny = "rr_"
    show SeRerouteAny = "RR_"

export
Show WordPicture where
    show w = string $ w (emptyContext [])
