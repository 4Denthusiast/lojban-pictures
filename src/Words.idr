module Words

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
WordPicture : Type
WordPicture = String

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

data Trie l t = Branch (Maybe t) (List (l,Trie l t))

emptyTrie : Trie l t
emptyTrie = Branch Nothing []

singletonTrie : List l -> t -> Trie l t
singletonTrie [] x = Branch (Just x) []
singletonTrie (l::ls) x = Branch Nothing [(l,singletonTrie ls x)]

trieAppend : Eq l => List l -> t -> Trie l t -> Trie l t
trieAppend [] x (Branch _ bs) = Branch (Just x) bs
trieAppend (c::cs) x (Branch y bs) = Branch y (trieAppend' c cs x bs)
    where trieAppend' : l -> List l -> t -> List (l, Trie l t) -> List (l, Trie l t)
          trieAppend' c cs x [] = [(c, singletonTrie cs x)]
          trieAppend' c cs x ((c',b)::bs) = if c' == c
              then (c,trieAppend cs x b) :: bs
              else (c',b) :: trieAppend' c cs x bs

trieFind : Eq l => List l -> Trie l t -> Maybe t
trieFind [] (Branch x _) = x
trieFind (l::ls) (Branch _ bs) = lookup l bs >>= trieFind ls

wordRecords : Trie Char WordRecord
wordRecords = foldr (\w, t => trieAppend (unpack $ string w) w t) emptyTrie [
        MkWordRecord A "a" "a",
        MkWordRecord BU "bu" "bu",
        MkWordRecord I "i" "i",
        MkWordRecord KU "ku" "ku",
        MkWordRecord LE "le" "le",
        MkWordRecord LE "lo" "lo",
        MkWordRecord KOhA "mi" "mi",
        MkWordRecord NAI "nai" "nai",
        MkWordRecord NA "na" "na",
        MkWordRecord NIhO "ni'o" "ni'o",
        MkWordRecord NIhO "no'i" "no'i",
        MkWordRecord Y "y" "y",
        MkWordRecord ZOI "zoi" "zoi",
        MkWordRecord Brivla "broda" "broda"
    ]

tryMaybe : Maybe a -> Lazy (Maybe a) -> Maybe a
tryMaybe Nothing x = x
tryMaybe x _ = x

-- Get a word record in the case that it's a known word.
export
findWordRecord : String -> Maybe WordRecord
findWordRecord s = trieFind (unpack s) wordRecords
