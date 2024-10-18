module MapFrom

import Data.So

import Set
import VerifiedOrd

%default total

infix 2 <=>
data (<=>) : Type -> Type -> Type where
    MkEquiv : (a -> b) -> (b -> a) -> (a <=> b)

infix 2 <==>
(<==>) : (t -> Type) -> (t -> Type) -> Type
(<==>) {t} a b = (x:t) -> (a x <=> b x)

equivRefl : (a <==> a)
equivRefl x = MkEquiv id id

equivCov : (a <=> b) -> a -> b
equivCov (MkEquiv cov _) = cov

equivContra : (a <=> b) -> b -> a
equivContra (MkEquiv _ contra) = contra

equivSymm : (a <==> b) -> (b <==> a)
equivSymm e x = MkEquiv (equivContra (e x)) (equivCov (e x))

equivConcat : (a <==> b) -> (b <==> c) -> (a <==> c)
equivConcat ab bc x = MkEquiv (equivCov (bc x) . equivCov (ab x)) (equivContra (ab x) . equivContra (bc x))


data Capped x = Low | Real x | High

Eq x => Eq (Capped x) where
    (==) Low Low = True
    (==) (Real x) (Real y) = x == y
    (==) High High = True
    (==) _ _ = False

Ord x => Ord (Capped x) where
    compare Low Low = EQ
    compare Low _ = LT
    compare (Real _) Low = GT
    compare (Real x) (Real y) = compare x y
    compare (Real _) High = LT
    compare High High = EQ
    compare High _ = GT
    
    --These definitions make the proofs easier than using the defaults.
    (<) x y = compare x y == LT
    (>) x y = compare x y == GT
    (<=) x y = compare x y /= GT
    (>=) x y = compare x y /= LT

VerifiedOrd x => VerifiedOrd (Capped x) where
    reflexive Low = Oh
    reflexive (Real x') = reflexive x'
    reflexive (High) = Oh
    eqTransitive Low Low Low Oh Oh = Oh
    eqTransitive (Real x') (Real y') (Real z') xy yz = eqTransitive x' y' z' xy yz
    eqTransitive High High High Oh Oh = Oh
    neqConsistent x y = Refl
    exact Low Low Oh = Refl
    exact (Real x') (Real y') xy = rewrite__impl (\x => Real x = Real y') (exact x' y' xy) $ Refl
    exact High High Oh = Refl
    
    ltConsistent x y = Refl
    gtConsistent x y = Refl
    lteConsistent x y = Refl
    gteConsistent x y = Refl
    eqConsistent Low Low = Refl
    eqConsistent Low (Real _) = Refl
    eqConsistent Low High = Refl
    eqConsistent (Real x') Low = Refl
    eqConsistent (Real x') (Real y') = eqConsistent x' y'
    eqConsistent (Real x') High = Refl
    eqConsistent High High = Refl
    eqConsistent High (Real _) = Refl
    eqConsistent High Low = Refl
    reversable = ?cappedReversable
    ltTransitive = ?cappedTransitive


data Tree : (k:Type) -> .(p:k -> Type) -> Nat -> VerifiedOrd k -> (k -> Type) -> Capped k -> Capped k -> Type where
    Leaf : {o:VerifiedOrd k} -> (x:k) -> v x -> So (Real x > l) -> Tree k (\x' => x' = x) 0 o v l (Real x)
    TEnd : Tree k (\_ => Void) 0 o v l High
    TNil : .(p <==> (\_ => Void)) -> Tree k p (S n) o v x x
    TCons : Tree k p0 (S n) o v l x0 -> Tree k p1 n o v x0 x1 -> .(p <==> (\x => if Real x > x0 then p1 x else p0 x)) -> Tree k p (S n) o v l x1

tNil : Tree k (\_ => Void) (S n) o v x x
tNil = TNil (equivRefl {a=(\_ => Void)})

treeOrdered : Tree k p n o v l r -> So (r >= l)
treeOrdered {l} (Leaf x _ gt) = gtImpliesGte (Real x) l gt
treeOrdered {l=Low} TEnd = Oh
treeOrdered {l=Real _} TEnd = Oh
treeOrdered {l=High} TEnd = Oh
treeOrdered {l} (TNil _) = eqImpliesGte l l $ reflexive l
treeOrdered {l} {r} (TCons {x0} tl t _) = gteTransitive r x0 l (treeOrdered t) (treeOrdered tl)

rephraseSet : Tree k p (S n) o v l r -> (p <==> p') -> Tree k p' (S n) o v l r
rephraseSet (TNil       pf) pf' = TNil       $ equivConcat (equivSymm pf') pf
rephraseSet (TCons tl t pf) pf' = TCons tl t $ equivConcat (equivSymm pf') pf

unCapGt : VerifiedOrd t => {a:t} -> {b:t} -> So (Real a > Real b) -> So (a > b)
unCapGt {a} {b} o with (a > b) proof ab
    unCapGt {a} {b} o | True = Oh
    unCapGt {a} {b} o | False = absurd $ replace (sym ab) $ replace (sym $ gtConsistent a b) o

unCapGte : VerifiedOrd t => {a:t} -> {b:t} -> So (Real a >= Real b) -> So (a >= b)
unCapGte {a} {b} o with (a >= b) proof ab
    unCapGte {a} {b} o | True = Oh
    unCapGte {a} {b} o | False = absurd $ replace (sym ab) $ replace (sym $ gteConsistent a b) o

unCapEq : Real a = Real b -> a = b
unCapEq Refl = Refl

rightBounded : Tree k p n o v l r -> p x -> So (r >= Real x)
rightBounded {x} (Leaf _ _ _) Refl = eqImpliesGte (Real x) (Real x) $ reflexive (Real x)
rightBounded TEnd i = Oh
rightBounded {x} (TNil pf) i = void $ equivCov (pf x) i
rightBounded {x} {l} {r} (TCons {x0} {p0} {p1} tl t pf) i with (Real x > x0) proof xgx0
    rightBounded {x} {l} {r} (TCons {x0} {p0} {p1} tl t pf) i | False = gteTransitive r x0 (Real x) (treeOrdered t) $ rightBounded tl $ rewrite__impl (\g => if g then p1 x else p0 x) xgx0 $ equivCov (pf x) i
    rightBounded {x} {l} {r} (TCons {x0} {p0} {p1} tl t pf) i | True = rightBounded t $ rewrite__impl (\g => if g then p1 x else p0 x) xgx0 $ equivCov (pf x) i

leftBounded : Tree k p n o v l r -> p x -> So (Real x > l)
leftBounded (Leaf _ _ pf) Refl = pf
leftBounded TEnd i = void i
leftBounded {x} (TNil pf) i = void $ equivCov (pf x) i
leftBounded {x} {l} (TCons {x0} {p0} {p1} tl t pf) i with (Real x > x0) proof xgx0
    leftBounded {x} {l} (TCons {x0} {p0} {p1} tl t pf) i | False = leftBounded tl $ rewrite__impl (\g => if g then p1 x else p0 x) xgx0 $ equivCov (pf x) i
    leftBounded {x} {l} (TCons {x0} {p0} {p1} tl t pf) i | True = case (gteCases x0 l (treeOrdered tl)) of
        (Left x0gl) => gtTransitive (Real x) x0 l (replace xgx0 Oh) x0gl
        (Right Refl) => replace xgx0 Oh

treeListSingle : Tree k p n o v l r -> Tree k p (S n) o v l r
treeListSingle {p} {l} t = TCons tNil t pf where
    pf : p <==> (\x => if Real x > l then p x else Void)
    pf x with (Real x > l) proof xgl
        pf x | True  = MkEquiv id id
        pf x | False = MkEquiv (\a => absurd $ replace (sym xgl) (leftBounded t a)) (\a => void a)

tConcat : Tree k p0 (S n) o v x0 x1 -> Tree k p1 (S n) o v x1 x2 -> (p <==> (\x => if Real x > x1 then p1 x else p0 x)) -> Tree k p (S n) o v x0 x2
tConcat {x0} {x1} {p0} {p1} tl (TNil pf1) pf0 = rephraseSet tl (equivConcat pf (equivSymm pf0)) where
    pf : p0 <==> (\x => if Real x > x1 then p1 x else p0 x)
    pf x' with (Real x' > x1) proof xgx1
        pf x' | False = MkEquiv id id
        pf x' | True = MkEquiv
            (\a => absurd $ rewrite__impl (So . not) xgx1 $ replace (sym $ gtGteConsistent (Real x') x1) $ rightBounded tl a)
            (\a => void $ equivCov (pf1 x') a)
tConcat {x0} {x1} {p0} {p1} tl0 (TCons {x0=x11} {p0=p10} {p1=p11} tl1 t pf1) pf0 = TCons (tConcat tl0 tl1 equivRefl) t (equivConcat pf0 pf) where
    pf : (\x => if Real x > x1 then p1 x else p0 x) <==> (\x => if Real x > x11 then p11 x else if Real x > x1 then p10 x else p0 x)
    pf x' with (Real x' > x1) proof xgx1
        pf x' | False with (Real x' > x11) proof xgx11
            pf x' | False | False = MkEquiv id id
            pf x' | False | True = absurd $ replace (sym xgx1) $ gtGteTransitive (Real x') x11 x1 (replace xgx11 Oh) (treeOrdered tl1)
        pf x' | True = pf1 x'


arrange : Tree k p (S n) o v l r -> Tree k p (S (S n)) o v l r
arrange {k} {p} {n} {l} {r} ts with (ts)
    arrange ts | (TNil pf) = TNil pf
    arrange ts | (TCons TNil _ _) = treeListSingle ts
    arrange ts | (TCons (TCons (TCons TNil _ _) _ _) _ _) = treeListSingle ts
    arrange {k} {p} {n} {l} {r} ts | (TCons {x0=x1} {p1=p1} {p0=p10} (TCons {x0=x0} {p1=p0} {p0=p00} ts' t0 pf0) t1 pf1) = TCons (arrange ts') pair pf
        where pairSet : k -> Type
              pairSet x = if Real x > x1 then p1 x else p0 x
              pair : Tree k pairSet (S n) o v x0 r
              pair = TCons (treeListSingle t0) t1 $ \x => MkEquiv id id
              pf : (p <==> (\x => if Real x > x0 then pairSet x else p00 x))
              pf x' with (Real x' > x1) proof xgx1
                pf x' | True with (Real x' > x0) proof xgx0
                  pf x' | True | True = rewrite__impl (\c => p x' <=> if c then p1 x' else p10 x') xgx1 $ pf1 x'
                  pf x' | True | False = absurd $ replace (sym xgx0) $ gtGteTransitive (Real x') x1 x0 (replace xgx1 Oh) $ treeOrdered t0
                pf x' | False = let
                      pf1' = rewrite__impl (\c => p x' <=> if c then p1 x' else p10 x') xgx1 (pf1 x')
                    in MkEquiv (equivCov (pf0 x') . equivCov pf1') (equivContra pf1' . equivContra (pf0 x'))

mutual
    insertT : (x:k) -> v x -> Tree k p n o v l r -> .(So (Real x > l)) -> .(So (r >= Real x)) -> Tree k (\x' => Either (p x') (x' = x)) (S n) o v l r
    insertT {l} x d (Leaf xl d0 xlgl) gtl gtr with (gteCases (Real xl) (Real x) gtr)
        insertT {l} x d (Leaf xl d0 xlgl) gtl gtr | (Left gtr') = TCons (treeListSingle $ Leaf x d gtl) (Leaf xl d0 gtr') pf where
            pf : (\x' => Either (x' = xl) (x' = x)) <==> (\x' => if Real x' > Real x then x' = xl else x' = x)
            pf x' with (x' > x) proof x'gx
                pf x' | True = rewrite__impl (\c => Either (x' = xl) (x' = x) <=> if c then x' = xl else x' = x) (trans (sym $ gtConsistent x' x) (sym x'gx)) $ MkEquiv (\a => case a of
                        Left x'exl => x'exl
                        Right x'ex => void $ gtIrreflexive x $ rewrite__impl (So . (>x)) (sym x'ex) $ replace x'gx Oh
                    ) Left
                pf x' | False = rewrite__impl (\c => Either (x' = xl) (x' = x) <=> if c then x' = xl else x' = x) (trans (sym $ gtConsistent x' x) (sym x'gx)) $ MkEquiv (\a => case a of
                        Left x'exl => absurd $ replace (sym x'gx) $ rewrite__impl (So . (>x)) (x'exl) $ unCapGt {a=xl} {b=x} gtr'
                        Right x'ex => x'ex
                    ) Right
        insertT {l} x d (Leaf xl d0 xlgl) gtl gtr | Right xlex = rephraseSet (treeListSingle $ Leaf xl d0 xlgl) pf where
            pf : (\x' => x' = xl) <==> (\x' => Either (x' = xl) (x' = x))
            pf x' = MkEquiv Left (\a => case a of
                    Left a' => a'
                    Right a' => trans a' $ sym $ unCapEq xlex
                )
    insertT x d TEnd gtl gtr = TCons (treeListSingle (Leaf x d gtl)) TEnd pf where
        pf : (\x' => Either Void (x' = x)) <==> (\x' => if Real x' > Real x then Void else x' = x)
        pf x' with (Real x' > Real x) proof gt
            pf x' | False = MkEquiv (\(Right x'ex) => x'ex) Right
            pf x' | True = MkEquiv (\(Right Refl) => void $ gtIrreflexive (Real x) $ replace gt Oh) void
    insertT x d {n=S n'} t gtl gtr = arrange $ insertTL x d t gtl gtr
    
    -- Insert an element into a *list* of trees, producing a list of trees which may be of arbitrary length.
    insertTL : (x:k) -> v x -> Tree k p (S n) o v l r -> .(So (Real x > l)) -> .(So (r >= Real x)) -> Tree k (\x' => Either (p x') (x' = x)) (S n) o v l r
    insertTL {l} x d (TNil pf) gtl gtr = void $ gtIrreflexive (Real x) $ gtGteTransitive (Real x) l (Real x) gtl gtr
    insertTL {p} x d (TCons {x0} {p0} {p1} tl t pf) gtl gtr with (Real x > x0) proof xgx0
        insertTL {p} x d (TCons {x0} {p0} {p1} tl t pf) gtl gtr | True = tConcat tl (insertT x d t (replace xgx0 Oh) gtr) pf' where
            pf' : (\x' => Either (p x') (x' = x)) <==> (\x' => if Real x' > x0 then Either (p1 x') (x' = x) else p0 x')
            pf' x' with (Real x' > x0) proof x'gx0
                pf' x' | True = MkEquiv (\a => case a of
                        Left px' => Left $ rewrite__impl (\c => if c then p1 x' else p0 x') x'gx0 $ equivCov (pf x') px'
                        Right x'ex => Right x'ex
                    ) (\a => case a of
                        Left p1x' => Left $ equivContra (pf x') $ rewrite__impl (\c => if c then p1 x' else p0 x') (sym x'gx0) p1x'
                        Right x'ex => Right x'ex
                    )
                pf' x' | False = MkEquiv (\a => case a of
                        Left px' => rewrite__impl (\c => if c then p1 x' else p0 x') x'gx0 $ equivCov (pf x') px'
                        Right x'ex => absurd $ rewrite__impl (\c => True = c) x'gx0 $ rewrite__impl (\x'' => True = Real x'' > x0) x'ex xgx0
                    ) (\a =>
                        Left $ equivContra (pf x') $ rewrite__impl (\c => if c then p1 x' else p0 x') (sym x'gx0) a
                    )
        insertTL {p} x d (TCons {x0} {p0} {p1} tl t pf) gtl gtr | False = TCons (insertTL x d tl gtl x0gex) t pf' where
            pf' : (\x' => Either (p x') (x' = x)) <==> (\x' => if Real x' > x0 then p1 x' else Either (p0 x') (x' = x))
            pf' x' with (Real x' > x0) proof x'gx0
                pf' x' | True = MkEquiv (\a => case a of
                        Left px' => rewrite__impl (\c => if c then p1 x' else p0 x') x'gx0 $ equivCov (pf x') px'
                        Right x'ex => absurd $ rewrite__impl (\c => False = c) x'gx0 $ rewrite__impl (\x'' => False = Real x'' > x0) x'ex xgx0
                    ) (\a =>
                        Left $ equivContra (pf x') $ rewrite__impl (\c => if c then p1 x' else p0 x') (sym x'gx0) a
                    )
                pf' x' | False = MkEquiv (\a => case a of
                        Left px' => Left $ rewrite__impl (\c => if c then p1 x' else p0 x') x'gx0 $ equivCov (pf x') px'
                        Right x'ex => Right x'ex
                    ) (\a => case a of
                        Left p0x' => Left $ equivContra (pf x') $ rewrite__impl (\c => if c then p1 x' else p0 x') (sym x'gx0) p0x'
                        Right x'ex => Right x'ex
                    )
            x0gex : So (x0 >= Real x)
            x0gex = replace (gtGteConsistent (Real x) x0) $ rewrite__impl (So . not) (sym xgx0) Oh

lookupT : Tree k p n o v l r -> (x:k) -> .(p x) -> v x
lookupT (Leaf x' d _) x i = replace (sym i) d
lookupT TEnd x i = void i
lookupT (TNil pf) x i = void $ equivCov (pf x) i
lookupT (TCons {x0} {p0} {p1} tl t pf) x i with (Real x > x0) proof xgx0
    lookupT (TCons {x0} {p0} {p1} tl t pf) x i | True  = lookupT t  x $ rewrite__impl (\c => if c then p1 x else p0 x) xgx0 $ equivCov (pf x) i
    lookupT (TCons {x0} {p0} {p1} tl t pf) x i | False = lookupT tl x $ rewrite__impl (\c => if c then p1 x else p0 x) xgx0 $ equivCov (pf x) i


export
data MapFrom : (s:Set) -> (underlying s -> Type) -> Type where
    MkMap : Tree k p n o v Low High -> .(p <==> p') -> MapFrom (MkSet k p') v

export
empty : VerifiedOrd t => MapFrom (empty t) v
empty @{o} = MkMap (TEnd {o}) $ \x => MkEquiv id id

export
insert : (x:k) -> v x -> MapFrom (MkSet k p') v -> MapFrom (insert (MkSet k p') x) v
insert x d (MkMap {p} {p'} t pf) = case rephraseSet (insertT x d t Oh Oh) pf' of
        TCons {x0=Low} TNil t' pf1 => MkMap t' (equivSymm pf1)
        t' => MkMap t' equivRefl
    where pf' : (\x' => Either (p x') (x' = x)) <==> (\x' => Either (p' x') (x' = x))
          pf' x' = MkEquiv
            (\a => case a of {Left a' => Left (equivCov    (pf x') a'); Right a' => Right a'})
            (\a => case a of {Left a' => Left (equivContra (pf x') a'); Right a' => Right a'})
