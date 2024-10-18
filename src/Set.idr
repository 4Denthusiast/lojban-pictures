module Set

%access public export

data Set : Type where
    MkSet : (t:Type) -> .(p:t -> Type) -> Set

underlying : Set -> Type
underlying (MkSet t _) = t

data Member : Set -> Type where
    MkMember : .{t:Type} -> .{p:t -> Type} -> (x:t) -> .(pf:p x) -> Member (MkSet t p)

forget : Member (MkSet t _) -> t
forget (MkMember x _) = x

empty : Type -> Set
empty t = MkSet t (\_ => Void)

universal : Type -> Set
universal t = MkSet t (\_ => ())

inUniversal : t -> Member (universal t)
inUniversal x = MkMember x ()

singleton : {t:Type} -> t -> Set
singleton {t} x = MkSet t (\y => x = y)

inSingleton : (x:t) -> Member (singleton x)
inSingleton {t} x = MkMember x Refl

insert : (s:Set) -> underlying s -> Set
insert (MkSet t p) x = MkSet t (\x' => Either (p x') (x' = x))
