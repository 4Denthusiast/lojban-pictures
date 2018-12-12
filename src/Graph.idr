module Graph

import Words

import Data.SortedMap

export
NodeLabel : Type
NodeLabel = Nat

export
EdgeLabel : Type
EdgeLabel = Nat

data Edge : (stubType : Type) -> (edgeType : stubType -> stubType -> Type) -> Type where
    MkEdge : NodeLabel ->
             NodeLabel ->
             (s0 : stubType) ->
             (s1 : stubType) ->
             edgeType s0 s1 ->
             Edge stubType edgeType

export
data Graph : (stubType : Type) -> (edgeType : stubType -> stubType -> Type) -> (nodeType : Type) -> Type where
    MkGraph : SortedMap NodeLabel nodeType ->
              SortedMap EdgeLabel (Edge stubType edgeType) ->
              Graph stubType edgeType nodeType

adjustEdge : (NodeLabel -> NodeLabel) -> (Edge s e) -> (Edge s e)
adjustEdge f (MkEdge n0 n1 s0 s1 e0) = MkEdge (f n0) (f n1) s0 s1 e0

mapKeys : (Ord k, Ord k') => (k -> k') -> SortedMap k v -> SortedMap k' v
mapKeys f m = fromList $ (\(k,v) => (f k,v)) <$> toList m --This would be more efficient if it could be implemented in the library.

nextKey : SortedMap Nat v -> Nat
nextKey m = fromMaybe 0 ((1+) <$> last' (keys m))

export
Semigroup (Graph s e n) where
    (<+>) (MkGraph ns0 es0) (MkGraph ns1 es1) = MkGraph (mergeWith const ns0 (mapKeys nodeRelabel ns1)) (adjustEdge nodeRelabel <$> mergeWith const es0 (mapKeys edgeRelabel es1))
        where nodeRelabel = (+ nextKey ns0)
              edgeRelabel = (+ nextKey es0)

export
Monoid (Graph s e n) where
    neutral = MkGraph empty empty

export
lineGraph : {edgeType : stubType -> stubType -> Type} -> (a:stubType) -> (b:stubType) -> edgeType a b -> (l:List nodeType) -> {auto ok : NonEmpty l} -> Graph stubType edgeType nodeType
lineGraph x y e ns {ok} with (ns)
    | (_::ns') = MkGraph (fromList $ zip [0..(length ns')] ns) (fromList $ map (\n => (n, MkEdge n (n+1) x y e)) $ takeWhile (< length ns') [0..length ns])

export
lineOrEmptyGraph : {edgeType : stubType -> stubType -> Type} -> (a:stubType) -> (b:stubType) -> edgeType a b -> (l:List nodeType) -> Graph stubType edgeType nodeType
lineOrEmptyGraph _ _ _ [] = neutral
lineOrEmptyGraph x y e (n::ns) = lineGraph x y e (n::ns)

export
data RootedGraph : (stubType : Type) -> (edgeType : stubType -> stubType -> Type) -> (nodeType : Type) -> Type where
    MkRooted : NodeLabel -> (Graph stubType edgeType nodeType) -> RootedGraph stubType edgeType nodeType

export
uproot : RootedGraph s e n -> Graph s e n
uproot (MkRooted r g) = g

export
Functor (Graph s e) where
    map f (MkGraph ns es) = MkGraph (map f ns) es

export
Functor (RootedGraph s e) where
    map f (MkRooted n g) = MkRooted n (map f g)

-- doesn't work as an actual Monad instance because it's not total.
export
join : RootedGraph s e (RootedGraph s e n) -> RootedGraph s e n
join (MkRooted r0 (MkGraph gs es0)) = MkRooted (fromJust $ lookup r0 rs) (MkGraph ns (mergeLeft es es0'))
    where foldResult : (SortedMap NodeLabel NodeLabel, SortedMap NodeLabel n, NodeLabel, SortedMap EdgeLabel (Edge s e), EdgeLabel)
          foldResult {-(rs, ns, _, es, eOff)-} = foldr (
                  \(l, MkRooted r (MkGraph ns' es')), (rsi, nsi, nOffi, esi, eOffi) => (
                      insert l (r+nOffi) rsi,
                      mergeLeft nsi $ mapKeys (+nOffi) ns',
                      nOffi + nextKey nsi,
                      mergeLeft esi $ mapKeys (+eOffi) $ map (adjustEdge (+nOffi)) es',
                      eOffi + nextKey esi
                  )
              ) (empty, empty, 0, empty, 0) (toList gs)
          rs : SortedMap NodeLabel NodeLabel
          rs = fst foldResult
          ns = fst $ snd foldResult
          es = fst $ snd $ snd $ snd foldResult
          eOff : EdgeLabel
          eOff = snd $ snd $ snd $ snd foldResult
          fromJust : {a:Type} -> Maybe a -> a
          fromJust (Just x) = x --I know it's not Nothing in this case, assuming the input is valid.
          es0' = mapKeys (+eOff) $ map (adjustEdge (fromJust . flip lookup rs)) es0

export
pure : n -> RootedGraph s e n
pure x = MkRooted 0 (MkGraph (fromList [(0,x)]) empty)

export
lineRooted : {edgeType : stubType -> stubType -> Type} -> (a:stubType) -> (b:stubType) -> edgeType a b -> (l:List nodeType) -> {auto ok : NonEmpty l} -> RootedGraph stubType edgeType nodeType
lineRooted x y e ns {ok} = MkRooted 0 $ lineGraph x y e ns {ok}

export
graphRootUnion : Graph s e n -> RootedGraph s e n -> RootedGraph s e n
graphRootUnion g (MkRooted r g') = MkRooted r (g' <+> g)

public export
data PictureStubLabel = FreeStub | SeFreeStub | NumberedStub Nat

public export
PictureGraph : Type
PictureGraph = RootedGraph PictureStubLabel (\s0, s1 => ()) WordPicture

public export
FloatingPictureGraph : Type
FloatingPictureGraph = Graph PictureStubLabel (\s0, s1 => ()) WordPicture
