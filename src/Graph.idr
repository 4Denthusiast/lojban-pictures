module Graph

import Words

import Data.SortedMap
import Data.Vect

public export
NodeLabel : Type
NodeLabel = Nat

-- The graph representation is directed, but what I really want is an undirected graph, but with directed edge labels.
public export
interface Reversable t where
    reverse : t -> t

public export
data Edge : (edgeType : Type) -> Type where
    MkEdge : NodeLabel ->
             NodeLabel ->
             edgeType ->
             Edge edgeType

export
Reversable e => Reversable (Edge e) where
    reverse (MkEdge n0 n1 x) = MkEdge n1 n0 (reverse x)

public export
edgeData : Edge e -> e
edgeData (MkEdge _ _ x) = x

-- invariants: All the NodeLabels referred to in the edge and root lists actually exist.
public export
data Graph : (nRoots : Nat) -> (edgeType : Type) -> (nodeType : Type) -> Type where
    MkGraph : Vect nRoots NodeLabel ->
              SortedMap NodeLabel nodeType ->
              List (Edge edgeType) ->
              Graph nRoots edgeType nodeType

export
graphNodes : Graph i e n -> SortedMap NodeLabel n
graphNodes (MkGraph _ ns _) = ns

export
graphEdges : Graph i e n -> List (Edge e)
graphEdges (MkGraph _ _ es) = es

-- naturality of the function should guarantee that the graph invariant is preserved.
export
permuteRoots : ({a:Type} -> Vect i a -> Vect i' a) -> Graph i e n -> Graph i' e n
permuteRoots f (MkGraph rs ns es) = MkGraph (f rs) ns es

export
uproot : {i:Nat} -> {i':Nat} -> {auto ok: i = i' + minus i i'} -> Graph i e n -> Graph i' e n
uproot {i} {i'} {ok} (MkGraph r n e) = MkGraph (take i' $ replace ok r) n e

export
getRoot : Fin i -> Graph i e n -> n
getRoot x (MkGraph rs ns es) = (\(Just a) => a) $ lookup (index x rs) ns

adjustEdge : (NodeLabel -> NodeLabel) -> (Edge e) -> (Edge e)
adjustEdge f (MkEdge n0 n1 e0) = MkEdge (f n0) (f n1) e0

mapKeys : (Ord k, Ord k') => (k -> k') -> SortedMap k v -> SortedMap k' v
mapKeys f m = fromList $ (\(k,v) => (f k,v)) <$> toList m --This would be more efficient if it could be implemented in the library.

nextKey : SortedMap Nat v -> Nat
nextKey m = fromMaybe 0 ((1+) <$> last' (keys m))

export
graphUnion : Graph i e n -> Graph i' e n -> Graph (i+i') e n
graphUnion (MkGraph rs0 ns0 es0) (MkGraph rs1 ns1 es1) = MkGraph
        (rs0 ++ (map nodeRelabel rs1))
        (mergeLeft ns0 (mapKeys nodeRelabel ns1))
        (map (adjustEdge nodeRelabel) es1 ++ es0)
    where nodeRelabel = (+ nextKey ns0)

export
Semigroup (Graph 0 e n) where
    (<+>) = graphUnion

export
Monoid (Graph 0 e n) where
    neutral = MkGraph [] empty empty

export
lineGraph : edgeType -> (l:List nodeType) -> {auto ok : NonEmpty l} -> Graph 2 edgeType nodeType
lineGraph e ns {ok} with (ns)
    | (_::ns') = MkGraph [0, length ns'] (fromList $ zip [0..(length ns')] ns) (map (\n => MkEdge n (n+1) e) $ takeWhile (< length ns') [0..length ns])

export
lineOrEmptyGraph : edgeType -> (l:List nodeType) -> Graph 0 edgeType nodeType
lineOrEmptyGraph _ [] = neutral
lineOrEmptyGraph e (n::ns) = uproot $ lineGraph e (n::ns)

export
Functor (Graph i e) where
    map f (MkGraph rs ns es) = MkGraph rs (map f ns) es

vectFlatten : Vect i (Vect j x) -> Vect (i*j) x
vectFlatten [] = []
vectFlatten (x::xs) = x ++ vectFlatten xs

-- doesn't work as an actual Monad instance because it's not total. Also it's graded.
export
join : {i:Nat} -> {i':Nat} -> Graph i e (Graph i' e n) -> Graph (i*i') e n
join {i} {i'} (MkGraph r0 gs es0) = MkGraph (vectFlatten $ map (fromJust . flip lookup rs) r0) ns (es0' ++ es)
    where foldResult : (SortedMap NodeLabel (Vect i' NodeLabel), SortedMap NodeLabel n, NodeLabel, List (Edge e))
          foldResult {-(rs, ns, nOff, es)-} = foldl (
                  \(rsi, nsi, nOffi, esi), (l, MkGraph r ns' es') => (
                      insert l ((+nOffi)<$>r) rsi,
                      mergeLeft nsi $ mapKeys (+nOffi) ns',
                      nOffi + nextKey ns',
                      map (adjustEdge (+nOffi)) es' ++ esi
                  )
              ) (empty, empty, 0, []) (toList gs)
          rs : SortedMap NodeLabel (Vect i' NodeLabel)
          rs = fst foldResult
          ns = fst $ snd foldResult
          es = snd $ snd $ snd foldResult
          fromJust : {a:Type} -> Maybe a -> a
          fromJust (Just x) = x --I know it's not Nothing in this case, assuming the input is valid.
          es0' = concatMap (adjustEdge' (fromJust . flip lookup rs)) es0
          adjustEdge' : (NodeLabel -> Vect i' NodeLabel) -> Edge e -> List (Edge e)
          adjustEdge' f (MkEdge n0 n1 e) = toList $ (\n0', n1' => MkEdge n0' n1' e) <$> f n0 <*> f n1

export
pure : n -> Graph 1 e n
pure x = MkGraph [0] (fromList [(0,x)]) []

export
addEdge : Fin i -> Fin i -> edgeType -> Graph i edgeType nodeType -> Graph i edgeType nodeType
addEdge i0 i1 e (MkGraph rs ns es) = MkGraph rs ns (MkEdge (index i0 rs) (index i1 rs) e :: es)

export
starGraph : edgeType -> nodeType -> List nodeType -> Graph 1 edgeType nodeType
starGraph e rn ns = MkGraph [0] (fromList ((0,rn)::zip ((+1)<$>indices) ns)) ((\i => MkEdge 0 (i+1) e) <$> indices)
    where indices = takeWhile (< length ns) [0..length ns] -- can't subtract in Nat

public export
PictureGraph : Nat -> Type
PictureGraph i = Graph i PictureEdgeLabel WordPicture

export
Reversable PictureEdgeLabel where
    reverse (x,y) = (y,x)

export
enclosePicture : {i:Nat} -> PictureGraph 1 -> PictureGraph i -> PictureGraph (S i)
enclosePicture {i} a b = case (graphUnion a b') of
        MkGraph (r::r'::rs) ns es => MkGraph (r::rs) ns (es ++ map (\n => MkEdge r n (Around,Inside)) (filter (>= r') $ map fst $ toList $ ns))
    where b' : PictureGraph (1+i)
          b' = (\(MkGraph rs ns es) => MkGraph (0::rs) ns es) b

export
(Show k, Show v) => Show (SortedMap k v) where
    showPrec d m = showCon d "fromList" $ showArg (toList m)

export
(Show e) => Show (Edge e) where
    show (MkEdge n0 n1 e) = show n0 ++ "--" ++ show e ++ "--" ++ show n1

export
(Show e, Show n) => Show (Graph i e n) where
    showPrec d (MkGraph rs ns es) = showCon d "MkGraph" $ showArg rs ++ showArg ns ++ showArg es
