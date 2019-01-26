module GraphSubstitution

import Graph

import Data.SortedMap
import Data.SortedSet
import Data.Vect

public export
EdgeLabel : Type
EdgeLabel = Nat

public export
DirEdgeLabel : Type
DirEdgeLabel = (Bool, EdgeLabel)

public export
Reversable DirEdgeLabel where
    reverse (r,e) = (not r, e)

adjust : (a -> a) -> k -> SortedMap k a -> SortedMap k a
adjust f k m = case lookup k m of
    Nothing => m
    Just v  => insert k (f v) m

lookupMax : SortedMap k v -> Maybe (k,v)
lookupMax = last' . toList

public export
-- A variant graph representation optimised for local modification. (False, e) is for edges out, and (True, e) for edges in.
record SGraph (edgeType : Type) (nodeType : Type) where
    constructor MkSGraph
    nodeMap : SortedMap NodeLabel (nodeType, List DirEdgeLabel)
    edgeMap : SortedMap EdgeLabel (Edge edgeType)

export
Functor (SGraph e) where
    map f (MkSGraph ns es) = MkSGraph (map (\(n,es) => (f n, es)) ns) es

public export
convertGraph : Graph i e n -> SGraph e n
convertGraph (MkGraph rs ns es) = MkSGraph (foldr annotate (map (\n => (n,[])) ns) es') (fromList es')
    where es' : List (EdgeLabel, Edge e)
          es' = zip [0..length es] es
          annotate' : NodeLabel -> Bool -> EdgeLabel -> SortedMap NodeLabel (n, List (Bool, EdgeLabel)) -> SortedMap NodeLabel (n, List (Bool, EdgeLabel))
          annotate' l b s ns' = adjust (\(n,ss) => (n,(b,s)::ss)) l ns'
          annotate (el, MkEdge n0 n1 _) ns' = annotate' n0 False el $ annotate' n1 True el ns'

export --TODO get rid of instances of this in Render.
maybeReverse : Reversable e => Bool -> e -> e
maybeReverse False = id
maybeReverse True  = reverse

export
getNode : SGraph e n -> NodeLabel -> Maybe n
getNode g nl = map fst $ lookup nl $ nodeMap g

export
getAdjEdges : SGraph e n -> NodeLabel -> Maybe (List DirEdgeLabel)
getAdjEdges g nl = map snd $ lookup nl $ nodeMap g

export
getEdge : Reversable e => SGraph e n -> DirEdgeLabel -> Maybe (Edge e)
getEdge g (r,el) = map (maybeReverse r) $ lookup el $ edgeMap g

export
getAdjEdges' : Reversable e => SGraph e n -> NodeLabel -> Maybe (List (DirEdgeLabel, e, NodeLabel))
getAdjEdges' g nl = getAdjEdges g nl >>= traverse (\el => (\(MkEdge _ nl' e) => (el, e, nl')) <$> getEdge g el)

export
deleteEdge : Reversable e => SGraph e n -> DirEdgeLabel -> SGraph e n
deleteEdge g el = case getEdge g el of
    Nothing => g
    Just (MkEdge nl0 nl1 _) => record {edgeMap $= delete (snd el), nodeMap $= adjust (map $ delete el) nl0 . adjust (map $ delete $ reverse el) nl1} g

export
deleteNode : Reversable e => SGraph e n -> NodeLabel -> SGraph e n
deleteNode g nl = fromMaybe g $ record {nodeMap $= delete nl} <$> foldl deleteEdge g <$> getAdjEdges g nl

export
setNode : SGraph e n -> NodeLabel -> n -> SGraph e n
setNode g nl n = record {nodeMap $= adjust (\(_,ss) => (n,ss)) nl} g

export
addEdge : SGraph e n -> Edge e -> SGraph e n
addEdge g (MkEdge n0 n1 ed) = record {nodeMap $= adjust (map ((False,el)::)) n0 . adjust (map ((True,el)::)) n1, edgeMap $= insert el (MkEdge n0 n1 ed)} g
    where el = fromMaybe 0 $ map (+1) $ fst <$> lookupMax (edgeMap g)


-- Given a set of nodes, partition the graph into the nodes inside, the nodes outside, and the edges between. Edges exiting the set are flipped using the function provided.
export
cutGraph : Reversable e => List NodeLabel -> SGraph e n -> (SGraph e n, SortedMap EdgeLabel (Edge e), SGraph e n)
cutGraph nl (MkSGraph ns es) = (MkSGraph nsi esii, mergeLeft esoi (map reverse esio), MkSGraph nso esoo)
    where nl' : SortedSet NodeLabel
          nl' = fromList nl
          esii : SortedMap EdgeLabel (Edge e)
          esii = fromList $ filter (\(_,MkEdge n0 n1 _) => contains n0 nl' && contains n1 nl') $ toList es
          esio : SortedMap EdgeLabel (Edge e)
          esio = fromList $ filter (\(_,MkEdge n0 n1 _) => contains n0 nl' && not (contains n1 nl')) $ toList es
          esoi : SortedMap EdgeLabel (Edge e)
          esoi = fromList $ filter (\(_,MkEdge n0 n1 _) => not (contains n0 nl') && contains n1 nl') $ toList es
          esoo : SortedMap EdgeLabel (Edge e)
          esoo = fromList $ filter (\(_,MkEdge n0 n1 _) => not (contains n0 nl') && not (contains n1 nl')) $ toList es
          xor : Bool -> Bool -> Bool
          xor a b = if a then not b else b
          ns' : SortedMap NodeLabel (n, List (Bool, EdgeLabel))
          ns' = map (\(x, nes) => (x, map (\(b,el) => (xor b $ isJust $ lookup el esio, el)) nes)) ns
          nsi : SortedMap NodeLabel (n, List (Bool, EdgeLabel))
          nsi = fromList $ filter (flip contains nl' . fst) $ toList ns'
          nso : SortedMap NodeLabel (n, List (Bool, EdgeLabel))
          nso = fromList $ filter (not . flip contains nl' . fst) $ toList ns'

export
(Show e, Show n) => Show (SGraph e n) where
    showPrec d (MkSGraph ns es) = showCon d "MkSGraph" $ showArg ns ++ showArg es
