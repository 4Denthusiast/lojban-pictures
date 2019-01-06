module GraphSubstitution

import Graph

import Data.SortedMap
import Data.SortedSet
import Data.Vect

public export
EdgeLabel : Type
EdgeLabel = Nat

adjust : (a -> a) -> k -> SortedMap k a -> SortedMap k a
adjust f k m = case lookup k m of
    Nothing => m
    Just v  => insert k (f v) m

public export
-- A variant graph representation optimised for local modification. (True, e) is for edges out, and (False, e) for edges in.
record SGraph (edgeType : Type) (nodeType : Type) where
    constructor MkSGraph
    nodeMap : SortedMap NodeLabel (nodeType, List (Bool, EdgeLabel))
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
          annotate (el, MkEdge n0 n1 _) ns' = annotate' n0 True el $ annotate' n1 False el ns'

-- Given a set of nodes, partition the graph into the nodes inside, the nodes outside, and the edges between. Edges exiting the set are flipped using the function provided.
export
cutGraph : Reversable e => List NodeLabel -> SGraph e n -> (SGraph e n, SortedMap EdgeLabel (Edge e), SGraph e n)
cutGraph nl (MkSGraph ns es) = (MkSGraph nsi esii, mergeLeft esoi (map reverse esio), MkSGraph nso esoo)
    where nl' : SortedSet NodeLabel
          nl' = fromList nl
          nsi : SortedMap NodeLabel (n, List (Bool, EdgeLabel))
          nsi = fromList $ filter (flip contains nl' . fst) $ toList ns
          nso : SortedMap NodeLabel (n, List (Bool, EdgeLabel))
          nso = fromList $ filter (not . flip contains nl' . fst) $ toList ns
          esii : SortedMap EdgeLabel (Edge e)
          esii = fromList $ filter (\(_,MkEdge n0 n1 _) => contains n0 nl' && contains n1 nl') $ toList es
          esio : SortedMap EdgeLabel (Edge e)
          esio = fromList $ filter (\(_,MkEdge n0 n1 _) => contains n0 nl' && not (contains n1 nl')) $ toList es
          esoi : SortedMap EdgeLabel (Edge e)
          esoi = fromList $ filter (\(_,MkEdge n0 n1 _) => not (contains n0 nl') && contains n1 nl') $ toList es
          esoo : SortedMap EdgeLabel (Edge e)
          esoo = fromList $ filter (\(_,MkEdge n0 n1 _) => not (contains n0 nl') && not (contains n1 nl')) $ toList es
