module GraphSubstitution

import Graph

import Data.SortedMap
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
data SGraph : (edgeType : Type) -> (nodeType : Type) -> Type where
    MkSGraph :
        SortedMap NodeLabel (nodeType, List (Bool, EdgeLabel)) ->
        SortedMap EdgeLabel (Edge edgeType) ->
        SGraph edgeType nodeType

public export
convertGraph : Graph i e n -> SGraph e n
convertGraph (MkGraph rs ns es) = MkSGraph (foldr annotate (map (\n => (n,[])) ns) es') (fromList es')
    where es' : List (EdgeLabel, Edge e)
          es' = zip [0..length es] es
          annotate' : NodeLabel -> Bool -> EdgeLabel -> SortedMap NodeLabel (n, List (Bool, EdgeLabel)) -> SortedMap NodeLabel (n, List (Bool, EdgeLabel))
          annotate' l b s ns' = adjust (\(n,ss) => (n,(b,s)::ss)) l ns'
          annotate (el, MkEdge n0 n1 _) ns' = annotate' n0 True el $ annotate' n1 False el ns'
