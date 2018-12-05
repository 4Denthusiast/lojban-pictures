module Graph

export
NodeLabel, EdgeLabel : Type
NodeLabel = Nat
EdgeLabel = Nat

data Edge : (stubType : Type) -> (edgeType : stubType -> stubType -> Type) where
    MkEdge : NodeLabel ->
             NodeLabel ->
             (s0 : stubType) ->
             (s1 : stubType) ->
             edgeType s0 s1 ->
             Edge stubType edgeType

export
data Graph : (nodeType : Type) -> (stubType : Type) -> (edgeType : stubType -> stubType -> Type) -> Type where
    MkGraph : SortedMap NodeLabel (nodeType, List EdgeLabel) ->
              SortedMap EdgeLabel (Edge edgeType stubType) ->
              Graph nodeType stubType edgeType

export public
data PictureStubLabel = FreeStub | SeFreeStub | NumberedStub Nat

data RootedGraph n s e = MkRooted n s (Graph n s e)

export public
PictureGraph : Type
PictureGraph = RootedGraph Picture PictureStubLabel (\s0, s1 => ())
