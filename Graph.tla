---- MODULE Graph --------------------------------------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE FiniteSets
(* Documentation *)
--------------------------------------------------------------------------------
(* as there doesn't seem to be a generic way of testing whether something is a
   function or not, this operator will fail when given a G that isn't a function *)
IsDirectedGraph(G) ==
    /\ DOMAIN G = {"node","edge"}
    /\ G = [node |-> G.node, edge |-> G.edge]
    /\ G.edge \subseteq G.node \X G.node

DirectedSubgraph(G) ==
    { sub \in [node : SUBSET G.node, edge : SUBSET G.edge ] : IsDirectedGraph(sub) }

IsDirectedSubgraph(H,G) ==
     H \in DirectedSubgraph(G)

IsUndirectedGraph(G) ==
    /\ IsDirectedGraph(G)
    /\ \A <<n,m>> \in G.edge : <<m,n>> \in G.edge

UndirectedSubgraph(G) ==
    { sub \in DirectedSubgraph(G) : IsUndirectedGraph(sub) }

S1 & S2 ==
    { s \o t : s \in S1, t \in S2 }

(* Returns the set of non-intersecting paths through G,
   assuming G is a finite graph *)
RECURSIVE PathsUpToLen(_,_)
LOCAL PathsUpToLen(G,n) ==
    LET smallerpath == PathsUpToLen(G,n-1)
    IN
    IF n = 1
    THEN { <<node>> : node \in G.node }
    ELSE  { path \in smallerpath & PathsUpToLen(G,1) :
           /\ <<path[Len(path)-1], path[Len(path)]>> \in G.edge
           /\ \A i \in 1..Len(path)-1 : path[i] # path[Len(path)] } \cup smallerpath

Path(G) == PathsUpToLen(G,Cardinality(G.node))

AreConnectedIn(m,n,G) ==
    \E path \in Path(G) : /\ path[1] = m
                          /\ path[Len(path)] = n

(* there exist paths from every node to every other node *)
IsStronglyConnected(G) ==
    \A <<i,j>> \in G.node \X G.node : AreConnectedIn(i,j,G)

(**)
Cycle(G) ==
    { path \in Path(G) & PathsUpToLen(G,1) :
      /\ Len(path) # 1
      /\ path[1] = path[Len(path)]
      /\ <<path[Len(path)-1], path[Len(path)]>> \in G.edge }

IsDAG(G) ==
    /\ IsDirectedGraph(G)
    /\ Cycle(G) = {}

Union(G1,G2) ==
    [node |-> G1.node \cup G2.node, edge |-> G1.edge \cup G2.edge]

Intersect(G1,G2) ==
    [node |-> G1.node \cap G2.node, edge |-> G1.edge \cap G2.edge]

(* complete graph without loops *)
CompleteGraph(N) ==
    [node |-> N, edge |-> N \X N \ {<<n,n>> : n \in N}]
================================================================================
