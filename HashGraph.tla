---- MODULE HashGraph ----------------------------------------------------------
EXTENDS Naturals, Sequences, SequencesExt, Graph, FiniteSets, TLC
(* Documentation *)
(* This module models the distributed consensus algorithm Hashgraph *)
--------------------------------------------------------------------------------
VARIABLES E, EGraph
vars == <<E, EGraph>>

CONSTANT MaxEvents, MaxTime, Honest, Byzantine, Payload, Self

Peer == Honest \cup Byzantine

AXIOM Honest # {}
AXIOM Self \in Honest

(* Coin flip constant*)
CONSTANT c
ASSUME c > 2

(* Number of rounds before election *)
CONSTANT d
ASSUME d > 0

Time == 0..MaxTime
n == Cardinality(Peer)
Signature == 0..MaxEvents
Id == [creator : Peer, sig : Signature] \cup {{}}

Event == [
    payload : Payload,
    self_parent : Id,
    other_parent : Id,
    time : Time,
    creator : Peer,
    sig : Signature (* is unique, id models hash which cannot be faked *)
]

Lookup(id) ==
    CHOOSE e \in ToSet(E) : /\ e.sig = id.sig
                            /\ e.creator = id.creator

Max(S) ==
    CHOOSE e \in S : \A elt \in S : e >= elt

Min(S) ==
    CHOOSE e \in S : \A elt \in S : e <= elt

(* think variables would make more sense the other way around, sticking
   to paper for now *)
(* read: y ancestor of x *)
RECURSIVE Ancestor(_,_)
Ancestor(x,y) ==
    \/ x = y
    \/ \E z \in {Lookup(id) : id \in {x.self_parent, x.other_parent}} : Ancestor(z,y)

RECURSIVE SelfAncestor(_,_)
SelfAncestor(x,y) ==
    \/ x = y
    \/ /\ x.self_parent # {}
       /\ SelfAncestor(Lookup(x.self_parent),y)

ManyCreators(S) ==
    /\ 3*Cardinality(S) > 2*n
    /\ \A x \in S :
       \A y \in S :
         x # y => x.creator # y.creator

(* x sees y *)
See(x,y) ==
    /\ Ancestor(x,y)
    /\ ~ \E a \in ToSet(E) :
         \E b \in ToSet(E) :
           /\ y.creator = a.creator
           /\ a.creator = b.creator
           /\ Ancestor(x,a)
           /\ Ancestor(x,b)
           /\ ~ SelfAncestor(a,b)
           /\ ~ SelfAncestor(b,a)

StronglySee(x,y) ==
    /\ See(x,y)
    /\ \E S \in SUBSET ToSet(E) :
         /\ ManyCreators(S)
         /\ \A z \in S :
              /\ See(x,z)
              /\ See(z,y)

RECURSIVE Round(_)
RECURSIVE SelfParentRound(_)
RECURSIVE RoundHelper(_,_)
RoundHelper(x,previous) ==
    IF \E S \in SUBSET ToSet(E) :
        /\ ManyCreators(S)
        /\ \A y \in S :
            /\ Round(y) = previous + 1
            /\ StronglySee(x,y)
    THEN RoundHelper(x,previous + 1)
    ELSE previous

(* the literal translation of the functional spec is *)
(* Round(x) == *)
(*     Max({SelfParentRound(x)} *)
(*      \cup { r \in Nat : *)
(*             \E S \in SUBSET ToSet(E) : *)
(*              /\ ManyCreators(S) *)
(*              /\ \A y \in S : *)
(*                  /\ Round(y) = r - 1 *)
(*                  /\ StronglySee(x,y) }) *)
(* which cannot be evaluated by tlc *)

(* in order to rewrite this into a function tlc can evaluate
   See(x,y) /\ SelfAncestor(y,z) => See(x,z) is needed.
   See(x,z) is Ancestor(x,z) /\ P for P being the rest.
   Since
   See(x,y) => Ancestor(x,y)
   and
   SelfAncestor(y,z) => Ancestor(y,z)
   hold it follows that
   See(x,y) /\ SelfAncestor(y,z) => Ancestor(x,y) /\ Ancestor(y,z) => Ancestor(x,z)
   and since
   (A => B) /\ (A => C) <=> (A => B /\ C)
   it remains to show that
   See(x,y) /\ SelfAncestor(y,z) => P
   holds.
   This is equivalent to proving the statement
   ~P => ~SelfAncestor(y,z) \/ ~See(x,y)
   Proof:
   I:
   ~P = ~P /\ TRUE = (~P /\ SelfAncestor(y,z)) \/ (~P /\ ~SelfAncestor(y,z))
   => (~P /\ SelfAncestor(y,z)) \/ ~SelfAncestor(y,z))
   II:
   ~P = \E (a,b) \in E x E :
         /\ z.creator = a.creator = b.creator
         /\ Ancestor(x,a)
         /\ Ancestor(x,b)
         /\ ~SelfAncestor(a,b)
         /\ ~SelfAncestor(b,a)
   and
   SelfAncestor(y,z) => y.creator = z.creator
   thus leading to
   III:
   ~P /\ SelfAncestor(y,z) => \E (a,b) \in E x E :
                               /\ y.creator = a.creator = b.creator
                               /\ Ancestor(x,a)
                               /\ Ancestor(x,b)
                               /\ ~SelfAncestor(a,b)
                               /\ ~SelfAncestor(b,a)
   This last implied proposition is ~P'
   where
   See(x,y) = Ancestor(x,y) /\ P'
   which is equivalent to ~See(x,y) = ~Ancestor(x,y) \/ ~P'
   so ~P' => ~See(x,y) and III: ~P /\ SelfAncestor(y,z) => ~P'
   leading to IV: ~P /\ SelfAncestor(y,z) => ~See(x,y)
   using I+IV it follows that ~P => ~See(x,y) \/ ~SelfAncestor(x,y)
   QED

   From this result it follows that
   StronglySee(x,y) /\ SelfParent(y,z) => StronglySee(x,z)
   *)



SelfParentRound(x) ==
    IF x.self_parent = {}
    THEN 1
    ELSE Round(Lookup(x.self_parent))

Witness(x) ==
    \/ x.self_parent = {}
    \/ Round(x) > Round(Lookup(x.self_parent))

Diff(x,y) ==
    Round(x) - Round(y)

RECURSIVE Vote(_,_)
Votes(x,y,v) ==
    Cardinality({z \in ToSet(E) :
                  /\ Diff(x,z) = 1
                  /\ Witness(z)
                  /\ StronglySee(x,z)
                  /\ Vote(z,y) = v})

(*FractTrue(x,y) == FractDenom(x,y) / FractNom(x,y)*)
FractDenom(x,y) == Votes(x,y,TRUE)
FractNom(x,y) == Max({1,Votes(x,y,TRUE)+Votes(x,y,TRUE)})

RECURSIVE Decide(_,_)
Decide(x,y) ==
    \/ /\ x.self_parent # {}
       /\ Decide(Lookup(x.self_parent),y)
    \/ /\ Witness(x)
       /\ Witness(y)
       /\ Diff(x,y) > d
       /\ Diff(x,y) % c > 0
       /\ \E v \in {TRUE,FALSE} : 3*Votes(x,y,v) > 2*n

CopyVote(x,y) ==
    \/ ~ Witness(x)
    \/ /\ x.self_parent # {}
       /\ Decide(Lookup(x.self_parent),y)

MiddleBit(x) == 1

Vote(x,y) ==
    IF CopyVote(x,y)
    THEN Vote(Lookup(x.self_parent),y)
    ELSE IF /\ ~ CopyVote(x,y)
            /\ Diff(x,y) = d
         THEN See(x,y)
         ELSE IF /\ ~ CopyVote(x,y)
                 /\ Diff(x,y) # d
                 /\ Diff(x,y) % c = 0
                 /\ FractNom(x,y) <= 3*FractDenom(x,y)
                 /\ 3*FractDenom(x,y) <= 2
              THEN 1 = MiddleBit(x.sig)
              ELSE 2*FractDenom(x,y) >= FractNom(x,y)

Famous(x) ==
    \E y \in ToSet(E) :
     /\ Decide(y,x)
     /\ Vote(y,x)

UniqueFamous(x) ==
    /\ Famous(x)
    /\ ~ \E y \in ToSet(E) :
          /\ y # x
          /\ Famous(y)
          /\ Round(x) = Round(y)
          /\ x.creator = y.creator

RoundsDecided(r) ==
    \A x \in ToSet(E) :
     (/\ Round(x) <= r
     /\ Witness(x)) =>
     \E y \in ToSet(E) : Decide(y,x)

RECURSIVE RoundReceivedHelper(_,_)
RoundReceivedHelper(r,x) ==
    IF /\ RoundsDecided(r)
       /\ \A y \in ToSet(E) :
           (/\ Round(y) = r
            /\ UniqueFamous(y)) => Ancestor(y,x)
    THEN r
    ELSE RoundReceivedHelper(r+1,x)

RoundReceived(x) ==
    RoundReceivedHelper(0,x)

(* Geq(x,y) == x <= y *)

(* Median(S) == *)
(*     LET sorted == SortSeq(SetToSeq(S),Geq) *)
(*     IN IF Cardinality(S) % 2 = 0 *)
(*        THEN (sorted[Cardinality(S) \div 2] + sorted[Cardinality(S) \div 2 + 1]) \div 2 *)
(*        ELSE sorted[Cardinality(S) \div 2 + 1] *)

Abs(x) ==
    IF x < 0 THEN 0-x
             ELSE x

RECURSIVE Gcd(_,_)
Gcd(x,y) ==
    IF \/ x < 0
       \/ y < 0
    THEN Gcd(Abs(x),Abs(y))
    ELSE IF x*y = 0
         THEN x + y
         ELSE IF x > y
              THEN Gcd(y,x)
              ELSE Gcd(x,y-x)

Average(S) ==
    LET elt == CHOOSE e \in S : TRUE
        RECURSIVE Sum(_)
        Sum(X) == Sum(X \ {elt}) + elt
    IN
    <<Sum(S) \div Gcd(Sum(S), Cardinality(S)),
      Cardinality(S) \div Gcd(Sum(S),Cardinality(S))>>

Median(S) ==
    LET takeaverage ==
         CHOOSE R \in SUBSET S :
          /\ Cardinality(R) = IF Cardinality(S) % 2 = 0 THEN 2
                                                         ELSE 1
          /\ Cardinality({s \in S \ R : s <= Min(R)})
             = Cardinality({s \in S \ R : s >= Max(R)})
    IN
    Average(takeaverage)


TimeReceived(x) ==
    LET H == {y \in ToSet(E) :
               /\ Ancestor(y,x)
               /\ \E z \in ToSet(E) :
                   /\ Round(z) = RoundReceived(x)
                   /\ UniqueFamous(z)
                   /\ SelfAncestor(z,y)
                   /\ ~ \E w \in ToSet(E) :
                         /\ SelfAncestor(y,w)
                         /\ Ancestor(w,x)}
    IN
    Median({y.time : y \in H})
================================================================================
