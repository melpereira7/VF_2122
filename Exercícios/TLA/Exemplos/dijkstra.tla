------------------------------ MODULE dijkstra ------------------------------

EXTENDS Naturals

\* There are N+1 K-State machines, numbered from 0 to N.
\* FIRST is the "first machine" of the ring. In the paper, it is the machine 0, but could be anyone
CONSTANT N, K, FIRST

ASSUME /\ N > 0 
       /\ K > N
       /\ FIRST \in 0..N

VARIABLES values

TypesOK == values \in [0..N -> 0..K-1]

Init == TypesOK

\* Lefthand neighbor of p
L[p \in 0..N] == (p-1) % (N+1) 
                   
Inc[v \in 0..K-1] == (v+1) % K 
                   
Move(p) == \/ /\ p = FIRST
              /\ values[L[FIRST]] = values[FIRST]
              /\ values' = [ values EXCEPT ![FIRST] = Inc[values[FIRST]] ]
                             
           \/ /\ p # FIRST 
              /\ values[p] # values[L[p]]
              /\ values' = [ values EXCEPT ![p] = values[L[p]] ]            

Next == \E p \in 0..N : Move(p) 

Spec == Init /\ [][Next]_<<values>> /\ WF_<<values>>(Next)

OnlyOneEnabled == \A p1, p2 \in 0..N : ENABLED(Move(p1)) /\ ENABLED(Move(p2)) => p1 = p2

SelfStabilization == <> OnlyOneEnabled

Stabilized == [] (OnlyOneEnabled => [] OnlyOneEnabled)
=============================================================================
\* Modification History
\* Last modified Tue May 17 15:11:33 WEST 2022 by mane
\* Created Fri May 06 11:45:12 WEST 2022 by mane
