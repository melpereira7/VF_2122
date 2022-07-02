----------------------------- MODULE petersonN -----------------------------
EXTENDS Integers

CONSTANT N

ASSUME N > 1

VARIABLES pc, level, last, l

Proc == 0..(N-1)

Init ==
       /\ pc = [ p \in Proc |-> "idle" ]
       /\ level = [ p \in Proc |-> -1 ]
       /\ last = [ lv \in 0..(N-2) |-> 0 ]
       /\ l = [ p \in Proc |-> -1 ]
       
Enter(p) ==
          (* Guard *)
       /\ pc[p] = "idle"
          (* Effect *)
       /\ pc' = [ pc EXCEPT ![p] = "waiting" ]
       /\ level' = [ level EXCEPT ![p] = 0 ]
       /\ l' = [ l EXCEPT ![p] = 0 ]
       /\ last' = [ last EXCEPT ![l'[p]] = p ]
     
LevelUp(p) ==
          (* Guard *)
       /\ pc[p] = "waiting"
       /\ l[p] < N-2
       /\ ~ (last[l[p]] = p /\ \E k \in Proc : (k # p /\ level[k] >= l[p]))
          (* Effect *)
       /\ pc' = pc
       /\ l' = [ l EXCEPT ![p] = l[p]+1 ]   
       /\ level' = [ level EXCEPT ![p] = l'[p] ]
       /\ last' = [ last EXCEPT ![l'[p]] = p ]
       
EnterCritical(p) ==
          (* Guard *)
       /\ pc[p] = "waiting"
       /\ l[p] = N-2
       /\ ~ (last[l[p]] = p /\ \E k \in Proc : (k # p /\ level[k] >= l[p]))
          (* Effect *)
       /\ pc' = [ pc EXCEPT ![p] = "critical" ]
       /\ l' = [ l EXCEPT ![p] = -1 ]  
       /\ UNCHANGED << level, last >>
       
LeaveCritical(p) ==
          (* Guard *)
       /\ pc[p] = "critical"
          (* Effect *)
       /\ pc' = [ pc EXCEPT ![p] = "idle" ]
       /\ level' = [ level EXCEPT ![p] = -1 ] 
       /\ UNCHANGED << last, l >>
       
Next == \E p \in Proc : (\/ Enter(p)
                         \/ LevelUp(p)
                         \/ EnterCritical(p)
                         \/ LeaveCritical(p))
                      
TypesOK == /\ pc \in [Proc -> {"idle", "waiting", "critical"}]       
           /\ level \in [Proc -> -1..N-2]             
           /\ last \in [0..N-2 -> Proc]
           /\ l \in [0..N-1 -> -1..N-2]
                      
Spec == Init /\ [][Next]_<<pc, level, last, l>>                      

MutualExclusion == [] (\A p1, p2 \in Proc : pc[p1] = "critical" /\ pc[p2] = "critical" => p1 = p2)
=============================================================================
\* Modification History
\* Last modified Tue May 17 15:33:33 WEST 2022 by mane
\* Created Fri Apr 29 11:34:25 WEST 2022 by mane
