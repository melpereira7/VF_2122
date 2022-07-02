----------------------------- MODULE PetersonN -----------------------------

EXTENDS Integers

CONSTANT N

ASSUME N > 1

VARIABLES pc, level, last, l

vars == << pc, level, last, l >>

Proc == 0..(N-1)

Init == 
    /\ pc = [ p \in Proc |-> "idle" ]
    /\ level = [ p \in Proc |-> -1 ]
    /\ last \in [ 0..(N-2) -> Proc ]
    /\ l = [ p \in Proc |-> 0 ]
    

enter(p) ==
    /\ pc[p] = "idle"
    /\ l[p] = N-1
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED << level, last, l >>


levelup(p) ==
    /\ pc[p] = "idle"
    /\ l[p] < N-1
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ level' = [level EXCEPT ![p] = l[p]]
    /\ last' = [last EXCEPT ![l[p]] = p]
    /\ UNCHANGED l
    

wait(p) ==
    /\ pc[p] = "wait"
    /\ ~(last[l[p]]) = p /\ \E k \in Proc : k # p /\ level[k] >= l[p]
    /\ l' = [l EXCEPT ![p] = l[p]+1]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED << last, level >>
    

exit(p) == 
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ level' = [level EXCEPT ![p] = -1]
    /\ l' = [l EXCEPT ![p] = 0]
    /\ UNCHANGED last
    
    
    
    
execute(p) == enter(p) \/ levelup(p) \/ wait(p) \/ exit(p)  
    
Next == \E p \in Proc : enter(p) \/ levelup(p) \/ wait(p) \/ exit(p)    
    
Spec == Init /\ [][Next]_vars

MutualExclusion == [] ~(\E i \in Proc: \E j \in Proc: i#j /\ pc[i] = "critical" /\ pc[j] = "critical")

\* Para verificar lockout freedom é necessária weak fairness para cada processo

Fairness == \A p \in Proc : WF_vars(execute(p))

LockoutFreedom == Fairness => \A p \in Proc : [] (pc[p] = "wait" => <> (pc[p] = "critical"))


=============================================================================
\* Modification History
\* Last modified Fri May 06 11:37:19 WEST 2022 by mel
\* Created Fri Apr 29 11:33:33 WEST 2022 by mel
