------------------------------ MODULE sapos ------------------------------
EXTENDS Integers

CONSTANT N 

VARIABLES rochas

ASSUME N % 2 = 0

TypeOK ==
    rochas \in [0..N -> {"cor1", "cor2", "empty"}]

Init == 
    /\ rochas = [i \in 0..N |-> IF i < N \div 2 
                                THEN "cor1" 
                                ELSE    IF i > N \div 2 
                                        THEN "cor2" 
                                        ELSE "empty"]


Move(s) ==
   \/   /\ s < N
        /\ rochas[s+1] = "empty"
        /\ rochas' = [rochas EXCEPT ![s+1] = rochas[s], ![s] = "empty"]

    \/  /\ s > 0
        /\ rochas[s-1] = "empty"
        /\ rochas' = [rochas EXCEPT ![s-1] = rochas[s], ![s] = "empty"]
    


Jump(s) ==
    \/  
        /\ s < N-1
        /\ rochas[s+1] # rochas[s]
        /\ rochas[s+2] = "empty"
        /\ rochas' = [rochas EXCEPT ![s+2] = rochas[s], ![s] = "empty"]
    \/  
        /\ s > 1
        /\ rochas[s-1] # rochas[s]
        /\ rochas[s-2] = "empty"
        /\ rochas' = [rochas EXCEPT ![s-2] = rochas[s], ![s] = "empty"]



Next == \E s \in 0..N : Move(s) \/ Jump(s)
    
Objetivo == ~
    /\ \A s \in 0..(N \div 2)-1 : rochas[s] = "cor2"
    /\ \A s \in (N \div 2)+1..N : rochas[s] = "cor1"
    /\ rochas[(N \div 2)] = "empty"

=========================================================================