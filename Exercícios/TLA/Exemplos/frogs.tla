------------------------------- MODULE frogs -------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N % 2 = 0

VARIABLES rocks

TypeOK == rocks \in [ 0..N -> { "brown", "green", "empty" } ]

Init == rocks = [ p \in 0..N |-> IF p < N \div 2 
                                 THEN "green"
                                 ELSE IF p = (N \div 2)
                                      THEN "empty"
                                      ELSE "brown" ]
                                
NextGreen(r) == /\ rocks[r] = "green"
                /\ \/ /\ r < N
                      /\ rocks[r+1] = "empty"
                      /\ rocks' = [ rocks EXCEPT ![r] = "empty", ![r+1] = "green" ]
                   \/ /\ r < N - 1
                      /\ rocks[r+1] = "brown" /\ rocks[r+2] = "empty"
                      /\ rocks' = [ rocks EXCEPT ![r] = "empty", ![r+2] = "green" ]
                      
NextBrown(r) == /\ rocks[r] = "brown"
                /\ \/ /\ r > 0
                      /\ rocks[r-1] = "empty"
                      /\ rocks' = [ rocks EXCEPT ![r] = "empty", ![r-1] = "brown" ]
                   \/ /\ r > 1
                      /\ rocks[r-1] = "green" /\ rocks[r-2] = "empty"
                      /\ rocks' = [ rocks EXCEPT ![r] = "empty", ![r-2] = "brown" ]
                      
Next == \E r \in 0..N : NextBrown(r) \/ NextGreen(r)

\* To find a solution to the problem, one must try to verify that ~Goal is an invariant (also, turn deadlock check off!)
\* The model-checker will return a counter-example, that corresponds to the puzzle's solution
Goal == /\ \A r \in 0..(N \div 2)-1 : rocks[r] = "brown"
        /\ \A r \in (N \div 2)+1..N : rocks[r] = "green"
        /\ rocks[N \div 2] = "empty"   

                                           




=============================================================================
\* Modification History
\* Last modified Tue May 17 15:21:12 WEST 2022 by mane
\* Created Fri May 13 10:15:03 WEST 2022 by mane
