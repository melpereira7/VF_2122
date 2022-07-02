-------------------------------- MODULE teste2 --------------------------------
EXTENDS Integers

CONSTANT N, V

VARIABLES array, first, whereToSend

vars == <<array, first, whereToSend>>

Ind == 0..(N-1)
Val == 0..(V-1)

TypesOK ==
    /\ array \in [ Ind -> -1..(V-1)]
    /\ first \in {0..(N-1)}
    /\ whereToSend \in {0..(N-1)}


(********** a **********)  
Init ==
    /\ array = [i \in Ind |-> -1]
    /\ first = 0
    /\ whereToSend = 0


send(v) ==
    /\ \E i \in Ind : array[i] = -1
    /\ array' = [array EXCEPT ![whereToSend] = v]
    /\ IF whereToSend \in {N-1} THEN whereToSend' = 0
                                ELSE whereToSend' = whereToSend+1
    /\ UNCHANGED first



read ==
    /\ \E i \in Ind : array[i] # -1
    /\ array' = [array EXCEPT ![first] = -1]
    /\ IF first \in {N-1} THEN first' = 0
                                ELSE first' = first+1
    /\ UNCHANGED whereToSend
   



Next == \E v \in Val : send(v) \/ read

(********** b
no meu caso, -1 é um valor válido, pois é o valor que defini para determinar que um indice do array está 
"vazio" para escrita *)  
InvalidVal == \A i \in Ind: [] (array[i] \in -1..(V-1))

(********** c **********)
c == ~
    [] ((\A i \in Ind: array[i] # -1) => <> (\A i \in Ind: array[i] = -1))


==============================================================================