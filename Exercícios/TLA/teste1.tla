-------------------------------- MODULE teste1 --------------------------------
EXTENDS Naturals

CONSTANT N

VARIABLES flag, pc

vars == <<flag, pc>>

Proc == 1..N

TypesOK ==
    /\ pc \in [ Proc -> {"idle","wait0","wait1","wait2","check","critical"}]
    /\ flag \in [ Proc -> {0,1,2,3,4}] 


(********** a **********)    
Init ==
    /\ pc = [ i \in Proc |-> "idle"]
    /\ flag = [ i \in Proc |-> 0] 


idle(p) ==
    /\ pc[p] = "idle"
    /\ flag' = [flag EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = "wait0"]

wait0(p) ==
    /\ pc[p] = "wait0"
    /\ \A k \in Proc : flag[k] \in 0..2
    /\ flag' = [flag EXCEPT ![p] = 3]
    /\ pc' = [pc EXCEPT ![p] = "check"]

check(p) ==
    /\ pc[p] = "check"
    /\  \/
            /\ \E k \in Proc : flag[k] \in {1}
            /\ flag' = [flag EXCEPT ![p] = 2]
            /\ pc' = [pc EXCEPT ![p] = "wait1"]
        \/
            /\ flag' = [flag EXCEPT ![p] = 4]
            /\ pc' = [pc EXCEPT ![p] = "wait2"]

wait1(p) ==
    /\ pc[p] = "wait1"
    /\ \E k \in Proc : flag[k] \in {4}
    /\ flag' = [flag EXCEPT ![p] = 4]
    /\ pc' = [pc EXCEPT ![p] = "wait2"]

wait2(p) ==
    /\ pc[p] = "wait2"
    /\ \A k \in 1..(p-1) : flag[k] \in {0,1}
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED flag

critical(p) ==
    /\ pc[p] = "critical"
    /\ \A k \in (p+1)..N : flag[k] \in {0,1,4}
    /\ flag' = [flag EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "idle"]






Next == \E p \in Proc : idle(p) \/ wait0(p) \/ check(p) \/ wait1(p) \/ wait2(p) \/ critical(p)    

execute(p) == idle(p) \/ wait0(p) \/ check(p) \/ wait1(p) \/ wait2(p) \/ critical(p)

Spec == Init /\ [][Next]_<<pc, flag>>


(********** b
São necessários 6 valores: {"idle","wait0","wait1","wait2","check","critical"} para a variável de controlo.
Essa variável, aqui, é a pc, definida no início da especificação.
Estes valores servem para determinar em que estado é que o processo se encontra, sendo que os estados 
existentes são 6, então são necessários 6 valores diferentes para essa variável de controlo. *)


(********** c **********)
MutualExclusion == [] ~(\E i \in Proc: \E j \in Proc: i#j /\ pc[i] = "critical" /\ pc[j] = "critical")


(********** d **********)
Fairness == \A p \in Proc : WF_vars(execute(p))

LockoutFreedom == Fairness => \A p \in Proc : [] ((pc[p] = "wait0" \/ pc[p] = "wait1" \/ pc[p] = "wait2") => <> (pc[p] = "critical"))

(********** e
Para obter um exemplo de execução basta escrever uma propriedade que represente a entrada recorrente de todos
os N processos na região crítica e tentar provar a sua negação, se a propriedade se verificar, a sua negação
lançará um erro e o trace onde tal propriedade se verifica é mostrado *)
Goal == ~ (\A p \in Proc: <> (pc[p] = "critical"))


(********** g 
A propriedade referida em f é uma propriedade de safety pois garante que algo "mau", neste caso, 
um processo entrar na região crítica duas vezes seguidas enquanto outro está à espera, nunca irá acontecer. *)



==============================================================================