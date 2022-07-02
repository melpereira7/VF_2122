# Algoritmo de exclusão mútua

Garante que:

+ numa secção crítica do código está, no máximo, um processo ao mesmo tempo
+ *no starvation* ou *lockout freedom*, i.e., todos os processos que estejam à espera para entrar na secção crítica irá eventualmente entrar na zona
+ *bounded waiting*, i.e., nenhum processo pode entrar na secção crítica mais de k vezes enquanto outros estão à espera

&rarr; Outros algoritmos: Semáforo; Peterson.


# Algortimo de Leader Election

Garante que:

+ no máximo um líder será eleito
+ pelo menos um líder será eleio
+ qualquer líder eleito, mantém-se eleito

&rarr; Chang and Roberts


# Algoritmo de Self Stabilisation (sistemas distribuídos)

Garante:

+ convergência: começando em qualquer estado, o sistema irá eventualmente a um estado correto
+ *closure*: se o sistema está num estado correto, mantém-se num estado correto

&rarr; Dijkstra


# Model checking

Automatiza o processo de verificação e não há neccessidade de encontrar invariantes complexos, mas... 

+ o sistema deve ser descrito com um modelo de estados finito
+ as propriedades desejadas devem ser especificadas usando lógica temporal

Se a propriedade não se verificar, é retornado um contra-exemplo.


# Estruturas de Kripke

Uma estrutura $M$ Kripke é um tuplo $(S,I,R,L)$ em que:

+ $S$ é um conjunto finito de estados
+ $I \subseteq S$ é o conjunto de estados iniciais
+ $R \subseteq S \times S$ é a relação de transições total (todo estado tem pelo menos um sucessor)
+ $L : S \rarr 2^A$ é uma função de etiquetagem, que mapeia cada estado $s \in S$ ao conjunto de proposições atómicas em $s$
+ um caminho (ou traço) $\pi$ numa estrutura $M = (S,I,R,L)$ é uma sequência infinita de estados $s_0s_1s_2...$ tais que $\forall_{i \geq 0 \cdot} (s_i,s_{i+1}) \in R$
+ $\pi_i$ é o estado $i$ do traço $\pi$ e $\pi^i$ é o caminho sufixo que começa nesse estado


# Modelos de tempo

Dois modelos básicos de tempo na lógica temporal:

+ Tempo linear: o comportamento do sistema é o conjunto de todos os caminhos infinitos que começam no estado inicial
+ Branching time: o comportamento do sistema é o conjunto de todas as árvores de computação que desenrolam dos estados iniciais
  
Os dois podem ser determinados por uma estrutura de Kripke


# Lógica Temporal Linear (LTL)

+ LTL é um lógica temporal com um modelo de tempo linear
+ Todas as fórmulas são avaliadas em caminhos infinitos
+ Dado um conjunto $A$ de proposições atómicas, a sintaxe de fórmulas LTL é dada pelas seguintes regras:
  + se $p \in A$ então $p$ é uma fórmula LTL atómica
  + se $f$ e $g$ são fórmulas LTL, então as seguintes são também fórmulas LTL:
    + $\top$
    + $\bot$
    + $\neg f$
    + $f \vee g$
    + $f \wedge g$
    + $f \rightarrow g$
    + **X** $f$
    + **F** $f$
    + **G** $f$
    + $f$ **U** $g$
    + $g$ **R** $f$
  
## Operadores Temporais LTL

|                               |                        |                                                       |
| :---------------------------: | :--------------------: | :---------------------------------------------------: |
|   **X** $f ~~~~ \bigcirc f$   |    **neXt, after**     |          $f$ será verdade no próximo estado           |
|   **G** $f ~~~~ \square f$    |  **Globaly, always**   |                $f$ será sempre verdade                |
| **F** $f ~~~~ \diamondsuit f$ | **Future, eventually** |            $f$ será eventualmente verdade             |
|         $f$ **U** $g$         |       **Until**        |        $g$ será verdade e $f$ é verdade até lá        |
|         $g$ **R** $f$         |      **Release**       | $f$ só pode ser falso depois de $g$ se tornar verdade |

## Semântica LTL

Dada uma estrutura Kripke $M$, dizemos que $f$ é validado em $M$ da seguinte forma: 

> $M \models f ~~~~ \Leftrightarrow ~~~~\forall_{\pi \in M \cdot} \pi_0 \in I \rightarrow M, \pi \models f$

<img src="LTL Semantics.JPG" width=70%>

## Minimal LTL Operators

Todas as fórmulas LTL podem ser expressas com $\top, \neg, \wedge$, **X** e **U**.

<img src="Minimal LTL Operators.JPG" width=40%>

### Exemplos LTL

+ Exclusão mútua
    > **G** $\neg(c_0 \wedge c_1)$
+ Lockout freedom
    > **G** $(w_0 \rightarrow$ **F** $c_0) \wedge$ **G** $(w_1 \rightarrow$ **F** $c_1)$

# Especificar o comportamento com LTL' (*prime*)

Para um variável booleana, define-se $b' = a$ como abreviação de **X**$b \leftrightarrow a$.

O operador *prime* pode ser usado em variáveis para referir o valor da variável no estado seguinte.

Assim, os comportamentos válidos podem ser especificados com a fórmula $init ~ \vee$ **G** $trans$, em que:

+ $init$ é uma fórmula proposicionl que especifica os estados iniciais válidos
+ $trans$ é uma fórmula proposicional (com *primes*) que especifica as transições válidas
  
Então, em vez de verificar $f$, verifica-se $init ~ \vee$ **G** $trans \rightarrow f$.


# Passado no LTL

|               |                       |                                                           |
| :-----------: | :-------------------: | :-------------------------------------------------------: |
|   **Y** $f$   | **Yesterday, before** |            $f$ foi verdade no estado anterior             |
|   **H** $f$   |   **Historically**    |                  $f$ foi sempre verdade                   |
|   **O** $f$   |       **Once**        |                $f$ foi verdade alguma vez                 |
| $f$ **S** $g$ |       **Since**       |     $g$ foi verdade alguma vez $f$ é verdade desde aí     |
| $g$ **T** $f$ |      **Release**      | $f$ só pôde ser falso antes de $g$ se ter tornado verdade |


# Lógica Temporal de Ações (TLA)

+ Restringe LTL' para garantir que as fórmulas são *stutter invariant*
+ Adiciona quantificadores de 1ª ordem ao LTL'
+ A sintaxe das fórmulas TLA é dada pelas seguintes regras:
  + qualquer predicado de estado $p$ (sem *primes*) é uma fórmula TLA atómica
  + se $a$ é um predicado de ação (com *primes*), então $\square [a]_t$ e **ENABLED** $a$ são fórmulas atómicas TLA, sendo que $[a]_t \equiv a \vee (t' = t)$
  + se $f$ e $g$ são fórmulas TLA e S é um conjunto, então as seguintes são também fórmulas TLA:
    + TRUE
    + FALSE
    + $\neg f$
    + $f \vee g$
    + $f \wedge g$
    + $f \rightarrow g$
    + $\forall x \in S : f$
    + $\exist x \in S : f$
    + $\square f$
    + $\diamondsuit f$
+ TLA+ é a linguagem de especificação concreta e completa baseada em TLA

## Validação com TLA+

+ Para encontrar cenários em que $f$ é verdadeiro, verificar $\neg f$
+ Em particular, para ver um cenário em que a ação $a$ acontece, verificar $\square [\neg a]_t$
+ É também comum incluir um invariante para verificar a correção de tipos:
<img src="Types Invariant TLA.JPG" width=60%>


# Lógica de Computação em Árvore (CTL)

+ CTL é uma lógica temporal com modelo de tempo em *branches*
+ Além de operadores temporais, também tem quantificadores de caminho, que constroem fórmulas de estado atrvés de fórmulas de caminho
+ Dado um conjunto $A$ de proposições atómicas, a sintaxe de fórmulas CTL é dada pelas seguintes regras:
  + se $p \in A$ então $p$ é uma fórmula de estado CTL
  + se $f$ e $g$ são fórmulas de estado CTL, então as seguintes são também fórmulas de estado CTL:
    + $\top$
    + $\bot$
    + $\neg f$
    + $f \vee g$
    + $f \wedge g$
    + $f \rightarrow g$
  + se $f$ é uma fórmula de caminho CTL, então **A**$f$ e **E**$f$ são fórmulas de estado CTL
  + se $f$ e $g$ são fórmulas de estado CTL,então as seguintes são fórmulas de caminho CTL:
    + **X** $f$
    + **F** $f$
    + **G** $f$
    + $f$ **U** $g$
    + $g$ **R** $f$

## Semântica CTL

Dada uma estrutura Kripke $M$, dizemos que $f$ é validado em $M$ da seguinte forma: 

> $M \models f ~~~~ \Leftrightarrow ~~~~\forall_{s \in I \cdot} M,s \models f$

<img src="CTL Semantics.JPG" width=70%>

## Minimal CTL Operators

Todas as fórmulas LTL podem ser expressas com $\top, \neg, \vee$, **X**, **EX**, **EG** e **EU**.

<img src="Minimal CTL Operators.JPG" width=40%>

## Exemplos CTL

+ Exclusão mútua:
    > **AG** $\neg (c_0 \wedge c_1)$
+ Lockout freedom:
    > **AG** $(w_0 \rightarrow$ **AF** $c_0) ~\wedge~$ **AG** $(w_1 \rightarrow$ **AF** $c_1)$
+ Reversibilidade:
    > **AG EF** $(i_0 \wedge i_1)$


# LTL vs CTL

+ A maioria das propriedades podem ser expressas tanto em CTL como em LTL, mas a sua expressividade não é comparável!
+ Em geral, fórmulas LTL não são equivalentes a fórmulas CTL obtidas adicionando **A** antes de cada operador temporal. Por exemplo, **AF AX** $p$ não é o mesmo que **F X** $p$.


# Saftey, Liveness e Fairness

+ Propriedades de **safety**
  + Nada de "mal" irá acontecer
  + Exclusão mútua é uma propriedade de safety
+ Propriedades de **liveness**
  + Algo "bom" irá acontecer
  + Lockout freedom é uma propriedade de liveness
+ Assunções de **fairness** (justiça) 
  + São necessárias para verificar propriedades de liveness
  + É uma propriedade de liveness que força o sistema a continuar a fazer algo em determinadas condições
    + ***unconditional fairness***: determinada ação irá ocorrer recorrentemente  
        > **G F** $action$
    + ***strong fairness***: determinada ação que é recorrentemente ativada, vai ocorrer (recorrentemente)
        > **G F** $enabled \rightarrow$ **G F** $action$
    + ***weak fairness***: determinada ação que é continuamente ativada, vai ocorrer (recorrentemente)
        > **F G** $enabled \rightarrow$ **G F** $action$


# Fairness no TLA

Se $a$ é um predicado de ação, então **WF**$_t(a)$ e **SF**$_t(a)$ são fórmulas atómicas TLA.

Em TLA+:

<img src="Fairness in TLA.JPG" width=80%>


# CTL Model Checking

Dada uma estrutura de Kripke $M = (S,I,R,L)$ e uma fórmula CTL $f$, o objetivo de um *model checker* é encontrar um conjunto de estados que satisfazem $f$

> $\llbracket f \rrbracket _M \equiv \lbrace s \in M | M,s \models f \rbrace$


# Model Checking Explícito vs Simbólico

Explícito

+ Conjuntos e transições são codificados por extensão
+ A semântica de operadores temporais é implementada por travessias de grafos

    > $M \models f ~~$ iff $~~ I \subseteq \llbracket f \rrbracket _M$

Simbólico

+ Conjuntos e transições são codificados intencionalmene por fórmulas proposicionais
+ A semântica dos operadores temporais é implementada por computações de ponto fixo

    > $M \models f ~~$ iff $~~ I \rightarrow \llbracket f \rrbracket _M$


# CTL Model Checking Explícito

## Componente fortemente conectado (SCC)

+ Um componente fortemente conectado é um subgrafo maximal onde todos os nodos são alcançavéis a partir de todos os outros.
+ Um SCC é *não trivial* de tem pelo menos um caminho (mais que um nodo, ou um nodo com lacete)

## Fairness em CTL

+ A fairness não pode ser expressa em CTL, por isso, a semântica e model checking deve ser adaptado para considerar fairness
+ $M \models \lbrack f \rbrack _p ~~$ iff $~~ M \models f$ e $p$ é recorrentemente verdade em $M$ (*unconditional fairness*)

(para tentar entender:)
<img src="Fairness in CTL.JPG">


# CTL Model Checking Simbólico

<img src="CTL Simbolico.JPG" width=40%>

$\llbracket f \rrbracket'$ é a fórmula obtida a partir de $\llbracket f \rrbracket$ substituindo todas as variáveis pela respetiva versão *primed*

+ O quantificador existencial pode ser eliminado por expansão:

    > $\exist_{x \cdot} f \equiv f\lbrack x \leftarrow \top \rbrack \vee f \lbrack x \leftarrow \bot \rbrack$

+ Necessita de procedimentos para verificar a validade e equivalência de fórmulas proposicionais
+ Pode ser implementado eficientemente com *Diagramas de Decisão Binários Ordenados*


# LTL Model Checking Explícito

Dada uma estruture de Kripke $M = (S,I,R,L)$ e considerando $S$ como um alfabeto, denota-se por $L(M)$ a linguagem de $M$ que é o conjunto de todos os caminhos que começam num estado inicial

> $L(M) = \lbrace \pi ~|~ \pi \in M \wedge \pi_0 \in I \rbrace$

A linguagem de uma fórmula LTL $f$ é denotada por $L(f)$ e é o conjunto de todos os possíveis caminhos que satisfazem $f$

> $L(f) = \lbrace \pi ~|~ \pi \models f \rbrace$

Uma fórmula é válida se e só se a linguagem do modelo é um subset da linguagem da fórmula

> $M \models f~~$ iff $~~ L(M) \subseteq L(f)~~$ iff $~~ L(M) \cap L(\neg f) = \emptyset$