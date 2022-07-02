Set Implicit Arguments.


Require Import List.
Require Import ZArith.
Require Import Lia.



Section Parte1.
(* ================================================================== *)
(* Prove os lemas desta secção SEM usar táticas automáticas.          *)
  
Variables A B C : Prop.
Variable X : Set.
Variables P Q R: X -> Prop.


Lemma questao1 : (A->C) /\ (B->C) -> (A/\B)->C.
Proof.
  intros.
  destruct H.
  apply H. apply H0.
Qed.



Lemma questao2 : ~A \/ ~B -> ~(A /\ B).
Proof.
  unfold not.
  intros.
  destruct H; apply H; apply H0.
Qed.



Lemma questao3 : (forall x:X, (P x) -> ~(Q x)) -> ~(exists y:X, (P y) /\ (Q y)).
Proof.
  intros.
  unfold not.
  intro.
  destruct H0.
  destruct H with x; apply H0.
Qed.


Lemma questao4 : (forall x:X, (P x)\/(Q x)) -> (exists y:X, ~(Q y)) -> (forall x:X, (R x) -> ~(P x)) -> (exists x:X, ~(R x)).
Proof.
  intros.
  destruct H0.
  exists x.
  unfold not.
  intro.
  destruct H with x.
  apply H1 in H3.
  - apply H3.
  - apply H2.
  - contradiction.
Qed.



Lemma questao5 : forall (x y:nat), x+2 = y -> y>x.
Proof.
  intros.
  destruct H.
  rewrite plus_n_O.
  apply plus_gt_compat_l.
  constructor.
  reflexivity.
Qed.


End Parte1.


Open Scope Z_scope.



Section Parte2.
(* ================================================================== *)
(* Prove os lemas desta secção. Pode usar táticas automáticas.        *)


Inductive In (A:Type) (y:A) : list A -> Prop :=
| InHead : forall (xs:list A), In y (cons y xs)
| InTail : forall (x:A) (xs:list A), In y xs -> In y (cons x xs).


Inductive Suffix (A:Type) : list A -> list A -> Prop :=
| Suff0 : forall (l:list A), Suffix nil l
| Suff1 : forall (x:A) (l1 l2:list A), Suffix l1 l2 -> Suffix (l1) (x::l2)
| Suff2 : forall (x:A) (l1 l2:list A), Suffix l1 l2 -> Suffix (x::l1) (x::l2).


Inductive Maiores (x:Z) : list Z -> Prop :=
| Maior_nil : Maiores x nil
| Maior_cons : forall (l:list Z) (y:Z),  Maiores x l -> y > x -> Maiores x (y::l).



Fixpoint drop (A:Type)(n:nat) (l:list A) : list A :=
  match n with
  | O => l
  | S x => match l with
           | nil => nil
           | y::ys => drop x ys
           end
  end.



Lemma questao6 : forall (A:Type) (l:list A),  drop (length l) l = nil.
Proof.
  intros.
  induction l.
  constructor.
  auto.
Qed.




Lemma questao7 : forall (A: Type) (x: A) (l: list A),
         In x l ->  exists l1: list A, exists l2: list A, l = l1 ++ (x :: l2).
Proof.
  intros.
  induction l.
  - 

Admitted.



Lemma questao8 : forall (x y:Z) (l:list Z),  Maiores x l /\ In y l -> y > x.
Proof.
  intros.
  destruct H.

Admitted.


Lemma questao9 : forall (A:Type) (l1 l2 l3:list A),
                      Suffix l1 l2 -> Suffix (l1++l3) (l2++l3).
Proof.
  intros.
  induction l1.
  - simpl. induction l3.
    + Search ( _ ++ nil). rewrite app_nil_r. apply H.
    + 

Admitted.




End Parte2.




Section Parte3.
(* ================================================================== *)
(* Considere as funções abaixo definidas e prove o teorema.           *)
(* Pode usar táticas automáticas.                                     *)
(* Se precisar de definir lemas auxiliares, deverá também prova-los.  *)


Fixpoint ocurr (a:Z) (l: list (Z*nat)) : nat :=
  match l with
  | nil => 0 
  | ((x,n)::xs) => if (Z.eq_dec a x) then n else ocurr a xs
  end.


Fixpoint addn (a:Z) (n:nat) (l: list (Z*nat)) : list (Z*nat) :=
  match l with
  | nil => (a,n)::nil
  | ((x,n1)::xs) => if (Z.eq_dec a x) then  ((x,(n+n1)%nat)::xs) else (x,n1) :: addn a n xs
  end.                                                         


Theorem questao10 : forall x n l, (ocurr x (addn x n l)) = (n + (ocurr x l))%nat.
Proof.
  intros.
  rewrite (addn x n l).
Admitted.


End Parte3.
