Section ExsPL.
Variables (A:Prop) (B:Prop) (C:Prop).

Lemma ex21 : (A \/ B) \/ C -> A \/ (B \/ C).
Proof.
    intros.
    destruct H.
    destruct H.
    - left. apply H.
    - right. left. apply H.
    - right. right. apply H.
Qed.  


Lemma ex22 : (B -> C) -> A \/ B -> A \/ C.
Proof.
    intros.
    destruct H0.
    - left. apply H0.
    - right. apply H. apply H0.
Qed.


Lemma ex23 : (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
    intros.
    destruct H.
    destruct H.
    - split. 
        + apply H.
        + split.
            * apply H1.
            * apply H0.
Qed.


Lemma ex24 : A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
    intros.
    split.
    destruct H.
    - left. apply H.
    - right. apply H.
    - destruct H.
        + left. apply H.
        + right. apply H.
Qed.


Lemma ex25 : (A /\ B) \/ (A /\ C) <-> A /\ (B \/ C).
Proof.
    red.
    split.
    - intros.
        split.
        destruct H.
        destruct H.
        + apply H.
        + destruct H. apply H.
        + destruct H as [h1 | h2].
            * left. apply h1.
            * right. apply h2.  
    - intros.
        destruct H.
        destruct H0.
        + left. split.
            * apply H.
            * apply H0.
        + right. split.
            * apply H.
            * apply H0.
Qed.


Lemma ex26 : (A \/ B) /\ (A \/ C) <-> A \/ (B /\ C).
Proof.
    red.
    split.
    - intros.
        tauto.
    - intros.
        split.
        destruct H.
        + left. apply H.
        + right. apply H.
        + destruct H.
            * left. apply H.
            * right. apply H.
Qed.

End ExsPL.


Section ExsFOL.

Variables X Y :Set.
Variables P Q R : X -> Prop.
Variable P1 : X -> X -> Prop.


Lemma ex31 : (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
    intros.
    destruct H.
    destruct H.
    split.
    - exists x. apply H.
    - exists x. apply H0.
Qed.


Lemma ex32 : (exists x, forall y, P1 x y) -> (forall y, exists x,  P1 x y).
Proof.
    intros.
    destruct H.
    exists x.
    apply H.
Qed.

Lemma ex33 : (exists x, P x) -> (forall x, forall y, P x -> Q y) -> (forall y, Q y).
Proof.
    intros.
    destruct H.
    apply H0 with x.
    apply H.
Qed.

Lemma ex34 : (forall x, Q x -> R x) -> (exists x, P x /\ Q x) -> (exists x, P x /\ R x).
Proof.
    intros.
    destruct H0.
    destruct H0.
    exists x.
    split.
    - apply H0. 
    - apply H. apply H1.
Qed.

Lemma ex35 : (forall x, P x -> Q x) -> (exists x, P x) -> exists y, Q y.
Proof.
    intros.
    destruct H0.
    exists x.
    apply H.
    apply H0.
Qed.


Lemma ex36 : (exists x, P x) \/ (exists x, Q x) <-> (exists x, P x \/ Q x).
Proof.
    red.
    split.
    - intros.
        destruct H.
        + destruct H.
            exists x.
            left. apply H.
        + destruct H.
            exists x.
            right. apply H. 
    - intros.
        destruct H.
        destruct H.
        + left. 
            exists x. 
            apply H.
        + right.
            exists x.
            apply H.
Qed.

End ExsFOL.


Section ExsCL.

Variables (A:Prop) (B:Prop).
Variable X :Set.
Variable P : X -> Prop.

Axiom EML : forall A:Prop, A \/ ~ A.

Lemma ex41 : ((A -> B) -> A) -> A.
Proof.
    intros.
    destruct EML with A as [Ax1 | Ax2].
    - assumption.
    - apply H.
        intros.
        contradiction. 
Qed.

Lemma ex42 : ~ ~ A -> A.
Proof.
    intros.
    destruct EML with A as [Ax1 | Ax2].
    - assumption.
    - contradiction.
Qed.

Lemma ex43 : (~ forall x, P x) -> exists x, ~ P x.
Proof.
    destruct EML with (exists x: X, ~P x).
    - intros. assumption.
    - intros. elim H0. intros.
        destruct EML with (P x).
        + assumption.
        + unfold not in H. 
            unfold not in H0. 
            elim H.
            unfold not in H1.
            exists x.
            assumption.
Qed.