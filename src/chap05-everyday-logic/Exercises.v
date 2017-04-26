Theorem conv_example : forall n : nat, 7 * 5 < n -> 6 * 6 <= n.
Proof.
  intros.
  assumption.
Qed.

Lemma L_35_36 : forall n : nat, 7 * 5 < n -> 6 * 6 <= n.
Proof.
  intro n.
  intro H; assumption.
Qed.

Print L_35_36.

Theorem imp_trans : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R H H0 p.
  apply H0; apply H; assumption.
Qed.

Print imp_trans.

Check (imp_trans _ _ _ (le_S 0 1) (le_S 0 2)).

Definition neutral_left (A : Set) (op : A -> A -> A) (e : A) : Prop :=
  forall x : A, op e x = x.

Require Import ZArith.

Theorem one_neutral_left : neutral_left Z Zmult 1%Z.
Proof.
  intro z. (* delta- and beta-reductions *)
Abort.

Theorem le_i_SSi : forall i : nat, i <= S (S i).
Proof.
  intro i.
  apply le_S. apply le_S. apply le_n.
Qed.

Theorem all_imp_dist :
  forall (A : Type) (P Q : A -> Prop),
    (forall x : A, P x -> Q x) -> (forall y : A, P y) -> forall z : A, Q z.
Proof.
  intros A P Q H H0 z.
  apply H; apply H0.
Qed.

Theorem le_mult_mult :
  forall a b c d : nat, a <= c -> b <= d -> a*b <= c * d.
Proof.
  intros a b c d H H0.
  apply le_trans with (m := c*b).
  - apply mult_le_compat_r; assumption.
  - apply mult_le_compat_l; assumption.
Qed.

Theorem le_mult_mult' :
  forall a b c d : nat, a <= c -> b <= d -> a*b <= c * d.
Proof.
  intros a b c d H H0.
  eapply le_trans.
  - eapply mult_le_compat_l. eexact H0.
  - apply mult_le_compat_r. assumption.
Qed. 

Theorem le_O_mult : forall n p : nat, 0*n <= 0*p.
Proof.
  intros n p. apply le_n.
Qed.

Lemma lt_8_9 : 8 < 9.
Proof.
  unfold lt. apply le_n.
Qed.

Search Zle.

SearchPattern (_ + _ <= _)%Z.
SearchPattern (?X1 * _ <= ?X1 * _)%Z.

Theorem lt_S : forall n p : nat, n < p -> n < S p.
Proof.
  intros n p H.
  unfold lt. apply le_S. trivial.
Qed.

Open Scope Z_scope.

Definition Zsquare_diff (x y : Z) := x*x - y*y.

Theorem unfold_example :
  forall x y : Z,
    x*x = y*y ->
    Zsquare_diff x y * Zsquare_diff (x+y)(x*y) = 0.
Proof.
  intros x y Heq.
  unfold Zsquare_diff at 1.
Abort.

Check conj.
Check and_ind.
Check False_ind.

Section ex_falso_quodlibet.
  Hypothesis ff : False.

  Lemma ex1 : 220 = 284.
  Proof.
    apply False_ind.
    exact ff.
  Qed.

  Lemma ex2 : 220 = 284.
  Proof.
    elim ff.
  Qed.

End ex_falso_quodlibet.
Print ex2.

Check False_rec.

Theorem absurd : forall P Q : Prop, P -> ~P -> Q.
Proof.
  intros P Q p H.
  elim H. assumption.
Qed.

Print absurd.

Theorem double_neg_i : forall P : Prop, P -> ~~P.
Proof.
  intros P p H.
  apply H. assumption.
Qed.

Theorem modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  intros P Q p H.
  apply H; assumption.
Qed.

Theorem double_neg_i' : forall P : Prop, P -> ~~P.
Proof.
  intro P.
  unfold not. apply modus_ponens.
Qed.

Theorem contrap : forall A B : Prop, (A -> B) -> ~B -> ~A.
Proof.
  intros A B.
  unfold not. apply imp_trans.
Qed.

(* Exercise: 5.3 *)

Theorem not_false : ~False.
Proof.
  unfold not.
  intros H. elim H.
Qed.

Theorem triple_not : forall P : Prop, ~~~P -> ~P.
Proof.
  intros P.
  unfold not. intros H p.
  apply H. intros H'. apply H'. assumption.
Qed.

Theorem imp_contra : forall P Q R : Prop, (P -> Q) -> (P -> ~Q) -> P -> R.
Proof.
  intros P Q R H H' p.
  unfold not in H'. apply H' in H.
  - elim H.
  - apply p.
  - apply p.
Qed.

Theorem and_commutes : forall A B : Prop, A /\ B -> B /\ A.
Proof.
  intros A B H.
  elim H.
  split; assumption.
Qed.

Theorem or_commutes : forall A B : Prop, A \/ B -> B \/ A.
Proof.
  intros A B H.
  elim H.
  - right; assumption.
  - left; assumption.
Qed.

(* Exercise: 5.5 *)
Theorem or_one :
  forall (A : Set) (a b c d : A), a = c \/ b = c \/ c = c \/ d = c.
Proof.
  intros A a b c d.
  right. right. left. trivial.
Qed. 

(* Exercise: 5.6 *)
Theorem and_associative :
  forall A B C : Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  intros A B C H.
  elim H. intros a H'. split.
  - elim H'. intros b c. split.
    + assumption.
    + assumption.
  - apply H'.
Qed.

Theorem and_implies : forall A B C D : Prop,
  (A -> B) /\ (C -> D) /\ A /\ C -> B /\ D.
Proof.
  intros A B C D H.
  elim H. intros H0 H1.
  elim H1. intros H2 H3.
  elim H3. intros a c.
  split.
  - apply H0; assumption.
  - apply H2; assumption.
Qed.

Theorem not_contra : forall A : Prop, ~(A /\ ~A).
Proof.
  intros A H.
  elim H. intros a H'. apply H'. assumption.
Qed.

Theorem or_associative : forall A B C : Prop,
  A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A B C H. elim H.
  - intros a. left; left; assumption.
  - intros H'. elim H'.
    + intros b. left; right; assumption.
    + intros c. right; assumption.
Qed.

Theorem double_neg_or : forall A : Prop, ~~(A \/ ~A).
Proof.
  intros A H. unfold not in H.
  apply H. right. intro a.
  apply H. left; assumption.
Qed.

Theorem or_neg_implies : forall A B : Prop, (A \/ B) /\ ~A -> B.
Proof.
  intros A B H.
  elim H. intro H1. elim H1.
  - intros a contra. apply contra in a. elim a.
  - intros b H2. assumption.
Qed.

Theorem ex_imp_ex :
  forall (A : Type) (P Q : A -> Prop), (ex P) ->
  (forall x : A, P x -> Q x) -> (ex Q).
Proof.
  intros A P Q H H0.
  elim H. intros a Ha.
  exists a. apply H0. exact Ha.
Qed.

(* Exercise: 5.9 *)
Theorem exists_or : forall (A : Set) (P Q : A -> Prop),
  (exists x : A, P x \/ Q x) -> (ex P) \/ (ex Q).
Proof.
  intros A P Q H.
  elim H. intros a Hor. elim Hor.
  - intros HPa. left. exists a. exact HPa.
  - intros HQa. right. exists a. exact HQa.
Qed.

Theorem exists_or_converse : forall (A : Set) (P Q : A -> Prop),
  (ex P) \/ (ex Q) -> exists x : A, P x \/ Q x.
Proof.
  intros A P Q H.
  elim H.
  - intros HPx.  elim HPx. intros a H'.
    exists a. left; assumption.
  - intros HQy. elim HQy. intros a H'.
    exists a. right; assumption.
Qed.

Theorem forall_contradiction : forall (A : Set) (R : A -> Prop),
  (exists x : A, (forall R : A -> Prop, R x)) -> 2 = 3.
Proof.
  intros A R H.
  elim H. intros a H'. apply H' with (R := fun (x : A) => 2 = 3).
Qed.

Theorem forall_implies_negation : forall (A : Set) (P : A -> Prop),
  (forall x : A, P x) -> ~(exists y : A, ~ (P y)).
Proof.
  intros A P H.
  unfold not. intro H'.
  elim H'. intros a H''.
  apply H''. apply H.
Qed.
(* End of Exercise 5.9 *)

Lemma L36 : 6*6 = 9*4.
Proof. reflexivity. Qed.
Print L36.

Theorem diff_of_squares : forall (a b : Z), (a+b)*(a-b) = a*a - b*b.
Proof.
  intros.
  Require Import ZArithRing.
  ring.
Qed.

Theorem eq_sym' : forall (A : Type) (a b : A), a = b -> b = a.
Proof.
  intros A a b eq.
  rewrite eq. reflexivity.
Qed.

Theorem Zmult_distr_1 : forall n x : Z, n*x + x = (n+1)*x.
Proof.
  intros.
  rewrite Zmult_plus_distr_l.
  rewrite Zmult_1_l.
  trivial.
Qed.

Theorem regroup : forall x : Z, x + x + x + x + x = 5*x.
Proof.
  intro x. pattern x at 1.
  rewrite <- Zmult_1_l.
  repeat rewrite Zmult_distr_1.
  auto with zarith.
Qed.

Open Scope nat_scope.

(* Exercise: 5.10 *)
Theorem plus_permute2 :
  forall n m p : nat, n + m + p = n + p + m.
Proof.
  intros n m p.
  rewrite <- plus_assoc.
  pattern (m + p) at 1.
  rewrite plus_comm. rewrite plus_assoc. reflexivity.
Qed.
(* End of Exercise 5.10 *)


(* Conditional Rewriting *)

(* Exercise 5.11 *)
Theorem eq_trans' : forall (A : Type) (x y z : A),
  x = y -> y = z -> x = z.
Proof.
  intros A x y z H H'.
  rewrite H; assumption.
Qed.
(* End of Exercise 5.11 *)


(* Searching Theorems for Rewriting *)
SearchRewrite (1 * _)%Z.


(*** Impredicative Definitions *)

Definition my_True : Prop :=
  forall P : Prop, P -> P.

Definition my_False : Prop :=
  forall P : Prop, P.

Theorem my_I : my_True.
Proof.
  intros P p; assumption.
Qed.

Theorem my_False_ind : forall P : Prop, my_False -> P.
Proof.
  intros P F. unfold my_False in F.
  apply F.
Qed.
