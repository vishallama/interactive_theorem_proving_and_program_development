(* Tactics for Inductive Types *)


(* Conversions *)

Theorem simpl_pattern_example : 3*3 + 3*3 = 18.
Proof.
  simpl (3*3) at 2.
  Show 1.
  lazy beta iota zeta delta [mult].
Abort.

Theorem lazy_example : forall n : nat, (S n) + O = S n.
Proof.
  intro n; lazy beta iota zeta delta.
  fold plus.
  rewrite <- plus_n_O. trivial.
Qed.

(* Tactics auto and eauto *)

Theorem SSSn_le_SSSm :
  forall n m : nat, S (S (S n)) <= S (S (S m)) -> n <= m.
Proof.
  Hint Resolve le_S_n : le_base.
  auto with le_base.
Qed.


(* Automatic Tactics for Rewriting *)

(* The autorewrite Tactic *)
Section combinatory_logic.

Variables (CL : Set) (App : CL -> CL -> CL) (S : CL) (K : CL).

Hypotheses
  (S_rule :
    forall A B C : CL, App (App (App S A) B) C = App (App A C) (App B C))
  (K_rule :
    forall A B : CL, App (App K A) B = A).

Hint Rewrite S_rule K_rule : CL_rules.

Theorem obtain_I : forall A : CL, App (App (App S K) K) A = A.
Proof.
  intros.
  autorewrite with CL_rules.
  trivial.
Qed.

End combinatory_logic.

Require Import Coq.Arith.Arith.

(* The subst Tactic *)
Theorem example_for_subst :
  forall (a b c d : nat), a = b + c -> c = 1 -> a + b = d -> 2*a = d + c.
Proof.
  intros a b c d H H1 H2.
  subst a. subst. simpl.
  rewrite <- plus_n_O.
  rewrite plus_assoc. reflexivity.
Qed.

(* The ring Tactic *)
Require Import ZArith.
Require Import NArith.
Open Scope Z_scope.

Theorem ring_example1 : forall x y : Z, (x+y)*(x+y) = x*x + 2*x*y + y*y.
Proof.
  intros; ring.
Qed.

Definition square (z : Z) := z*z.

Theorem ring_example2 :
  forall x y : Z, square (x+y) = square x + 2*x*y + square y.
Proof.
  intros; unfold square; ring.
Qed.

Theorem ring_example3 :
  (forall x y : nat, (x+y)*(x+y) = x*x + 2*x*y + y*y)%nat.
Proof.
  intros x y. ring.
Qed.

Theorem ring_example4 :
  (forall x : nat, (S x)*(x+1) = x*x + (x+x+1))%nat.
Proof.
  intro x. ring.
Qed.

(* The omega Tactic *)
Require Import Omega.

Theorem omega_example1 :
  forall x y z t : Z, x <= y <= z /\ z <= t <= x -> x = t.
Proof.
  intros; omega.
Qed.

Theorem omega_example2 :
  forall x y : Z,
    0 <= square x -> 3*(square x) <= 2*y -> square x <= y.
Proof.
  intros; omega.
Qed.

Theorem omega_example3 :
  forall x y : Z,
    0 <= x*x -> 3*(x*x) <= 2*y -> x*x <= y.
Proof.
  intros; omega.
Qed.

(* The field Tactic *)
Require Import Reals.

Open Scope R_scope.

Theorem example_for_field :
  forall x y : R, y <> 0 -> (x+y)/y = 1 + (x/y).
Proof.
  intros; field; trivial.
Qed.

(* The fourier Tactic: Provides the same functionality as the omega tactic,
   but for real numbers. The inequalities must be easily transformed into
   linear inequalities with rational coefficients.
 *)
Require Import Fourier.

Theorem example_for_Fourier :
  forall x y : R, x-y > 1 -> x - 2*y < 0 -> x > 1.
Proof.
  intros; fourier.
Qed.


(* Other Decision Procedures *)

(* Exanples of logical formulas solved by tauto but not by auto *)
Theorem A_and_B_implies_A : forall A B : Prop, A /\ B -> A.
Proof. tauto. Qed.

Theorem contradiction_implies_anything : forall A B : Prop, A /\ ~A -> B.
Proof. tauto. Qed.

(* intuition Tactic *)
Open Scope nat_scope.

Theorem example_intuition :
  (forall n p q : nat, n <= p \/ n <= q -> n <= p \/ n <= S q).
Proof.
  intros n p q. intuition auto with arith.
Qed.


(* ** The Tactic Definition Language: Ltac *)

Ltac autoClear h := try (clear h; auto with arith; fail).
Ltac autoAfter tac := try (tac; auto with arith; fail).

Open Scope nat_scope.

Ltac le_S_star := apply le_n || (apply le_S; le_S_star).

Theorem le_5_25: 5 <= 25.
Proof. le_S_star. Qed.


(* Pattern Matching *)

(* Pattern Matching in the Goal *)
Section primes.

Definition divides (n m : nat) := exists p : nat, p*n = m.

Hypotheses
  (divides_0 : forall n, divides n 0)
  (divides_plus : forall n m, divides n m -> divides n (n + m))
  (not_divides_plus : forall n m, ~ divides n m -> ~ divides n (n + m))
  (not_divides_lt : forall n m, 0 < m -> m < n -> ~ divides n m)
  (not_lt_2_divides : forall n m, n <> 1 -> n < 2 -> 0 < m -> ~ divides n m)
  (le_plus_minus : forall n m, n <= m -> m = n + (m - n))
  (lt_lt_or_eq : forall n m, n < S m -> n < m \/ n = m).

Ltac check_not_divides :=
  match goal with
  | [ |- (~ divides ?X1 ?X2) ] =>
      cut (X1 <= X2); [idtac | le_S_star]; intros Hle;
      rewrite (le_plus_minus _ _ Hle); apply not_divides_plus;
      simpl; clear Hle; check_not_divides
  | [ |- _ ] =>
      apply not_divides_lt; unfold lt; le_S_star
  end.

Theorem not_2_divides_9 : ~ divides 2 9.
Proof. check_not_divides. Qed.

Theorem not_9_divides_2 : ~ divides 9 2.
Proof. check_not_divides. Qed.

End primes.

(* Exercise 7.1 *)
Theorem divides_0 : forall n, divides n 0.
Proof.
  intros n; unfold divides; exists 0; reflexivity.
Qed.

Theorem divides_plus : forall n m, divides n m -> divides n (n + m).
Proof.
  destruct m as [| m'].
  - (* m = 0 *) intros H; rewrite <- plus_n_O;
    unfold divides; exists 1; simpl;
    rewrite <- plus_n_O; reflexivity.
  - (* m = S m' *) rewrite <- plus_n_Sm;
    unfold divides; intros H;
    inversion H as [x H']; exists (S x); simpl;
    rewrite plus_n_Sm; rewrite H'; reflexivity.
Qed.

Theorem not_divides_plus : forall n m, ~ divides n m -> ~ divides n (n + m).
Proof.
  intros n m; unfold divides, not.
  intros H H'. apply H. inversion H' as [x H''].
Abort.

(* End of Exercise 7.1 *)

(* Finding the Names of Hypotheses *)
Ltac contrapose H :=
  match goal with
  | [ id: (~ _) |- (~ _) ] =>
      intro H; apply id
  end.

Theorem example_contrapose :
  forall x y : nat, x <> y -> x <= y -> ~ y <= x.
Proof.
  intros x y H H0.
  contrapose H'. auto with arith.
Qed.

(* Pattern Matching and Backtracking *)
Ltac clear_all :=
  match goal with
  | [ id : _ |- _ ] => clear id; clear_all
  | [ |- _ ] => idtac
  end.

(* This tactic can be used to reduce the number of hypotheses in a goal
   before calling another tactic whose behavior is sensitive to the size
   of the context. For example, if the omega tactic only requires
   hypotheses H1, H2, and H3, then we can use the following combined
   tactic:
     generalize H1 H2 H3; clear_all; intros; omega.
*)

(* In-Depth Pattern Matching and Conditional Expressions *)




























