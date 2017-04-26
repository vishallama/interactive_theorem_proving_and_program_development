Require Import Arith.
Require Import ZArith.

Parameters (prime_divisor : nat -> nat)
           (prime : nat -> Prop)
           (divides : nat -> nat -> Prop).

Open Scope nat_scope.

Check (prime (prime_divisor 220)).

Check (divides (prime_divisor 220) 220).

Check (divides 3).


(* Parameterized Data Types *)

Parameter binary_word : nat -> Set.

Definition short : Set := binary_word 32.

Definition long : Set := binary_word 64.

(* Exercise 4.1 *)
Check ((nat -> nat) -> Prop). (* Compare if two naturals are equal *)
Check ((nat -> nat) -> (nat -> nat) -> Prop). (* Compare if two functions are
equal *)
Check (nat -> nat -> Set). (* Given two naturals m and n, return the type of
an m x n matrix *)

Print not.

Require Import List.

Parameters (decomp : nat -> list nat) (decomp2 : nat -> nat * nat).

Check (decomp 220).
Check (decomp2 284).

Check @cons.
Check @pair.
Check @fst.

Check le_n.
Check le_S.

Check (le_n 36).


(* Definition of Polymorphic Functions *)

Definition twice : forall A : Set, (A -> A) -> A -> A :=
  fun A f a => f (f a).

Check (twice Z).

Check (twice Z (fun z => (z*z)%Z)).

Check (twice _ S 56).

Check (twice (nat -> nat) (fun f x => f (f x)) (mult 3)).

Eval compute in
  (twice (nat -> nat) (fun f x => f (f x)) (mult 3) 1).


(* Proofs - Curry-Howard isomorphism *)
Theorem le_i_SSi : forall i : nat, i <= S (S i).
Proof (fun i : nat => le_S _ _ (le_S _ _ (le_n i))).


(* Expressive power of the Dependent Product *)

(* Exercise 4.3 *)
Section A_declared.
  Variables (A : Set) (P Q : A -> Prop) (R : A -> A -> Prop).

  Theorem all_perm : (forall a b : A, R a b) -> forall a b : A, R b a.
  Proof (fun (H : forall a b : A, R a b) (a b : A) => H b a).

  Theorem all_imp_dist :
    (forall a : A, P a -> Q a) -> (forall a : A, P a) -> forall a : A, Q a.
  Proof (fun (H : forall a : A, P a -> Q a)
             (H' : forall a : A, P a)
             (a : A) => H a (H' a)).

  Theorem all_delta : (forall a b : A, R a b) -> forall a : A, R a a.
  Proof (fun (H : forall a b : A, R a b)
             (a : A) => H a a).

End A_declared.

(* Exercise 4.4 *)
Theorem id : forall A : Set, A -> A.
Proof (fun (A : Set) (a : A) => a).
Print id.

Theorem diag : forall A B : Set, (A -> A -> B) -> A -> B.
Proof (fun (A B : Set) (f : A -> A -> B) (a : A) => (f a) a).
Print diag.

Theorem permute : forall A B C : Set, (A -> B -> C) -> B -> A -> C.
Proof (fun (A B C : Set) (f : A -> B -> C) (b : B) (a : A) => f a b).
Print permute.

Theorem f_nat_Z : forall A : Set, (nat -> A) -> Z -> A.
Proof (fun (A : Set) (f : nat -> A) (z : Z) => f (Zabs_nat z)).
Print f_nat_Z.

(* Exercise 4.5 *)
Theorem all_perm' :
  forall (A : Type) (P : A -> A -> Prop),
  (forall x y : A, P x y) -> forall x y : A, P y x.
Proof (fun (A : Type)
      (P : A -> A -> Prop)
      (H : forall x y : A, P x y) (x y : A) => H y x).
Print all_perm'.

Theorem resolution :
  forall (A : Type) (P Q R S : A -> Prop),
  (forall a : A, Q a -> R a -> S a) ->
  (forall b : A, P b -> Q b) ->
  (forall c : A, P c -> R c -> S c).
Proof.
  intros A P Q R S H H' c HPc HRc.
  apply H; [apply H'; assumption | assumption].
Qed.
Print resolution.


(* Equality in the Coq System *)

Check @eq.
Check @refl_equal.

Theorem ThirtySix : 9*4 = 6*6.
Proof (refl_equal 36).

Check eq_sym.
Print eq_sym.

Theorem eq_sym' : forall (A : Type) (x y : A), x = y -> y = x.
Proof.
  intros A x y H.
  rewrite H. reflexivity.
Qed.

Print eq_sym'.

Print and.
Print or.
