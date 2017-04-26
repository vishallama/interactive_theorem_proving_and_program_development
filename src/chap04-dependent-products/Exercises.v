Require Import Arith.
Require Import ZArith.
Require Import List.

Parameters (prime_divisor : nat -> nat)
           (prime : nat -> Prop)
           (divides : nat -> nat -> Prop).

Open Scope nat_scope.

Check (prime (prime_divisor 220)).

Check (divides (prime_divisor 220) 220).

Check (divides 3).

Parameter binary_word : nat -> Set.

Definition short : Set := binary_word 32.

Definition long : Set := binary_word 64.

Check ((nat -> nat) -> Prop).
Check ((nat -> nat) -> (nat -> nat) -> Prop).
Check (nat -> nat -> Set).

Check (not (divides 3 81)).
Check (let d := prime_divisor 220 in prime d /\ divides d 220).


Parameters (decomp : nat -> list nat) (decomp2 : nat -> nat * nat).

Check (decomp 220).
Check (decomp2 284).

Check @cons.
Check @pair.
Check (forall A B : Set, A -> B -> A*B).
Check @fst.

Check @le_n.
Check @le_S.
Check (le_n 36).

Definition le_36_37 := le_S 36 36 (le_n 36).
Check le_36_37.

Definition le_36_38 := le_S 36 37 le_36_37.
Check le_36_38.

Check (le_S _ _ (le_S _ _ (le_n 36))).

Definition twice : forall A : Set, (A -> A) -> A -> A :=
  fun A f a => f (f a).

Check (twice Z).
Check (twice Z (fun z => (z*z)%Z)).
Check (twice _ S 56).
Check (twice (nat -> nat) (fun f x => f (f x)) (mult 3)).

Eval compute in (twice (nat -> nat) (fun f x => f (f x)) (mult 3) 1).

Theorem le_i_SSi : forall i : nat, i <= S (S i).
Proof (fun i : nat => le_S _ _ (le_S _ _ (le_n i))).

Definition compose :
  forall A B C : Set, (A -> B) -> (B -> C) -> A -> C :=
    fun A B C f g x => g (f x).

Print compose.

Check (fun (A : Set) (f : Z -> A) => compose _ _ _ Z_of_nat f).

Implicit Arguments compose [A B C].
Implicit Arguments le_S [n m].

Check (le_S (le_i_SSi 1515)).

Check (compose (C := Z) S).

Check (le_S (n := 45)).

Reset compose.
Set Implicit Arguments.

Definition compose (A B C : Set) (f : A -> B) (g : B -> C) (a : A) :=
  g (f a).

Definition thrice (A : Set) (f : A -> A) := compose f (compose f f).

Unset Implicit Arguments.

Print compose.
Print thrice.

Eval cbv beta delta in (thrice (thrice (A := nat)) S O).

(* Exercise: 4.3 *)
Section A_declared.
  Variables (A : Set) (P Q : A -> Prop) (R : A -> A -> Prop).

  Theorem all_perm : (forall a b : A, R a b) -> forall a b : A, R b a.
  Proof (fun (H : forall a b : A, R a b) (a b : A) => H b a).

  Theorem all_imp_dist :
    (forall a : A, P a -> Q a) -> (forall a : A, P a) ->
      (forall a : A, Q a).
  Proof
    (fun (H : forall a : A, P a -> Q a) (H' : forall a : A, P a) (a : A) =>
      H a (H' a)).

  Theorem all_delta : (forall a b : A, R a b) -> forall a : A, R a a.
  Proof (fun (H : forall a b : A, R a b) (a : A) => H a a).

End A_declared.

Check (forall n : nat, 0 < n -> nat).

Theorem id : forall A : Set, A -> A.
Proof (fun (A : Set) (a : A) => a).

Theorem diag : forall A B : Set, (A -> A -> B) -> A -> B.
Proof (fun (A B : Set) (f : A -> A -> B) (a : A) => f a a).

Theorem permute : forall A B C : Set, (A -> B -> C) -> B -> A -> C.
Proof (fun (A B C : Set) (f : A -> B -> C) (b : B) (a : A) => f a b).

Theorem f_nat_Z : forall A : Set, (nat -> A) -> Z -> A.
Proof (fun (A : Set) (f : nat -> A) (z : Z) => f (Z.to_nat z)).
