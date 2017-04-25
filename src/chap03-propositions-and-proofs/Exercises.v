Section Minimal_propositional_logic.

Variables P Q R T : Prop.

Section example_of_assumption.
  Hypothesis H : P -> Q -> R.

  Lemma L1 : P -> Q -> R.
  Proof.
    assumption.
  Qed.
End example_of_assumption.

Theorem delta : (P -> P -> Q) -> P -> Q.
Proof.
  exact (fun (H : P -> P -> Q)(p : P) => H p p).
Qed.

Theorem apply_example : (Q -> R -> T) -> (P -> Q) -> P -> R -> T.
Proof.
  intros H H0 p.
  apply H.
  exact (H0 p).
Qed.

Theorem imp_dist : (P -> Q -> R) -> (P -> Q) -> (P -> R).
Proof.
  intros H H' p.
  apply H.
  - assumption.
  - apply H'. assumption.
Qed.

Print imp_dist.

Theorem K : P -> Q -> P.
Proof.
  intros p q.
  assumption.
Qed.

(* Ex 3.2 *)

Lemma id_P : P -> P.
Proof.
  intro p. assumption.
Qed.

Lemma id_PP : (P -> P) -> (P -> P).
Proof.
  intro H. assumption.
Qed.

Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros H H' p.
  apply H'. apply H. assumption.
Qed.

Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros H q p.
  apply H.
  - assumption.
  - assumption.
Qed.

Lemma ignore_Q : (P -> R) -> P -> Q -> R.
Proof.
  intros H p q.
  apply H. assumption.
Qed.

Lemma delta_imp : (P -> P -> Q) -> P -> Q.
Proof.
  intros H p.
  apply H.
  - assumption.
  - assumption.
Qed.

Lemma delta_impR : (P -> Q) -> (P -> P -> Q).
Proof.
  intros H p. assumption.
Qed.

Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  intros H H' H'' p.
  apply H''.
  - apply H. assumption.
  - apply H'. assumption.
Qed.

Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  intros H. apply H.
  intros H'. apply H'.
  intro p. apply H.
  intro H'''. assumption.
Qed.

Definition f : (nat -> bool) -> (nat -> bool) -> nat -> bool.
  intros f1 f2.
  assumption.
Qed.

Print f.

Section proof_of_triple_impl.
 Hypothesis H : ((P -> Q) -> Q) -> Q.
 Hypothesis p : P.
 
 Lemma Rem : (P -> Q) -> Q.
 Proof (fun H0 : P -> Q => H0 p).
 
 Theorem triple_impl : Q.
 Proof (H Rem).
End proof_of_triple_impl.

Theorem then_example : P -> Q -> (P -> Q -> R) -> R.
Proof.
  intros p q H.
  apply H; assumption.
Qed.

Lemma L3 : (P -> Q) -> (P -> R) -> (P -> Q -> R -> T) -> P -> T.
Proof.
  intros H H0 H1 p.
  apply H1; [idtac | apply H | apply H0]; assumption.
Qed.

Theorem try_example : (P -> Q -> R -> T) -> (P -> Q) -> (P -> R -> T).
Proof.
  intros H H' p r.
  apply H; try assumption.
  apply H'. assumption.
Qed.

Section section_for_cut_example.
Hypotheses (H : P -> Q)
           (H0 : Q -> R)
           (H1 : (P -> R) -> T -> Q)
           (H2 : (P -> R) -> T).

Theorem cut_example : Q.
Proof.
  cut (P -> R).
  intro H3.
  apply H1; [assumption | apply H2; assumption].
  intro; apply H0; apply H; assumption.
Qed.

Print cut_example.

End section_for_cut_example.
End Minimal_propositional_logic.

Print imp_dist.
Print f.
Print try_example.












