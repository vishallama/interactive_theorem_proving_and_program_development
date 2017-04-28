Print bool.

Inductive month : Set :=
  | January : month
  | February : month
  | March : month
  | April : month
  | May : month
  | June : month
  | July : month
  | August : month
  | September : month
  | October : month
  | November : month
  | December : month.

Check month_ind.
Check month_rec.
Check month_rect.

(* Exercise: 6.1 *)
Inductive season : Set :=
  | Spring
  | Summer
  | Fall
  | Winter.

Definition month_season' :=
  month_rec (fun month => season)
    Winter Winter Winter
    Spring Spring Spring
    Summer Summer Summer
    Fall Fall Fall.

Definition month_season (m : month) : season :=
  match m with
  | January | February | March => Winter
  | April | May | June => Spring
  | July | August | September => Summer
  | October | November | December => Fall
  end.

Lemma month_season_convertible : month_season = month_season'.
Proof. reflexivity. Qed.

(* Exercise: 6.2 *)
Check (bool_ind).
Check (bool_rec).

(* Exercise: 6.3 *)
Theorem bool_equal : forall b : bool, b = true \/ b = false.
Proof.
  intro b. pattern b. apply bool_ind.
  - left; reflexivity.
  - right; reflexivity.
Qed.

Theorem bool_equal' : forall b : bool, b = true \/ b = false.
Proof.
  destruct b.
  - left; reflexivity.
  - right; reflexivity.
Qed.

Definition month_length (leap : bool) (m : month) : nat :=
  match m with
  | January => 31 | February => if leap then 29 else 28
  | March => 31 | April => 30 | May => 31 | June => 30
  | July => 31 | August => 31 | September => 30
  | October => 31 | November => 30 | December => 31
  end.

(* Less readable code, even though it is concise *)
Definition month_length' (leap : bool) :=
  month_rec (fun month => nat)
  31 (if leap then 29 else 28) 31 30 31 30 31 31 30 31 30 31.

Definition month_length'' (leap : bool) (m : month) :=
  match m with
  | February => if leap then 29 else 28
  | April => 30 | June => 30 | September => 30 | November => 30
  | _ => 31
  end.

Eval compute in (fun leap => month_length leap November).

Theorem length_february : month_length false February = 28.
Proof.
  simpl. (* triggers iota reduction *)
  trivial.
Qed.

(* Exercise: 6.4. Solution using pattern matching presented in solution to
   Exercise 6.1 *)

(* Exercise: 6.5 *)
Definition month_even (leap : bool) (m : month) :=
  match (month_length leap m) with
  | 28 => true
  | 30 => true
  | _ => false
  end.

Definition bool_xor (b1 b2 : bool) : bool :=
  match b1, b2 with
  | true, false => true
  | false, true => true
  | _, _ => false
  end.

Definition bool_and (b1 b2 : bool) : bool :=
  if b1 then b2 else false.

Definition bool_or (b1 b2 : bool) : bool :=
  if b1 then true else b2.

Definition bool_eq (b1 b2 : bool) : bool :=
  match b1, b2 with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

Definition bool_not (b : bool) : bool :=
  if b then false else true.

Theorem bool_xor_not_eq :
 forall b1 b2:bool,
   bool_xor b1 b2 = bool_not (bool_eq b1 b2).
Proof.
  destruct b1, b2; reflexivity.
Qed.

Theorem bool_not_and :
  forall b1 b2:bool,
    bool_not (bool_and b1 b2) = bool_or (bool_not b1) (bool_not b2).
Proof.
  destruct b1, b2; reflexivity.
Qed.

Theorem bool_not_not : forall b:bool, bool_not (bool_not b) = b.
Proof.
  destruct b; reflexivity.
Qed.

Theorem bool_ex_middle : forall b:bool, bool_or b (bool_not b) = true.
Proof.
  destruct b; reflexivity.
Qed.

Theorem bool_eq_reflect :
  forall b1 b2 : bool, bool_eq b1 b2 = true -> b1 = b2.
Proof.
  destruct b1, b2; intro H; simpl in H.
  - reflexivity.
  - rewrite H. reflexivity.
  - apply H.
  - reflexivity.
Qed.

Theorem bool_eq_reflect2 :
  forall b1 b2:bool, b1 = b2 -> bool_eq b1 b2 = true.
Proof.
  destruct b1, b2; simpl; intro H; simpl in H.
  - reflexivity.
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
  - reflexivity.
Qed.

Theorem bool_not_or :
  forall b1 b2:bool,
   bool_not (bool_or b1 b2) = bool_and (bool_not b1) (bool_not b2).
Proof.
  destruct b1, b2; reflexivity.
Qed.

Theorem bool_or_and_distr :
  forall b1 b2 b3:bool,
    bool_or (bool_and b1 b3) (bool_and b2 b3) = bool_and (bool_or b1 b2) b3.
Proof.
  destruct b1, b2, b3; reflexivity.
Qed.


(* Record Types *)
Require Import ZArith.

Inductive plane : Set := point : Z -> Z -> plane.

Check plane_ind.

Definition abscissa (p : plane) : Z :=
  match p with point x _ => x end.

Reset plane.

Record plane : Set := point { abscissa : Z; ordinate : Z }.

Print plane.
Print abscissa.
Print ordinate.

(* Exercise: 6.7 *)
(* Check (plane_rec) does not work for Coq 8.6 *)

(* Exercise: 6.8 *)
Definition manhattan_distance (p1 p2 : plane) : Z :=
  (Zabs (abscissa p1 - abscissa p2)) +
  (Zabs (ordinate p1 - ordinate p2)).

Eval compute in (manhattan_distance (point 2 5) (point 2 4)). (* 1 *)
(* End of Exercise 6.8 *)


(* Records with Variants *)

Inductive vehicle : Set :=
  | bicycle : nat -> vehicle
  | motorized : nat -> nat -> vehicle.

Check vehicle_ind.

Definition nb_wheels (v : vehicle) : nat :=
  match v with
  | bicycle _ => 2
  | motorized _ n => n
  end.

Definition nb_seats (v : vehicle) : nat :=
  match v with
  | bicycle x => x
  | motorized x _ => x
  end.

(* Exercise: 6.9 *)
Check vehicle_rec.

Definition nb_seats' :=
  vehicle_rec (fun vehicle => nat)
    (fun nseats => nseats)
    (fun nseats _ => nseats).

Eval compute in nb_seats' (bicycle 1). (* 1 *)
Eval compute in nb_seats' (motorized 5 4). (* 5 *)
(* End of Exercise 6.9 *)

Theorem at_least_28 :
  forall (leap : bool) (m : month), 28 <= month_length leap m.
Proof.
  intros leap m; case m; simpl; auto with arith.
  case leap; simpl; auto with arith.
Qed.

Definition next_month (m : month) :=
  match m with
  | January => February   | February => March | March => April
  | April => May          | May => June       | June => July
  | July => August        | August => September
  | September => October  | October => November
  | November => December  | December => January
  end.

Theorem next_august_then_july :
  forall m : month, next_month m = August -> m = July.
Proof.
  intros m; case m; simpl; intros Hnext_eq;
  discriminate Hnext_eq || reflexivity.
Qed.


(* ** The Inner Workings of Discriminate *)
Theorem not_January_eq_February : ~ January = February.
Proof.
  unfold not; intros H.
  change ((fun m : month =>
             match m with
             | January => True
             | _ => False
             end) February).
  rewrite <- H.
  trivial.
Qed.

(* Exercise 6.10 *)
Definition is_January :=
  month_rect (fun month => Prop)
    True
    False
    False
    False
    False
    False
    False
    False
    False
    False
    False
    False.
(* End of Exercise 6.10 *)

(* Exercise 6.11 *)
Theorem not_true_eq_false : ~ true = false.
Proof.
  unfold not; intros H.
  change ((fun b : bool =>
             match b with
             | true => True
             | false => False
             end) false).
  rewrite <- H.
  trivial.
Qed.
(* End of Exercise 6.11 *)

(* Exercise 6.12 *)
Theorem not_bicycle_eq_motorized :
  forall (s w : nat), ~ bicycle s = motorized s w.
Proof.
  intros s w; unfold not; intros H.
  change ((fun v : vehicle =>
             match v with
             | bicycle _ => True
             | motorized _ _ => False
             end) (motorized s w)).
  rewrite <- H.
  trivial.
Qed.
(* End of Exercise 6.12 *)


(* Injective Constructors *)

Theorem bicycle_eq_seats :
  forall x1 y1 : nat, bicycle x1 = bicycle y1 -> x1 = y1.
Proof.
  intros x1 y1 H.
  injection H. trivial.
Qed.

(* ** The Inner Workings of injection *)
Reset bicycle_eq_seats.

Theorem bicycle_eq_seats :
  forall x1 y1 : nat, bicycle x1 = bicycle y1 -> x1 = y1.
Proof.
  intros x1 y1 H.
  change (nb_seats (bicycle x1) = nb_seats (bicycle y1)).
  rewrite H; trivial.
Qed.

Section injection_example.
  Variables A B : Set.

  Inductive T : Set :=
  | c1 : A -> T
  | c2 : B -> T.

  Theorem inject_c2 : forall x y : B, c2 x = c2 y -> x = y.
  Proof.
    intros x y H.
    change (let phi :=
              fun v : T =>
                match v with
                | c1 _ => x
                | c2 v' => v'
                end in
              phi (c2 x) = phi (c2 y)).
    rewrite H; simpl; reflexivity.
  Qed.
End injection_example.

(* Exercise 6.13 *)
Require Import Arith.

Record RatPlus : Set :=
  mkRat { top : nat; bottom : nat; bottom_condition : bottom <> 0 }.

Axiom eq_RatPlus :
  forall r r' : RatPlus,
    top r * bottom r' = top r' * bottom r ->
      r = r'.

Theorem inconsistent_theory : False.
Proof.
  (* TODO *)
Abort.

Reset eq_RatPlus.


(* * Guidelines for the case Tactic *)


(* Recursive Types *)

Print nat.
Check nat_ind.

Check plus.
Check plus_O_n.
Check plus_Sn_m.

Theorem plus_assoc :
  forall x y z : nat, (x + y) + z = x + (y + z).
Proof.
  intros x y z.
  elim x.
  - rewrite plus_O_n. rewrite plus_O_n. trivial.
  - intros x' Hrec.
    rewrite (plus_Sn_m x' y). rewrite (plus_Sn_m (x' + y) z).
    rewrite plus_Sn_m. rewrite Hrec. trivial.
Qed.

(* Recursive Programming *)

Fixpoint mult2 (n : nat) : nat :=
  match n with
  | O => O
  | S p => S (S (mult2 p))
  end.

Fixpoint iterate (A : Set) (f : A -> A) (n : nat) (x : A) {struct n} : A :=
  match n with
  | O => x
  | S p => f (iterate A f p x)
  end.

(* Exercise: 6.15 *)
Definition lt_3 (n : nat) : bool :=
  match n with
  | O | 1 | 2 => true
  | _ => false
  end.

Compute lt_3 43. (* false *)
Compute lt_3 2.  (* true *)
(* End of Exercise 6.15 *)

(* Exercise 6.16 *)
Fixpoint rplus (n p : nat) {struct p} : nat :=
  match p with
  | O => n
  | S p' => S (rplus n p')
  end.

Compute rplus 33 17. (* 50 *)
(* End of Exercise 6.16 *)

(* Exercise: 6.17 *)
Fixpoint sum_f (n : nat) (f : nat -> Z) {struct n} : Z :=
  match n with
  | O => f O
  | S n' => Zplus (sum_f n' f) (f n)
  end.
(* End of Exercise 6.17 *)

(* Exercise: 6.18 *)
Fixpoint two_power (n : nat) {struct n} : nat :=
  match n with
  | O => 1
  | S n' => 2 * two_power n'
  end.
(* End of Exercise 6.18 *)


(* Variations in the Form of Constructors *)

Inductive Z_btree : Set :=
  | Z_leaf : Z_btree
  | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Check Z_btree_ind.

Print positive.
Print Z.
Check positive_ind.

Fixpoint sum_all_values (t : Z_btree) : Z :=
  (match t with
   | Z_leaf => 0
   | Z_bnode v t1 t2 =>
       v + sum_all_values t1 + sum_all_values t2
   end)%Z.

Fixpoint zero_present (t : Z_btree) : bool :=
  match t with
  | Z_leaf => false
  | Z_bnode (0%Z) t1 t2 => true
  | Z_bnode _ t1 t2 => zero_present t1 || zero_present t2
  end.

Fixpoint Psucc' (x : positive) : positive :=
  match x with
  | xI x' => xO (Psucc' x')
  | xO x' => xI x'
  | xH => 2%positive
  end.

(* Exercise 6.19 *)
Eval compute in (xO (xO (xO (xI (xO (xI (xI (xI (xI xH))))))))). (* 1000 *)
Eval compute in (xI (xO (xO (xI xH)))). (* 25 *)
Eval compute in (xO (xO (xO (xO (xO (xO (xO (xO (xO xH))))))))). (* 512 *)
(* End of Exercise 6.19 *)

(* Exercise 6.20 *)
Definition pos_even_bool (p : positive) : bool :=
  match p with
  | xO _ => true
  | _ => false
  end.

Eval compute in (pos_even_bool xH). (* false *)
Eval compute in (pos_even_bool (xI (xO xH))). (* false *)
Eval compute in (pos_even_bool (xO (xI xH))). (* true *)
(* End of Exercise 6.20 *)

(* Exercise 6.21 *)
Fixpoint pos_div4 (p : positive) : Z :=
  match p with
  | xH => 1%Z
  | xO xH => 2%Z
  | xO (xO _) => 0%Z
  | xO (xI _) => 2%Z
  | xI xH => 3%Z
  | xI (xO _) => 1%Z
  | xI (xI _) => 3%Z
  end.

Eval compute in (pos_div4 512%positive). (* 0%Z *)
Eval compute in (pos_div4 18%positive). (* 2%Z *)
Eval compute in (pos_div4 31%positive). (* 3%Z *)
Eval compute in (pos_div4 65%positive). (* 1%Z *)
(* End of Exercise 6.21 *)

(* Exercise 6.23 *)
Inductive L : Set :=
  | L_True : L
  | L_False : L
  | L_and : L -> L -> L
  | L_or : L -> L -> L
  | L_not : L -> L
  | L_implies : L -> L -> L.
(* End of Exercise 6.23 *)

(* Exercise 6.25 *)
Fixpoint value_present (z : Z) (z_tree : Z_btree) : bool :=
  match z_tree with
  | Z_leaf => false
  | Z_bnode z' l_tree r_tree =>
    orb (Zeq_bool z z')
        (orb (value_present z l_tree)
             (value_present z r_tree))
  end.
(* End of Exercise 6.25 *)

(* Exercise 6.26 *)
Fixpoint power (z : Z) (n : nat) : Z :=
  match n with
  | O => 1%Z
  | S n' => Zmult z (power z n')
  end.

Example power_1 : power (2%Z) O = 1%Z.
Proof. reflexivity. Qed.

Example power_2 : power (2%Z) 2 = 4%Z.
Proof. reflexivity. Qed.

Example power_3 : power (3%Z) 2 = 9%Z.
Proof. reflexivity. Qed.

Fixpoint discrete_log (p : positive) : nat :=
  match p with
  | xH => O
  | xO p' => S (discrete_log p')
  | xI p' => S (discrete_log p')
  end.

Example discrete_log_1 : discrete_log 127%positive = 6.
Proof. reflexivity. Qed.

Example discrete_log_2 : discrete_log 128%positive = 7.
Proof. reflexivity. Qed.

Example discrete_log_3 : discrete_log 255%positive = 7.
Proof. reflexivity. Qed.

Example discrete_log_4 : discrete_log 1999%positive = 10.
Proof. reflexivity. Qed.
(* End of Exercise 6.26 *)

(* ** Types with Functional Fields *)
Inductive Z_fbtree : Set :=
  | Z_fleaf : Z_fbtree
  | Z_fnode : Z -> (bool -> Z_fbtree) -> Z_fbtree.

Definition right_son (t : Z_btree) : Z_btree :=
  match t with
  | Z_leaf => Z_leaf
  | Z_bnode _ _ t => t
  end.

Definition fright_son (t : Z_fbtree) : Z_fbtree :=
  match t with
  | Z_fleaf => Z_fleaf
  | Z_fnode _ f => f false
  end.

Fixpoint fsum_all_values (t : Z_fbtree) : Z :=
  (match t with
   | Z_fleaf => 0
   | Z_fnode v f =>
       v + fsum_all_values (f true) + fsum_all_values (f false)
   end)%Z.

(* Exercise: 6.27 *)
Fixpoint fzero_present (t : Z_fbtree) : bool :=
  match t with
  | Z_fleaf => false
  | Z_fnode 0 _ => true
  | Z_fnode _ f => fzero_present (f true) || fzero_present (f false)
  end.
(* End of Exercise: 6.27 *)


(* *** Infinitely branching trees *)
Inductive Z_inf_branch_tree : Set :=
  | Z_inf_leaf : Z_inf_branch_tree
  | Z_inf_node : Z -> (nat -> Z_inf_branch_tree) -> Z_inf_branch_tree.

Fixpoint n_sum_all_values (n : nat) (t : Z_inf_branch_tree) {struct t}
  : Z :=
  (match t with
   | Z_inf_leaf => 0
   | Z_inf_node v f =>
       v + sum_f n (fun x : nat => n_sum_all_values n (f x))
   end)%Z.


(* Proofs on Recursive Functions *)
Theorem plus_assoc' : forall x y z : nat, x + y + z = x + (y + z).
Proof.
  intros x y z; elim x.
  - simpl. trivial.
  - intros n H. simpl; rewrite H; auto.
Qed.

(* Exercise: 6.29 *)
Theorem plus_n_O' : forall n : nat, n = n + O.
Proof.
  intro n; elim n.
  - simpl; reflexivity.
  - intro n'; intro H; simpl; rewrite <- H; reflexivity.
Qed.
(* End of  Exercise: 6.29 *)

(* Exercise: 6.30 *)
Fixpoint f1 (t : Z_btree) : Z_fbtree :=
  match t with
  | Z_leaf => Z_fleaf
  | Z_bnode v l r =>
      Z_fnode v (fun b: bool => if b then f1 l else f1 r)
  end.
(* End of Exercise: 6.30 *)

(* Finish the above exercise later *)

(* Exercise: 6.31 *)
Theorem mult2_double : forall n : nat, mult2 n = n + n.
Proof.
  intro n; elim n.
  - simpl; reflexivity.
  - intros n' H. simpl. rewrite H.
    rewrite plus_n_Sm. reflexivity.
Qed.
(* End of Exercise: 6.31 *)

(* Exercise: 6.32 *)
Fixpoint sum_n (n : nat) : nat :=
  match n with
  | O => O
  | S p => n + sum_n p
  end.

Theorem sum_closed_form : forall n : nat, 2 * sum_n n = n + n.
Proof.
  intro n; elim n.
  - simpl; reflexivity.
  - intros n' H; simpl. rewrite <- plus_n_Sm.
    rewrite <- plus_n_Sm. apply f_equal. apply f_equal. 
    rewrite <- H. simpl. 
    rewrite <- plus_n_O. rewrite <- plus_n_O.
    rewrite plus_assoc. 
    assert (H': sum_n n' + (n' + sum_n n') = sum_n n' + n' + sum_n n').
    { rewrite plus_assoc. reflexivity. }
    rewrite H'.
Abort. (* TODO *)
(* End of Exercise: 6.32 *)

(* Exercise: 6.33 *)
Theorem sum_n_le_n : forall n : nat, n <= sum_n n.
Proof.
  intro n; elim n.
  - simpl; reflexivity.
  - intros n' H. simpl. auto with arith.
Qed.
(* End of Exercise: 6.33 *)


(* Anonymous Recursive Functions (fix) *)
Definition mult2' : nat -> nat :=
  fix f (n : nat) : nat :=
    match n with
    | O => O
    | S p => S (S (f p))
    end.


(* Polymorphic Types *)

(* Polymorphic Lists *)
Require Import List.

Section define_lists.
  Variable A : Set.
  Inductive list' : Set :=
  | nil' : list'
  | cons' : A -> list' -> list'.

  Check list'_ind.
End define_lists.

Check list'.
Check nil'.
Check cons'.
Check list'_ind.

Fixpoint app (A : Set) (l m : list A) {struct l} : list A :=
  match l with
  | nil => m
  | cons a l' => cons a (app A l' m)
  end.

(* Exercise: 6.34 *)
Definition first_two {A : Type} (l : list A) : list A :=
  match l with
  | a :: b :: _ => a :: b :: nil
  | _ => nil
  end.
(* End of Exercise: 6.34 *)

(* Exercise: 6.35 *)
Fixpoint first_n {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | _, nil => nil
  | O, _ => nil
  | S n', h :: t => h :: first_n n' t
  end.
(* End of Exercise: 6.35 *)

(* Exercise: 6.36 *)
Fixpoint sum_l (l : list Z) : Z :=
  (match l with
   | nil => 0
   | h :: t => h + sum_l t
   end)%Z.
(* End of Exercise: 6.36 *)

(* Exercise: 6.37 *)
Fixpoint n_ones (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => 1 :: n_ones n'
  end.
(* End of Exercise: 6.37 *)

(* Exercise: 6.38 *)
Fixpoint upto_n (n : nat) : list nat :=
  (fix f (m : nat) (l : list nat) {struct m} : list nat :=
     match m with
     | O => l
     | S m' => f m' (m :: l)
     end
  ) n nil.
(* End of Exercise: 6.38 *)


(* ** The option Type *)
Print option.

Definition pred_option (n : nat) : option nat :=
  match n with
  | O => None
  | S n' => Some n'
  end.

Definition pred2_option (n : nat) : option nat  :=
  match pred_option n with
  | None => None
  | Some n' => pred_option n'
  end.

Fixpoint nth_option {A : Type} (n : nat) (l : list A) {struct l}
  : option A :=
  match n, l with
  | O, a :: _ => Some a
  | S n', _ :: t => nth_option n' t
  | _, nil => None
  end.

(* Exercise: 6.39 *)
Fixpoint nth_option' {A : Type} (n : nat) (l : list A) {struct n}
  : option A :=
  match n, l with
  | O, a :: _ => Some a
  | S n', _ :: t => nth_option n' t
  | _, nil => None
  end.

Theorem nth_option_eq_nth_option' : forall (A : Type) (n : nat) (l : list A),
  nth_option n l = nth_option' n l.
Proof.
  intros A n l. generalize dependent n.
  destruct l as [| h l'].
  - (* l = nil *) destruct n as [| n'].
    + (* n = O *) simpl. reflexivity.
    + (* n = S n' *) simpl. reflexivity.
  - (* l = h :: l' *) destruct n as [| n'].
    + (* n = O *) simpl. reflexivity.
    + (* n = S n' *) simpl. reflexivity.
Qed.
(* End of Exercise: 6.39 *)

(* Exercise: 6.40 *)
Lemma nth_length {A : Type} : 
  forall (n:nat) (l:list A),
    nth_option n l = None <-> length l <= n.
Proof. 
  intros n l. generalize dependent n.
  induction l as [| h l' IHl].
  - (* l = nil *) destruct n as [| n'].
    + (* n = O *) simpl. split.
      { trivial. }
      { trivial. }
    + (* n = S n' *) simpl. split.
      { intro. apply le_O_n. }
      { trivial. }
  - (* l = h :: l' *) destruct n as [| n'].
    + (* n = O *) simpl. split.
      { intro H. discriminate H. }
      { intro H. inversion H. }
    + (* n = S n' *) simpl. split.
      { intro H. apply le_n_S. apply IHl. assumption. }
      { intro H. apply le_S_n in H. apply IHl in H. assumption. }
Qed.
(* End of Exercise: 6.40 *)

(* Exercise 6.41 *)
Fixpoint first_in_list {A : Set} (f : A -> bool) (l : list A)
  : option A :=
  match l with
  | nil => None
  | h :: t => if f h then Some h else first_in_list f t
  end.
(* End of Exercise 6.41 *)


(* The Type of Pairs *)
Print prod.
Print fst.

(* Exercise 6.42 *)
Fixpoint split {A B : Type} (l : list (A * B)) : list A * list B :=
  match l with
  | nil => (nil, nil)
  | (x, y) :: t =>
    let
      (t1, t2) := split t
    in
      (x :: t1, y :: t2)
  end. 

Fixpoint combine {A B: Type} (l1 : list A) (l2 :list B) : list (A*B):=
  match l1, l2 with
  | h1 :: t1, h2 :: t2 => (h1, h2) :: combine t1 t2
  | _, _ => nil
  end.

Theorem combine_of_split :
  forall (A B : Type),
  forall l : list (A*B),
    let (l1, l2) := split l in
    combine l1 l2 = l.
Proof.
  intros A B l.
  induction l as [|(a, b) l' IHl].
  - (* l = nil *) simpl. trivial.
  - (* l = h :: l' *) simpl.
    (* TODO *)
Abort.
(* End of Exercise 6.42 *)

(* Exercise 6.43 *)
Print Z_btree.

Inductive btree (A : Set) : Set :=
  | bleaf : btree A
  | bnode : A -> btree A -> btree A -> btree A.

Fixpoint Z_btree_to_btree (t : Z_btree) : btree Z :=
  match t with
  | Z_leaf =>
      bleaf Z
  | Z_bnode z t1 t2 =>
      bnode Z z
            (Z_btree_to_btree t1)
            (Z_btree_to_btree t2)
  end.

Fixpoint btree_to_Z_btree (t : btree Z) : Z_btree :=
  match t with
  | bleaf _ => Z_leaf
  | bnode _ z t1 t2 =>
      Z_bnode z
             (btree_to_Z_btree t1)
             (btree_to_Z_btree t2)
  end.

Theorem btree_to_Z_inv :
  forall t, Z_btree_to_btree (btree_to_Z_btree t) = t.
Proof.
  induction t as [| x t1 IHt1 t2 IHt2].
  - (* t = bleaf *) simpl. reflexivity.
  - (* t = bnode x t1 t2 *) simpl.
    rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

Theorem Z_btree_to_b_inv :
  forall t, btree_to_Z_btree (Z_btree_to_btree t) = t.
Proof.
  induction t as [| x t1 IHt1 t2 IHt2].
  - (* t = Z_leaf *) simpl. reflexivity.
  - (* t = Z_bnode x t1 t2 *) simpl.
    rewrite IHt1; rewrite IHt2. reflexivity.
Qed.
(* End of Exercise 6.43 *)


(* The Type of Disjoint Sums *)
Check (sum nat bool).
Check (inl bool 4).
Check (inr nat false).


(* * Dependent Inductive Types *)
Inductive ltree (n : nat) : Set :=
  | lleaf : ltree n
  | lnode : forall p : nat, p <= n -> ltree n -> ltree n -> ltree n.

Check (lnode 2 1 (le_S 1 1 (le_n 1)) (lleaf 2) (lleaf 2)).

Check ltree_ind.

Inductive sqrt_data (n : nat) : Set :=
  sqrt_intro : forall x : nat,
               x*x <= n -> n < (S x)*(S x) -> sqrt_data n.


(* Variably dependent inductive types *)
Inductive htree (A : Set) : nat -> Set :=
  | hleaf : A -> htree A O
  | hnode : forall n : nat, A -> htree A n -> htree A n -> htree A (S n).

Print htree_ind.


(* *Empty Types *)
Inductive Empty_set : Set := .
Print Empty_set_ind.

Inductive strange : Set := cs : strange -> strange.
Check strange_ind.

Theorem strange_empty : forall x : strange, False.
Proof.
  intros x. elim x. trivial.
Qed.

(* Exercise: 6.51 *)
Theorem all_equal : forall x y : Empty_set, x = y.
Proof.
  intros x; elim x.
Qed.

Theorem all_diff : forall x y : Empty_set, x <> y.
Proof.
  intro x; elim x.
Qed.
(* End of Exercise: 6.51 *)


(* Dependence and Empty Types *)
Inductive even_line : nat -> Set :=
  | even_empty_line : even_line 0
  | even_step_line : forall n : nat, even_line n -> even_line (S (S n)).

Check even_empty_line.
Check (even_step_line _ even_empty_line).
Check (even_step_line _ (even_step_line _ even_empty_line)).
