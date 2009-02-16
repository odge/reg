Require Import Eqdep_dec_defined Cast.
Require Import Arith OrderedType.

Inductive Fin : nat -> Set :=
| fz n : Fin (S n)
| fs {n} : Fin n -> Fin (S n).

Definition NoConfusion_Fin n (i j : Fin n) : Prop :=
  match i, j with
    | fz _, fz _ => True
    | fz _, fs _ _ => False
    | fs _ _, fz _ => False
    | fs _ u, fs _ v => INeq Fin u v
  end.
Definition noConfusion_Fin n (i j : Fin n) : i = j -> NoConfusion_Fin n i j.
intros n i j E; elim E; elim i; simpl; intros.
exact I.
reflexivity.
Defined.

Theorem discriminate_Fin_l n : forall i : Fin n, fz n <> fs i.
intros n i E; exact (noConfusion_Fin (S n) (fz n) (fs i) E).
Defined.
Theorem discriminate_Fin_r n : forall i : Fin n, fs i <> fz n.
intros n i E; exact (noConfusion_Fin (S n) (fs i) (fz n) E).
Defined.
Theorem injection_Fin n : forall i j : Fin n, fs i = fs j -> i = j.
intros n i j E; exact (INeq_eq eq_nat_dec (noConfusion_Fin (S n) (fs i) (fs j) E)).
Defined.

Definition eq_Fin_dec n (i j : Fin n) : {i = j} + {i <> j}.
apply INeq_dec_dec.
apply eq_nat_dec.
refine (fix eq_Fin_dec n n' i j nEQn' : {INeq Fin i j} + {~ INeq Fin i j} := _).
refine (
  match i as i' in Fin n'',
        j as j' in Fin n'''
  return n = n'' -> n' = n''' -> {INeq Fin i' j'} + {~ INeq Fin i' j'}
  with
    | fz _, fz _ => fun _ _ => left _ _
    | fz _, fs _ _ => fun _ _ => right _ _
    | fs _ _, fz _ => fun _ _ => right _ _
    | fs m u, fs w v => fun _ _ =>
      if eq_Fin_dec m w u v _
        then left _ _
        else right _ _
  end (refl_equal n) (refl_equal n')
);
destruct n; destruct n';
  repeat match goal with Q : S _ = S _ |- _ => injection Q; clear Q end;
    intros; subst; subst; try discriminate.

reflexivity.
intro Q; apply (discriminate_Fin_l _ _ (INeq_eq eq_nat_dec Q)).
intro Q; apply (discriminate_Fin_r _ _ (INeq_eq eq_nat_dec Q)).
congruence.
match goal with Q : INeq Fin _ _ |- _ => rewrite Q end.
apply eq_nat_dec.
reflexivity.
match goal with H : ~ _ |- _ =>
  contradict H; rewrite (injection_Fin _ _ _ (INeq_eq eq_nat_dec H)) end.
reflexivity.
Defined.

Fixpoint nat_of_Fin n (i : Fin n) : nat :=
  match i with
    | fz _ => O
    | fs _ i => S (nat_of_Fin _ i)
  end.

Theorem nat_of_Fin_injective n (i j : Fin n) : nat_of_Fin n i = nat_of_Fin n j -> i = j.
(* difficult proof due to type errors *)
Admitted.

Definition Fin_lt n : Fin n -> Fin n -> Prop.
exact (fun n i j => nat_of_Fin n i < nat_of_Fin n j).
Defined.

Definition Fin_compare n : forall i j : Fin n, Compare (Fin_lt n) (@eq (Fin n)) i j.
refine (fun n i j =>
  match lt_eq_lt_dec (nat_of_Fin n i) (nat_of_Fin n j) with
    | inleft (left lPrf) => LT _ _
    | inleft (right ePrf) => EQ _ _
    | inright rPrf => GT _ _
  end).
apply lPrf.
apply (nat_of_Fin_injective _ _ _ ePrf).
apply rPrf.
Defined.
