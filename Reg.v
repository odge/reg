Require Import Eqdep_dec_defined Cast Fin.
Require Import Arith OrderedType.

Notation "'!'" := (False_rect _ _).
Definition cast {I:Type}(F:I -> Type)(i:I) {j:I} (e : j = i) : F j -> F i :=
  fun t' => eq_rect _ F t' _ e.


Record OrderedType (t : Type) : Type :=
  { lt : t -> t -> Prop
  ; lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z
  ; lt_not_eq : forall x y : t, lt x y -> ~ eq x y
  ; compare : forall x y : t, Compare lt (@eq t) x y
  }.


Inductive type :=
| Void | Unit | Loop | Para
| Summ : type -> type -> type
| Prod : type -> type -> type.

Definition eq_type_dec : forall τ σ : type, {τ = σ} + {τ <> σ}.
decide equality.
Defined.

Definition eq_type : forall τ σ : type, τ = σ \/ τ <> σ.
decide equality.
Defined.

Section Reg.

Variable Φ : type.

Variable params : nat.
Variable paramType : Fin params -> Type.
Variable paramLt : forall i : Fin params, paramType i -> paramType i -> Prop.
Variable paramCompare : forall i : Fin params,
  forall x y : paramType i, Compare (paramLt i) (@eq (paramType i)) x y.

Inductive value : type -> Type :=
| The : value Unit
| Rec : value Φ -> value Loop
| Get : forall i : Fin params, paramType i -> value Para
| Inl : forall τ σ, value τ -> value (Summ τ σ)
| Inr : forall τ σ, value σ -> value (Summ τ σ)
| And : forall τ σ, value τ -> value σ -> value (Prod τ σ).

Definition value_lt (ρ : type) (x y : value ρ) : Prop.
refine (fix value_lt (ρ : type) (x y : value ρ) {struct x} : Prop := _).
refine (
  match x in value ρ, y in value ρ' return ρ = ρ' -> Prop with
    | The, The => fun _ => True
    
    | Rec φ, Rec φ' => fun _ => value_lt Φ φ φ'
    
    | Get i x, Get i' x' => fun _ =>
      match Fin_compare params i i' with
        | LT _ => True
        | EQ e2 => paramLt i x (cast paramType i _ x')
        | GT _ => False
      end
    
    | Inl τ σ l, Inl τ' σ' l' => fun _ => value_lt τ l (cast value τ _ l')
    | Inl τ σ l, Inr τ' σ' r' => fun _ => True
    
    | Inr τ σ r, Inl τ' σ' l' => fun _ => False
    | Inr τ σ r, Inr τ' σ' r' => fun _ => value_lt σ r (cast value σ _ r')
    
    | And τ σ u v, And τ' σ' u' v' => fun _ =>
      value_lt τ u (cast value τ _ u') \/
      (u = (cast value τ _ u') /\ value_lt σ v (cast value σ _ v'))
    
    | _, _ => fun _ => !
  end
  (refl_equal ρ)
);
match goal with
  | |- False => discriminate
  | _ => congruence
end.
Defined.


Ltac snap_Summ :=
  match goal with Q : Summ _ _ = Summ _ _ |- _ =>
    injection Q; intro; intro; clear Q
  end.

Ltac snap_Prod :=
  match goal with Q : Prod _ _ = Prod _ _ |- _ =>
    injection Q; intro; intro; clear Q
  end.

Ltac specializer :=
  (match goal with Q : ?x = ?y |- _ =>
     (subst x || subst y); clear Q end) ||
  (match goal with Q : @INeq _ _ ?i ?x ?i ?y |- _ =>
     let Q' := fresh "Q'" in
       assert (x = y) as Q' by apply (INeq_eq eq_type_dec Q);
         clear Q end) ||
  (match goal with Q : ?i = ?i |- _ =>
     rewrite (eq_proofs_unicity (eq_Fin params) Q (refl_equal _)) in *;
       clear Q; simpl in * end) ||
  snap_Summ ||
  snap_Prod.

Ltac finish :=
  exact I || reflexivity || assumption.

Ltac typ_specialize Q :=
  generalize dependent Q; repeat specializer; intro Q; intros;
    rewrite (eq_proofs_unicity eq_type Q (refl_equal _)) in *;
      simpl in *.

Definition value_compare (ρ : type) (x y : value ρ) : Compare (value_lt ρ) (@eq (value ρ)) x y.
refine (fix value_compare (ρ : type) (x y : value ρ) {struct x} : Compare (value_lt ρ) (@eq (value ρ)) x y := _).
refine (
  match x as x' in value ρ',
        y as y' in value ρ''
  return ρ' = ρ'' -> ρ = ρ' -> ρ = ρ'' ->
         INeq value x x' -> INeq value y y' ->
         Compare (value_lt ρ) (@eq (value ρ)) x y
  with
    | The, The => fun e1 e2 e3 e4 e5 => EQ _ _
    
    | Rec φ, Rec φ' => fun e1 e2 e3 e4 e5 =>
      match value_compare Φ φ φ' with
        | LT _ => LT _ _
        | EQ _ => EQ _ _
        | GT _ => GT _ _
      end
    
    | Get i x, Get i' x' => fun e1 e2 e3 e4 e5 =>
      match Fin_compare params i i' with
        | LT _ => LT _ _
        | EQ _ =>
          let Q := _ in
            match paramCompare i x (cast paramType i Q x') with
              | LT _ => LT _ _
              | EQ _ => EQ _ _
              | GT _ => GT _ _
            end
        | GT _ => GT _ _
      end
    
    | Inl τ σ l, Inl τ' σ' l' => fun e1 e2 e3 e4 e5 =>
      let Q := _ in
      match value_compare τ l (cast value τ Q l') with
        | LT _ => LT _ _
        | EQ _ => EQ _ _
        | GT _ => GT _ _
      end
    | Inl τ σ l, Inr τ' σ' r' => fun e1 e2 e3 e4 e5 => LT _ _
    
    | Inr τ σ r, Inl τ' σ' l' => fun e1 e2 e3 e4 e5 => GT _ _
    | Inr τ σ r, Inr τ' σ' r' => fun e1 e2 e3 e4 e5 =>
      let Q := _ in
      match value_compare σ r (cast value σ Q r') with
        | LT _ => LT _ _
        | EQ _ => EQ _ _
        | GT _ => GT _ _
      end

    | And τ σ u v, And τ' σ' u' v' => fun e1 e2 e3 e4 e5 =>
      let Q := _ in let Q' := _ in
      match value_compare τ u (cast value τ Q u') with
        | LT _ => LT _ _
        | EQ _ =>
          match value_compare σ v (cast value σ Q' v') with
            | LT _ => LT _ _
            | EQ _ => EQ _ _
            | GT _ => GT _ _
          end
        | GT _ => GT _ _
      end

    | _, _ => fun _ => !
  end
  (refl_equal ρ) (refl_equal ρ) (refl_equal ρ)
  (INeq_refl value x) (INeq_refl value y)
); try
match goal with
  | |- False => discriminate
  | _ => congruence
end;
try solve [ repeat specializer; finish ];
try solve [ repeat specializer; typ_specialize Q; finish ].


repeat specializer; simpl.
destruct (Fin_compare params i i').
exact I.
elim (lt_irreflexive _ _ _ f e).
elim (lt_asymm _ _ _ f f0).

repeat specializer.
destruct (Fin_compare params i' i').
elim (lt_irreflexive _ _ _ f (refl_equal _)).
specializer; assumption.
elim (lt_irreflexive _ _ _ f (refl_equal _)).

repeat specializer.
destruct (Fin_compare params i' i').
elim (lt_irreflexive _ _ _ f (refl_equal _)).
specializer; assumption.
elim (lt_irreflexive _ _ _ f (refl_equal _)).

repeat specializer; simpl.
destruct (Fin_compare params i' i).
exact I.
elim (lt_irreflexive _ _ _ f e).
elim (lt_asymm _ _ _ f f0).

repeat specializer.
injection e1; intro; clear e1.
typ_specialize Q.
left; assumption.

repeat specializer.
typ_specialize Q';
typ_specialize Q.
right; split; auto.

repeat specializer.
typ_specialize Q';
typ_specialize Q.
reflexivity.

repeat specializer.
typ_specialize Q';
typ_specialize Q.
right; split; auto.

repeat specializer.
injection e1; intro; clear e1.
typ_specialize Q.
left; assumption.

Defined.

End Reg.

Section Gen.

Variable T : Type.
Variable Φ : type.

Variable params : nat.
Variable paramType : Fin params -> Type.
Variable paramLt : forall i : Fin params, paramType i -> paramType i -> Prop.
Variable paramCompare : forall i : Fin params,
  forall x y : paramType i, Compare (paramLt i) (@eq (paramType i)) x y.

Variable codify : T -> value Φ params paramType Φ.
Variable codify_faithful : forall x y, codify x = codify y -> x = y.

Theorem generic_compare : forall x y : T,
  Compare (fun x y => value_lt Φ params paramType paramLt Φ (codify x) (codify y)) (@eq _) x y.
intros x y.
destruct (value_compare Φ params paramType paramLt paramCompare Φ (codify x) (codify y));
  [ apply LT | apply EQ | apply GT ].
assumption.
apply codify_faithful; assumption.
assumption.
Defined.

End Gen.


Section Examples.

Definition bool_code := Summ Unit Unit.
Definition bool_codify (b : bool) : value bool_code 0 no_Fin0 bool_code :=
  match b with
    | true => Inl _ _ _ _ _ (The _ _ _)
    | false => Inr _ _ _ _ _ (The _ _ _)
  end.
Theorem bool_codify_faithful : forall x y : bool, bool_codify x = bool_codify y -> x = y.
destruct x; destruct y; simpl; intros.
reflexivity.
discriminate.
discriminate.
reflexivity.
Defined.

Eval compute in generic_compare
  bool bool_code 0 no_Fin0 (fun i => no_Fin0 i) (fun i => no_Fin0 i)
  bool_codify bool_codify_faithful
  true false.
(* LT *)

Eval compute in generic_compare
  bool bool_code 0 no_Fin0 (fun i => no_Fin0 i) (fun i => no_Fin0 i)
  bool_codify bool_codify_faithful
  true true.
(* EQ *)


Definition nat_code := Summ Unit Loop.
Fixpoint nat_codify (n : nat) : value nat_code 0 no_Fin0 nat_code :=
  match n with
    | O => Inl _ _ _ _ _ (The _ _ _)
    | S n => Inr _ _ _ _ _ (Rec _ _ _ (nat_codify n))
  end.
Theorem nat_codify_faithful : forall x y : nat, nat_codify x = nat_codify y -> x = y.
fix 1; destruct x; destruct y; simpl; intros.
reflexivity.
discriminate.
discriminate.
injection H; intros H'; rewrite (nat_codify_faithful _ _ H').
reflexivity.
Defined.

Definition nat_compare := generic_compare
  nat nat_code 0 no_Fin0 (fun i => no_Fin0 i) (fun i => no_Fin0 i)
  nat_codify nat_codify_faithful.

Eval compute in nat_compare
  3 5.
(* LT *)

Eval compute in nat_compare
  7 7.
(* EQ *)


Section Parametrized_Example.

Variable param : Type.
Variable paramLt : param -> param -> Prop.
Variable paramCompare : forall i j : param, Compare paramLt (@eq _) i j.

Definition list_code := Summ Unit (Prod Para Loop).
Fixpoint list_codify (l : list param) : value list_code 1 (fun _ => param) list_code :=
  match l with
    | nil => Inl _ _ _ _ _ (The _ _ _)
    | x :: xs => Inr _ _ _ _ _ (And _ _ _ _ _ (Get _ 1 (fun _ => param) (fz 0) x) (Rec _ _ _ (list_codify xs)))
  end.
Theorem list_codify_faithful : forall x y : list param, list_codify x = list_codify y -> x = y.
fix 1; destruct x; destruct y; simpl; intro.
reflexivity.
discriminate.
discriminate.
injection H; intros.
rewrite (list_codify_faithful _ _ H0).
rewrite H1.
reflexivity.
Defined.

End Parametrized_Example.


Definition nat_lt (x y : nat) :=
  value_lt nat_code 0 no_Fin0 (fun i : Fin 0 => no_Fin0 i) nat_code
  (nat_codify x) (nat_codify y).

Eval compute in generic_compare
  (list nat) list_code 1
  (fun _ => nat)
  (fun _ => nat_lt)
  (fun _ => nat_compare)
  (list_codify nat)
  (list_codify_faithful nat)
  (2 :: 3 :: nil)
  (2 :: 3 :: 4 :: nil).
(* LT *)

End Examples.

