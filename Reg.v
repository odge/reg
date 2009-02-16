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
        | LT _ => LT _ _ | EQ _ => EQ _ _ | GT _ => GT _ _
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
try subst;
repeat match goal with Q : INeq _ _ _ |- _ => rewrite Q; [ apply eq_type_dec | clear Q ] end.
(* pattern match specialization and proofs *)
Admitted.

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
destruct (value_compare Φ params paramType paramLt Φ (codify x) (codify y));
  [ apply LT | apply EQ | apply GT ].
assumption.
apply codify_faithful; assumption.
assumption.
Defined.

End Gen.
