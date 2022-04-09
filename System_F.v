(*
  Mostly taken from: https://github.com/coq-community/autosubst/blob/master/examples/ssr/SystemF_SN.v

 *)

Require Export System_F_syn.


Inductive step : term -> term -> Prop :=
| step_beta (A : type) (s t : term) :
    step (App (Abs s) t) s[t..]
| step_appL s1 s2 t :
    step s1 s2 -> step (App s1 t) (App s2 t)
| step_appR s t1 t2 :
    step t1 t2 -> step (App s t1) (App s t2)
| step_abs s1 s2 :
    step s1 s2 -> step (Abs s1) (Abs s2).

Definition ctx := fin -> type.

(* Variable ty : type. *)

(* Set Printing All. *)
(* Check ty⟨↑⟩. *)

Locate ">>".
Print funcomp.
Locate "↑".
Check shift.
Definition lift_ctx : ctx -> ctx := fun Γ => Γ >> ⟨↑⟩.

Inductive has_type : forall (Γ : ctx)(t : term)(ty : type), Prop :=
| has_type_var : forall Γ n, has_type Γ (var_term n) (Γ n)
| has_type_abs : forall Γ ty1 ty2 t,
    has_type (ty1, Γ) t ty2 -> has_type Γ t (Arrow ty1 ty2)
| has_type_app : forall Γ ty1 ty2 t u,
    has_type Γ t (Arrow ty1 ty2) -> has_type Γ u ty1 -> has_type Γ (App t u) ty2
| has_type_tabs : forall Γ ty t,
    has_type (Γ >> ⟨↑⟩) t ty -> has_type Γ t (Forall ty)
| has_type_tapp : forall Γ ty1 ty2 t,
    has_type Γ t (Forall ty1) -> has_type Γ t ty1[ty2..].

Print Acc.
Definition sn t := Acc step t.

(* The main theorem *)
Theorem well_typed_sn : forall Γ t T, has_type Γ t T -> sn t.
Admitted.
