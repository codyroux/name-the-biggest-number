Require Import ha2_refl.


Print tm.
(* We define an injective function Nat^2 -> Nat to be able to go ham on ADTs *)
Definition Pair (t1 t2 : tm) := Add (Mult (Add t1 t2) (Add t1 t2)) t1.

(* How often do I need this? *)
(* Definition Proj1 (t1 t2 : tm) :=  *)

Print Nat.

Definition v0 := var_tm 0.
Definition v1 := var_tm 1.
Definition v2 := var_tm 2.
Definition v3 := var_tm 3.

Definition V0 := var_pred 0.
Definition V1 := var_pred 1.

(* We define constructors as particular tuples, in order to state the
induction principles. *)
Definition T_Nat := Z.

Definition T_Arrow t1 t2 := Pair (Succ Z) (Pair t1 t2).

Definition T_type t := FORALL T_Nat ∈ V0 ⇒ (all all v0 ∈ V0 ⇒ v1 ∈ V0 ⇒ (T_Arrow v0 v1) ∈ V0) ⇒ t ∈ V0.

Search (nat -> tm).

Definition T_Var n := Pair (n_tm 0) n.

Definition T_App t1 t2 := Pair (n_tm 1) (Pair t1 t2).

Definition T_Abs t := Pair (n_tm 2) t.

Definition T_Const n := Pair (n_tm 3) n.

Definition T_S t := Pair (n_tm 4) t.

Definition T_Rec ty tz ts t := Pair (n_tm 5) (Pair ty (Pair tz (Pair ts t))).

Definition T_term t :=
  FORALL
    (all Nat v0 ⇒ (T_Var v0) ∈ V0) ⇒
    (all all v0 ∈ V0 ⇒ v1 ∈ V0 ⇒ (T_App v0 v1) ∈ V0) ⇒
    (all v0 ∈ V0 ⇒ (T_Abs v0) ∈ V0) ⇒
    (all Nat v0 ⇒ (T_Const v0) ∈ V0) ⇒
    (all v0 ∈ V0 ⇒ (T_S v0) ∈ V0) ⇒
    (all all all all var_tm 0 ∈ V0 ⇒ var_tm 1 ∈ V0 ⇒ var_tm 2 ∈ V0 ⇒ var_tm 3 ∈ V0 ⇒ (T_Rec (var_tm 0) (var_tm 1) (var_tm 2) (var_tm 3)) ∈ V0) ⇒
    t ∈ V0.

Definition T_Empty_ctx := Z.
Definition T_Push_ctx v c := Pair (Succ Z) (Pair v c).
Definition T_VAbs t c := Pair Z (Pair t c).
Definition T_VConst n := Pair (Succ Z) n.

Definition T_eval_ctx e :=
  FORALL (* V0 *) FORALL (* V1 *)
         T_Empty_ctx ∈ V0 ⇒
         (all (* v0 *) all (* v1 *) v0 ∈ V1 ⇒ v1 ∈ V0 ⇒ (T_Push_ctx v0 v1) ∈ V0) ⇒
         (all (* v0 *) all (* v1 *) T_term v0 ⇒ v1 ∈ V0 ⇒ (T_VAbs v0 v1) ∈ V1) ⇒
         (all (* v0 *) (T_VConst v0) ∈ V1) ⇒
         e ∈ V0.

Definition T_value v :=
  FORALL (* V0 *) FORALL (* V1 *)
         T_Empty_ctx ∈ V0 ⇒
         (all (* v0 *) all (* v1 *) v0 ∈ V1 ⇒ v1 ∈ V0 ⇒ (T_Push_ctx v0 v1) ∈ V0) ⇒
         (all (* v0 *) all (* v1 *) T_term v0 ⇒ v1 ∈ V0 ⇒ (T_VAbs v0 v1) ∈ V1) ⇒
         (all (* v0 *) (T_VConst v0) ∈ V1) ⇒
         v ∈ V1.

Definition Triple a b c := Pair (Pair a b) c.

Definition T_nth e n v :=
  FORALL (* V0 *)
    (all (* v0 *) all (* v1 *) (Triple (T_Push_ctx v0 v1) Z v0) ∈ V0) ⇒
    (all (* v0 *) all (* v1 *) all (* v2 *) all (* v3 *)
         (Triple v3 v2 v1) ∈ V0 ⇒
         (Triple (T_Push_ctx v0 v3) (Succ v2) v1) ∈ V0) ⇒
    (Triple e n v) ∈ V0.

Definition T_TmEval e t v :=
