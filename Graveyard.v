Require Import Arith Lia.


(* This is the current contender for largest number. *)
(* Submitted by codyroux *)
Definition contender_0 : nat := 0.

Theorem contender_0_lt_nothing : True.
Proof.
  auto.
Qed.

(* Submitted by codyroux *)
Definition contender_1 : nat := 42.

Theorem contender_0_lt_contender_1 : contender_0 < contender_1.
Proof.
  unfold contender_0, contender_1.
  auto with arith.
Qed.
