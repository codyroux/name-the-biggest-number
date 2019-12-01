Require Import Arith Lia.


Fixpoint iter (f : nat -> nat) (b : nat) :=
  match b with
  | 0 => 1
  | S b' => f (iter f b')
  end.

Fixpoint ack (n a b : nat) :=
  match n with
  | 0 => S b
  | 1 => a + b
  | S n' => iter (ack n' a) b
  end.


(* This is the previous contender for largest number *)
(* Submitted by codyroux *)
Definition contender_4 := ack 5 42 10002.

Definition contender_5: nat. Admitted.


Theorem contender_4_lt_contender_5 : contender_4 < contender_5.
Proof.
Admitted.
