Require Import Arith Lia.

(* (* This is the previous contender for largest number. *) *)
(* (* Submitted by jaykru *) *)
(* Time Definition contender_2 : nat := 42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42^42. *)

(* This is the current contender for largest number *)
(* Submitted by codyroux *)

(* This is a fun trick *)
Opaque Nat.pow.

Definition tower_of_power (n : nat) : nat :=
  Nat.recursion 42 (fun _ k => 42 ^ k) n.

Ltac depth t :=
  match constr:(t) with
  | 42 => constr:(0)
  | ?x ^ ?y =>
    let d := depth y in
    constr:(S d)
  | _ => fail
  end.

Ltac reify_tower t :=
  match constr:(t) with
  | _ ^ _ =>
    let d := depth t in
    constr:(tower_of_power d)
  | _ => fail
  end.

Ltac reify_goal :=
  match goal with
  | [ |- ?x < ?y ] =>
    let t := (reify_tower x) in
    replace x with t by reflexivity
  end.

Definition contender_3 := tower_of_power 10000.

Lemma fund_lemma : forall n m, n < m -> tower_of_power n < tower_of_power m.
Proof.
  intros.
  induction H.
  - simpl.
    apply Nat.pow_gt_lin_r; lia.
  - simpl.
    assert (42 ^ tower_of_power n < 42 ^ tower_of_power m) by (apply Nat.pow_lt_mono_r; lia).
    eapply Nat.lt_trans; [exact IHle|].
    apply Nat.pow_gt_lin_r; lia.
Qed.
    
   

(* Theorem contender_2_lt_contender_3 : contender_2 < contender_3. *)
(* Proof. *)
(*   unfold contender_2. *)
(*   Time reify_goal. *)
(*   unfold contender_3. *)
(*   apply fund_lemma. *)
(*   compute; lia. *)
(* Qed. *)


(* Fixpoint ack (n m : nat) := *)
(*   match n with *)
(*   | 0 => S m *)
(*   | S n' => *)
(*     let fix inner m := *)
(*         match m with *)
(*         | 0 => ack n' 1 *)
(*         | S m' => ack n' (inner m') *)
(*         end *)
(*     in *)
(*     inner m *)
(*   end. *)

(* Stealing this bit from wikipedia *)
(* https://en.wikipedia.org/wiki/Hyperoperation *)

Fixpoint inner (f : nat -> nat) (n a b : nat) :=
  match b with
  | 0 => match n with
         | 0 => a
         | 1 => 0
         | _ => 1
         end
  | S b' =>
    f (inner f n a b')
  end.

Fixpoint ack (n a b : nat) :=
  match n with
  | 0 => S b
  | S n' =>
    inner (ack n' a) n' a b
  end.

Eval compute in ack 0 156 3.
Eval compute in ack 1 2 6.
Eval compute in ack 2 2 6.
Eval compute in ack 3 2 4.

Definition contender_4 := ack 5 42 10000.


Lemma ack_0 : forall a b, ack 0 a b = S b.
Proof.
  intros; reflexivity.
Qed.

Lemma ack_1 : forall a b, ack 1 a b = a + b.
Proof.
  intros; simpl.
  induction b; simpl; [lia|].
  rewrite IHb; lia.
Qed.

Lemma ack_2 : forall a b, ack 2 a b = a * b.
Proof.
  intros; simpl.
  induction b; simpl; [ring|].
  rewrite IHb.
  assert (H : ack 1 a (a * b) = a + (a * b)) by (rewrite ack_1; lia).
  simpl in H.
  rewrite H.
  lia.
Qed.

Lemma ack_3 : forall a b, ack 3 a b = a ^ b.
Proof.
  intros; simpl.
  induction b; simpl; [induction a; now auto|].
  rewrite IHb.
  assert (H : ack 2 a (a ^ b) = a * (a ^ b)) by (rewrite ack_2; ring).
  simpl in H; rewrite H.
  SearchAbout (_ ^ (S _)).
  rewrite Nat.pow_succ_r'; now auto.
Qed.

Eval vm_compute in (ack 4 42 1).
Eval vm_compute in (tower_of_power 0).

Lemma ack_4 : forall b, ack 4 42 (S b) = tower_of_power b.
Proof.
  intros; simpl.
  induction b; simpl; [now auto|].
  rewrite IHb.
  assert (H : ack 3 42 (tower_of_power b) = 42 ^ (tower_of_power b)) by (rewrite ack_3; now auto).
  simpl in H; rewrite H.
  reflexivity.
Qed.

Lemma inner_mon : forall f n n' a b,
    (forall n n', n <= n' -> f n <= f n')
    -> 2 <= n <= n'
    -> inner f n a b <= inner f n' a b.
Proof.
  induction b; simpl.
  intros f_mon.
  case n; simpl; try lia.
  case n'; simpl; try lia.
  intro n0; case n0; intros; simpl; try lia.
  intros.
  revert H.
  case n0; case n1; intros; lia.

  intros f_mon leq.
  apply f_mon.
  apply IHb; try lia; auto.
Qed.

Lemma inner_ge_arg : forall f n,
    (forall n, S n <= f n) ->
    (forall n m, n <= m -> f n <= f m) ->
    2 <= n ->
    forall b a,
    b <= inner f n a b.
Proof.
  intros.
  induction b; simpl.
  - SearchAbout (_ <= _ \/ _).
    revert H1.
    case n; [lia| intro n'; case n'; [lia| now auto]].
  - transitivity (S (inner f n a b)).
    + SearchAbout (S _ <= S _).
      apply le_n_S.
      now auto.
    + apply H.
Qed.

Lemma inner_ge_f_arg : forall f n,
    (forall n, S n <= f n) ->
    (forall n m, n <= m -> f n <= f m) ->
    2 <= n ->
    forall b a,
    f b <= inner f n a (S b).
Proof.
  intros.
  simpl.
  apply H0.
  apply inner_ge_arg; auto.
Qed.

Lemma ack_gt_S_b : forall n b a,
    1 < a -> S b <= ack n a b.
Proof.
Admitted.
    

Lemma ack_mon : forall n a b n' a' b',
    n' < n -> 1 < a' < a -> 1 < b' < b -> ack n' a' b' < ack n a b.
Proof.
  induction n; intros; [lia |].
  simpl.
  assert (H2 : forall b, S b <= ack n a b).
  - intros.
    apply ack_gt_S_b; lia.
  - 
    generalize (inner_ge_f_arg (ack n a) n H2).
    intros.
    fail.



    
  unfold lt.
  transitivity (S (inner (ack n a) n a b)).
  - SearchAbout (_ ->  S _ <= S _).
     apply le_n_S.
     Print inner.

     transitivity (ack n a b).
     + apply IHn; auto.
     
     assert (exists b_pred, S b_pred = b).
     { destruct b; [lia|].
       exists b; now auto.
     }
     destruct H2 as [b_pred H2].
     subst b.
     apply inner_ge_f_arg.
     simpl.
     

      

    
Admitted.
