(* Works in 8.9.1, submitted by jakobbotsh *)


Require Hurkens.

Module TypeNequivSmallType.
Import Hurkens.

Section Paradox.

(* I feel like this version of the paradox should already by in
   Hurkens.v but can't find it, there's only the version with A=U *)

Definition U := Type.
Variable A:U.

Variable down : U -> A.
Variable up : A -> U.
Hypothesis up_down : forall (X:U), up (down X) = X.

Theorem paradox : False.
Proof.
  Generic.paradox p.
  (** Large universe *)
  + exact U.
  + exact (fun X=>X).
  + cbn. exact (fun X F => forall x:X, F x).
  + cbn. exact (fun _ _ x => x).
  + cbn. exact (fun _ _ x => x).
  + exact (fun F => forall x:A, F (up x)).
  + cbn. exact (fun _ f => fun x:A => f (up x)).
  + cbn. intros * f X.
    specialize (f (down X)).
    rewrite up_down in f.
    exact f.
  (** Small universe *)
  + exact A.
  (** The interpretation of [A] as a universe is [U]. *)
  + cbn. exact up.
  + cbn. exact (fun _ F => down (forall x, up (F x))).
  + cbn. exact (fun _ F => down (forall x, up (F x))).
  + cbn. exact (down False).
  + rewrite up_down in p.
    exact p.
  + cbn. easy.
  + cbn. intros ? f X.
    destruct (up_down X). cbn.
    reflexivity.
  + cbn. intros ? ? f.
    rewrite up_down.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down in f.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down in f.
    exact f.
Qed.

End Paradox.

End TypeNequivSmallType.

Inductive foo (A:Type) := bar X : foo X -> foo A | nonempty.
Arguments nonempty {_}.

Notation U := TypeNequivSmallType.U.

Definition A : U := foo nat.

Definition down : U -> A := fun u => bar nat u nonempty.

Definition up : A -> U := fun a => match a with bar _ u _ => u | nonempty => nat end.

Lemma up_down : forall (X:U), up (down X) = X.
Proof.
  reflexivity.
Qed.

Definition contender_final : nat := 7.

Lemma n_lt_contender_final :
  forall n, n < contender_final.
Proof (match TypeNequivSmallType.paradox A down up up_down with end).

Print Assumptions n_lt_contender_final.