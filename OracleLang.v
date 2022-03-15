(*

Doesn't work as is: We can only carry around terms and evaluate them
wholesale, without doing funny stuff to their syntax.

We need to define levels for the evaluator, in which we're allowed to
call a first level eval, and get a term which will later be evaluated
at a second level.

*)


From Coq Require Import Arith Lia EquivDec List.

Import ListNotations.

(* The type of *indexed* system T with lists and a type of 'syntax'; essentially, Lisp. *)
Inductive type :=
| tpSyn : type
| tpNat: type
| tpList : type -> type (* Sadly, we're gonna need lists to simulate contender_5 *)
| tpArr: type -> type -> type.

Notation "A --> B" := (tpArr A B)(at level 33, right associativity).

Check (tpNat --> (tpNat --> tpNat)).

Definition eqdec_type : forall x y : type, {x = y} + {x <> y}.
Proof.
  intros x y.
  assert ({x = y} + {x <> y}) by decide equality.
  auto.
Defined.

Fixpoint type_depth(t: type): nat :=
  match t with
  | tpSyn => 1
  | tpNat => 1
  | tpList t => S (type_depth t)
  | tpArr t1 t2 => S (max (type_depth t1) (type_depth t2))
  end.

Fixpoint interp_type(Syn : Type)(tp: type): Type :=
  match tp with
  | tpSyn => Syn
  | tpNat => nat
  | tpList t => list (interp_type Syn t)
  | tpArr t1 t2 => (interp_type Syn t1) -> (interp_type Syn t2)
  end.

(* Terms with an extra "Quote" oracle, which knows how to embed programs from O, and evaluate them to a nat. *)
Inductive term (Syn : Type) :=
| tQuote(t : term Syn) (* Quoting will succeed iff no "higher" evals are beneath *)
| tVar(x: nat) (* 0 = last element of the env, ie the outermost binder (reversed DeBruijn) *)
| tLam(A B: type)(body: term Syn)
| tApp(t1 t2: term Syn)
| tO
| tS
| tNatRec(R: type)
| tEmpty(A : type)
| tCons(A : type)(hd : term Syn)(tail : term Syn)
| tListRec(A R : type)
| tEval(A : type)(s : Syn) (* Eval the syntax at type A *)
.


Definition error{Syn : Type}{tp: type}(default : Syn): interp_type Syn tp.
  revert tp.
  refine (fix rec tp := _).
  destruct tp; simpl.
  - exact default.
  - exact 0.
  - exact nil.
  - intros _; apply rec.
Defined.

(* reverse lookup *)
Definition lookup{T}(e: list T)(n: nat): option T :=
  let l := List.length e in if l <=? n then None else nth_error e (l - S n).

Definition cast{Syn}{from: type}(to: type)(default : Syn): interp_type Syn from -> interp_type Syn to.
Proof.
  destruct (eqdec_type from to).
  - rewrite e.
    exact id.
  - exact (fun _ => error default).
Defined.

Print cast.

Definition default {Syn} default : { tp : type & interp_type Syn tp } := existT _ tpNat (error default).

Definition list_recursion (A : Type) (R : Type) : R -> (A -> list A -> R -> R) -> list A -> R :=
  fun base ind l => @list_rect A (fun _ => R) base ind l.

Definition list_rec_type (A R : type) := R --> (A --> (tpList A) --> R --> R) --> (tpList A) --> R.

Record interp(Syn : Type) :=
  {
  def : Syn;
  reify : Syn -> type -> term Syn;
  eval : Syn -> { tp : type & interp_type Syn tp }
  }.

Definition interp_term: forall {Syn} (r : interp Syn) (e: list {tp: type & interp_type Syn tp}) (t: term Syn),
    {tp: type & interp_type Syn tp}.
  refine (fix rec _ r e t {struct t} :=
  match t with
  | tQuote _ t => _
  | tVar _ x =>
    match lookup e x with
    | Some v => v
    | None => default (def _ r)
    end
  | tLam _ A B body => existT _ (tpArr A B) _
  | tApp _ t1 t2 => _
  | tO _ => existT _ tpNat 0
  | tS _ => existT _ (tpArr tpNat tpNat) S
  | tNatRec _ R => existT _ (R --> (tpNat --> R --> R) --> tpNat --> R) (@Nat.recursion (interp_type _ R))
  | tEmpty _ A => existT _ (tpList A) []
  | tCons _ A hd tail => existT _ (tpArr A (tpArr (tpList A) (tpList A))) cons
  | tListRec _ A R => existT _ (list_rec_type A R) (list_recursion (interp_type _ A) (interp_type _ R))
  | tEval _ A s => _
  end).
  (* Abstraction case *)
  - simpl.
    intro x'.
    set (r := (projT2 (rec ((existT _ A x') :: e) body))).
    simpl in r.
    exact (cast B r).
  (* Application case *)
  - destruct (rec e t1) as [R1 r1] eqn: E1.
    destruct (rec e t2) as [R2 r2] eqn: E2.
    destruct R1 as [ | | |A B]; [exact (existT _ tpNat error)| exact (existT _ tpNat error) | exact (existT _ tpNat error) | ].
    simpl in *.
    exact (existT _ _ (r1 (cast A r2))).
  (* Quote case *)
  - destruct (rec e t0) as [R r] eqn: E.
    Check cast.
    exact (eval_O (cast tpO r)).
Defined.
