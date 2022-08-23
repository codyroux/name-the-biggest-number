Require Import ha2_refl.
Close Scope subst_scope.
Require Import List.

Import ListNotations.

Fixpoint vars_up_to (n : nat) : list fin :=
  match n with
  | 0 => [0]
  | S m => n :: vars_up_to m
  end.


Class has_depth A := { depth : A -> nat }.

Instance has_depth_fin : has_depth fin := {| depth n := n |}.

(* Let's see if we need this... *)
Class enum A {d : has_depth A} :=
  {
    list_up_to : nat -> list A;
    list_has_all : forall n (a : A), depth a <= n -> In a (list_up_to n);
  }.

(* Useful if we're defining the set of elements of depth less than n by induction *)
Class enum_up_to A {d : has_depth A} n :=
  {
    list_le_n : list A;
    list_has_all_n : forall a, depth a <= n -> In a list_le_n;
  }.

Instance enum_up_to_enum {A} {d : has_depth A} (h : forall n, enum_up_to A n) : enum A.
Proof.
  refine {| list_up_to := fun n => @list_le_n _ _ _ (h n) |}.
  intros.
  destruct (h n); simpl.
  auto.
Defined.

Instance enum_enum_up_to {A} {d : has_depth A} {e : enum A} : forall n, enum_up_to A n.
Proof.
  intro n.
  refine {| list_le_n := list_up_to n |}.
  destruct e; auto.
Defined.

Require Import Lia.

Instance enum_fin : enum fin.
Proof.
  refine {| list_up_to := vars_up_to |}.
  induction n; simpl; intros; [ lia | ].
  assert (h : a <= n \/ a = S n) by lia.
  destruct h; [ | lia ].
  right; auto.
Defined.

Generalizable Variable A.

Fixpoint depth_list `{has_depth A} (l : list A) : nat :=
  match l with
  | [] => S 0
  | a::aa => S (depth a + depth_list aa)
  end.

Definition apply_1 {A B} (f : A -> B)(l : list A) : list B := map f l.

Lemma mem_apply_1 : forall {A B} (l : list A) (a : A) (f : A -> B),
    In a l -> In (f a) (apply_1 f l).
Proof.
  Search map.
  intros; apply in_map; auto.
Qed.

Fixpoint apply_2 {A B C} (f : A -> B -> C)(l1 : list A) (l2 : list B) : list C :=
  match l1 with
  | [] => []
  | a::aa => (apply_1 (f a) l2) ++ apply_2 f aa l2
  end.

Lemma mem_apply_2 : forall {A B C} (l1 : list A) (l2 : list B) a b (f : A -> B -> C),
    In a l1 -> In b l2 -> In (f a b) (apply_2 f l1 l2).
Proof.
  intros until l1.
  induction l1; simpl; auto.
  intros until f.
  intros [h1 | h2] h; subst.
  - apply in_or_app; left; apply mem_apply_1; auto.
  - apply in_or_app; right; auto.
Qed.

Instance has_depth_pair {A B} {da : has_depth A} {db : has_depth B} : has_depth (A * B) := {| depth (p : A * B) := let (a, b) := p in depth a + depth b |}.

Instance enum_pair {A B} `{ea : enum A} `{eb : enum B} : enum (A * B).
refine {| list_up_to n := apply_2 (@pair A B) (list_up_to n) (list_up_to n) |}.
destruct ea, eb.
intros n [a b] h;
  simpl in h.
apply mem_apply_2; [apply list_has_all0; lia | apply list_has_all1; lia ].
Defined.

Record enum_component_1 B n :=
  {
    enum_ty :> Type;
    constr : enum_ty -> B;
    ha_depth_ty : has_depth enum_ty;
    is_enum_ty : enum_up_to enum_ty n;
  }.

(* (* Since most of our constructors have *at most* 2 arguments, we *)
(*    define a type that has exactly 2, and will put in dummy unit args *)
(*    if they have fewer, and tuple them up if there are more. *)
(* *) *)
(* Record enum_component_2 C n := *)
(*   { *)
(*     enum_ty1 : Type; *)
(*     enum_ty2 : Type; *)
(*     constr : enum_ty1 -> enum_ty2 -> C; *)
(*     has_depth_ty1 : has_depth enum_ty1; *)
(*     has_depth_ty2 : has_depth enum_ty2; *)
(*     is_enum_ty1 : enum_up_to enum_ty1 n; *)
(*     is_enum_ty2 : enum_up_to enum_ty2 n; *)
(*   }. *)


(* Useful dummy instances *)
Instance has_depth_false : has_depth False :=
  {| depth (f : False) := match f with end |}.

Instance enum_false : enum False.
Proof.
  refine {| list_up_to _ := [] |}.
  intros; auto.
Defined.

Instance has_depth_tt : has_depth unit :=
  {| depth (_ : unit) := 0 |}.

Instance enum_unit : enum unit.
Proof.
  refine {| list_up_to _ := [tt] |}.
  intros.
  destruct a; simpl; auto.
Defined.

Arguments enum_ty {B} {n}.
Arguments is_enum_ty {B} {n}.

Fixpoint apply_all_1 {A n} (l : list (enum_component_1 A n)) : list A :=
  match l with
  | [] => []
  | c::cs =>
      let list_le_n_c := @list_le_n _ _ _ (is_enum_ty c) in
      apply_1 (constr _ n c) list_le_n_c ++
                     apply_all_1 cs
  end.


(* Fixpoint apply_all_2 {A n} (l : list (enum_component_2 A n)) : list A := *)
(*   match l with *)
(*   | [] => [] *)
(*   | c::cs => *)
(*       let list_le_n_c1 := @list_le_n _ _ _ (is_enum_ty1 c) in *)
(*       let list_le_n_c2 := @list_le_n _ _ _ (is_enum_ty2 c) in *)
(*       apply_2 (constr _ n c) list_le_n_c1 list_le_n_c2 ++ *)
(*                      apply_all_2 cs *)
(*   end. *)


(* Instance has_depth_enum_component_1 {A n} : forall (c : enum_component_1 A n), has_depth c. *)
(* Proof. *)
(*   intro c; destruct c; auto. *)
(* Defined. *)

Instance has_depth_enum_componant {A n} : forall (c : enum_component_1 A n), has_depth (enum_ty c).
Proof.
  intros c; destruct c; auto.
Defined.

(* Instance has_depth_enum_component_1 {A n} : forall (c : enum_component_2 A n), has_depth (enum_ty1 c). *)
(* Proof. *)
(*   intro c; destruct c; auto. *)
(* Defined. *)

(* Instance has_depth_enum_component_2 {A n} : forall (c : enum_component_2 A n), has_depth (enum_ty2 c). *)
(* Proof. *)
(*   intro c; destruct c; auto. *)
(* Defined. *)

Lemma all_of_depth_n : forall A n
                              (h : has_depth A)
                              (l : list (enum_component_1 A n)),
    (forall a, depth a <= S n ->
               exists (c : enum_component_1 A n) (b : enum_ty c),
                 In c l /\ depth b <= n /\ a = constr _ _ _ b)
    -> forall a, depth a <= S n -> In a (apply_all_1 l).
Proof.
  intros A n h l H a dpth.
  destruct (H a dpth) as (c & b & mem_l & depth_b & is_cons); subst.
  clear H dpth.
  revert c b mem_l depth_b.
  induction l; simpl; auto.
  intros c b [h1 | h2] le_b.
  - apply in_or_app; left.
    subst; apply mem_apply_1; destruct c.
    apply is_enum_ty0; auto.
  - apply in_or_app; right.
    auto.
Qed.


(* Lemma all_of_depth_n : forall A n *)
(*                               (h : has_depth A) *)
(*                               (l1 : list (enum_component_2 A n)), *)
(*     (forall a, depth a <= S n -> *)
(*                exists (c : enum_component_2 A n) (b1 : enum_ty1 c)(b2 : enum_ty2 c), *)
(*                  In c l1 /\ depth b1 <= n /\ depth b2 <= n /\ a = constr _ _ _ b1 b2) *)
(*     -> forall a, depth a <= S n -> In a (apply_all_2 l1). *)
(* Proof. *)
(*   intros. *)
(*   destruct (H a H0) as (c & b1 & b2 & mem_l1 & depth_b1 & depth_b2 & is_cons); subst. *)
(*   clear H H0. *)
(*   revert c b1 b2 mem_l1 depth_b1 depth_b2. *)
(*   induction l1; simpl; auto. *)
(*   intros c b1 b2 [h1 | h2] le_b1 le_b2. *)
(*   - apply in_or_app; left. *)
(*     subst; apply mem_apply_2; destruct c. *)
(*     + apply is_enum_ty3; auto. *)
(*     + apply is_enum_ty4; auto. *)
(*   - apply in_or_app; right. *)
(*     auto. *)
(* Qed. *)

(* Let's define the identity enum_component, since we may need it *)
Definition id_enum_comp {A} n {d : has_depth A} {e : enum_up_to A n} : enum_component_1 A n :=
    {|
      enum_ty := A;
      constr a := a;
    |}.


Fixpoint depth_tm t :=
      match t with
      | var_tm v => S (depth v)
      | Z => 1
      | Succ t' => S (depth_tm t')
      | ha2_syn.Add t1 t2 => S (depth_tm t1 + depth_tm t2)
      | Mult t1 t2 => S (depth_tm t1 + depth_tm t2)
      end.

Instance has_depth_tm : has_depth tm :=
  {| depth := depth_tm |}.

(* We'll bootstrap this later *)
Instance enum_up_to_tm_0 : enum_up_to tm 0.
Proof.
  refine {| list_le_n := [] |}.
  intros a; destruct a; simpl; lia.
Defined.

Definition var_tm_enum_comp n : enum_component_1 tm n :=
    {|
      enum_ty := fin;
      constr b := var_tm b;
    |}.

Definition Z_enum_comp n : enum_component_1 tm n :=
  {|
    enum_ty := unit;
    constr a := Z;
  |}.

Definition Succ_enum_comp n (h : enum_up_to tm n) : enum_component_1 tm n :=
  {|
    enum_ty := tm;
    constr b := Succ b;
  |}.


(* A bit of proof duplication unfortunately *)
Instance enum_up_to_pair {A B} n `(ea : enum_up_to A n) `(eb : enum_up_to B n) :
  enum_up_to (A * B) n.
Proof.
  refine {| list_le_n := apply_2 pair list_le_n list_le_n |}.
  intros [a b] h.
  destruct ea, eb.
  simpl in h.
  apply mem_apply_2; [apply list_has_all_n0; lia | apply list_has_all_n1; lia].
Defined.

(* Low but should suffice... *)
Set Typeclasses Depth 10.

Definition Add_enum_comp n (h : enum_up_to tm n) : enum_component_1 tm n :=
  {|
    enum_ty := tm * tm;
    constr (p : tm * tm) := let (a, b) := p in ha2_syn.Add a b;
  |}.

Definition Mult_enum_comp n (h : enum_up_to tm n) : enum_component_1 tm n :=
  {|
    enum_ty := tm * tm;
    constr p := let (a, b) := p in Mult a b;
  |}.


Check (apply_all_1 ([(var_tm_enum_comp 0); (var_tm_enum_comp 0)])).

Definition incr_enum_tm_fun n (h : enum_up_to tm n) : list tm :=
  (apply_all_1
     (
       [(var_tm_enum_comp n);
        (* id_enum_comp n; *)(* I thought we'd need this... *)
        Z_enum_comp n;
        Succ_enum_comp n _ ;
        Add_enum_comp n _ ;
        Mult_enum_comp n _
       ]
  )).

Instance incr_enum_tm_enum_up_to n (h : enum_up_to tm n) : enum_up_to tm (S n).
Proof.
  refine
    {|
      list_le_n := incr_enum_tm_fun n h
    |}.
  apply all_of_depth_n; auto.
  destruct a; simpl; intros.
  - exists (var_tm_enum_comp n).
    simpl; exists n0; split; auto.
    repeat split; lia.
  - exists (Z_enum_comp n).
    simpl. exists tt.
    split; auto.
    repeat split; lia.
  - exists (Succ_enum_comp n h).
    simpl; exists a; split; auto.
    repeat split; lia.
  - exists (Add_enum_comp n h).
    simpl. exists (pair a1 a2); split; auto.
    repeat split; lia.
  - exists (Mult_enum_comp n h).
    simpl. exists (pair a1 a2); split; [auto | repeat split; lia].
    do 4 right; left; auto.
Defined.
    

Fixpoint enum_up_to_tm_rec n : enum_up_to tm n :=
  match n with
  | 0 => enum_up_to_tm_0
  | S n' => incr_enum_tm_enum_up_to _ (enum_up_to_tm_rec n')
  end.

Instance enum_up_to_tm : forall n, enum_up_to tm n :=
  fun n => enum_up_to_tm_rec n.

(* Nice! *)
Eval lazy in (@list_le_n tm _ _ (enum_up_to_tm 2)).

Instance enum_tm : enum tm := _.

(* Ok let's see if we can do propositions *)

Fixpoint depth_prop p :=
  match p with
  | v ∈ pr => S (depth v + depth_pred pr)
  | all p' => S (depth_prop p')
  | FORALL p' => S (depth_prop p')
  | p1 ⇒ p2 => S (depth_prop p1 + depth_prop p2)
  end with depth_pred pr :=
    match pr with
    | var_pred v => S (depth v)
    | {{ _ | p }} => S (depth_prop p)
    end.

Instance has_depth_prop : has_depth prop := {| depth := depth_prop |}.
Instance has_depth_pred : has_depth pred := {| depth := depth_pred |}.

Instance enum_up_to_prop_0 : enum_up_to prop 0.
Proof.
  refine {| list_le_n := [] |}.
  intros a; destruct a; simpl; lia.
Defined.


Instance enum_up_to_pred_0 : enum_up_to pred 0.
Proof.
  refine {| list_le_n := [] |}.
  intros a; destruct a; simpl; lia.
Defined.

Definition var_pred_enum_comp n : enum_component_1 pred n.
Proof.
  refine {| enum_ty := fin |}.
  exact (fun n => var_pred n).
Defined.

Definition Mem_prop_enum_comp n
           (h_pred : enum_up_to pred n)
  : enum_component_1 prop n.
Proof.
  refine {| enum_ty := tm * pred |}.
  exact (fun '(pair t p) => t ∈ p).
Defined.

Definition Forallt_prop_enum_comp n
           (h_prop : enum_up_to prop n)
  : enum_component_1 prop n.
Proof.
  refine {| enum_ty := prop |}.
  exact (fun p => all p).
Defined.

Definition Forallp_prop_enum_comp n
           (h_prop : enum_up_to prop n)
  : enum_component_1 prop n.
Proof.
  refine {| enum_ty := prop |}.
  exact (fun p => FORALL p).
Defined.

Definition Impl_prop_enum_comp n
           (h_prop : enum_up_to prop n)
  : enum_component_1 prop n.
Proof.
  refine {| enum_ty := prop * prop |}.
  exact (fun '(pair p q) => p ⇒ q).
Defined.

Definition Comp_pred_enum_comp n
           (h_prop : enum_up_to prop n)
  : enum_component_1 pred n.
Proof.
  refine {| enum_ty := prop |}.
  exact (fun p => {{ _ | p }}).
Defined.

Definition incr_enum_prop_fun (n : fin) (h1 : enum_up_to prop n) (h2 : enum_up_to pred n) : list prop :=
  apply_all_1
    ([
        Mem_prop_enum_comp n h2;
        Forallt_prop_enum_comp n h1;
        Forallp_prop_enum_comp n h1;
        Impl_prop_enum_comp n h1
    ]).


Definition incr_enum_pred_fun (n : fin) (h1 : enum_up_to prop n) (h2 : enum_up_to pred n) : list pred :=
  apply_all_1
    ([
        var_pred_enum_comp n;
        Comp_pred_enum_comp n h1
    ]).

Instance incr_enum_prop_enum_up_to n (h1 : enum_up_to prop n)(h2 : enum_up_to pred n) : enum_up_to prop (S n).
Proof.
  refine
    {|
      list_le_n := incr_enum_prop_fun n h1 h2
    |}.
  apply all_of_depth_n; auto.
  destruct a; simpl; intros.
  - exists (Mem_prop_enum_comp _ _); simpl.
    exists (pair t p).
    intuition; lia.
  - exists (Forallt_prop_enum_comp _ _); simpl.
    exists a.
    intuition.
  - exists (Forallp_prop_enum_comp _ _); simpl.
    exists a.
    intuition.
  - exists (Impl_prop_enum_comp _ _); simpl.
    exists (pair a1 a2); intuition; lia.
Defined.

Instance incr_enum_pred_enum_up_to n (h1 : enum_up_to prop n)(h2 : enum_up_to pred n) : enum_up_to pred (S n).
Proof.
  refine
    {|
      list_le_n := incr_enum_pred_fun n h1 h2
    |}.
  apply all_of_depth_n; auto.
  destruct a; simpl; intros.
  - exists (var_pred_enum_comp _); simpl.
    exists n0; intuition.
  - exists (Comp_pred_enum_comp _ _); simpl.
    exists p; intuition.
Defined.

Fixpoint enum_up_to_prop_rec n : enum_up_to prop n :=
  match n with
  | 0 => enum_up_to_prop_0
  | S n' => incr_enum_prop_enum_up_to
              n'
              (enum_up_to_prop_rec n')
              (enum_up_to_pred_rec n')
  end
with enum_up_to_pred_rec n : enum_up_to pred n :=
       match n with
       | 0 => enum_up_to_pred_0
       | S n' => incr_enum_pred_enum_up_to
                   n'
                   (enum_up_to_prop_rec n')
                   (enum_up_to_pred_rec n')
  end.
             
Instance enum_up_to_prop : forall n, enum_up_to prop n :=
  fun n => enum_up_to_prop_rec n.

Instance enum_up_to_pred : forall n, enum_up_to pred n :=
  fun n => enum_up_to_pred_rec n.

Instance enum_prop : enum prop := _.

Instance enum_pred : enum pred := _.

(* Ok now proofs! *)


Instance has_depth_list {A} {d : has_depth A} : has_depth (list A) :=
  {|
    depth := depth_list
  |}.

Lemma depth_list_len : forall A (d : has_depth A) (l : list A),
    length l <= depth l.
Proof.
  induction l; simpl; auto.
  unfold depth, has_depth_list in IHl.
  lia.
Qed.

Lemma depth_list_In : forall A (d : has_depth A) (l : list A) a,
    In a l -> depth a <= depth l.
Proof.
  intros A d l; induction l; simpl; intros ? h.
  - contradiction.
  - destruct h.
    + subst; lia.
    + assert (h := IHl _ H).
      rewrite h.
      unfold depth; simpl.
      lia.
Qed.

Fixpoint cons_all {A} (l : list A) (ll : list (list A)) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => map (fun l' => x :: l') ll ++ cons_all xs ll
  end.


Lemma in_cons_all : forall A (l : list A) (ll : list (list A)) x xs,
    In x l -> In xs ll -> In (x :: xs) (cons_all l ll).
Proof.
  intros A l; induction l; simpl; auto.
  intros ll x xs.
  rewrite in_app_iff.
  intros [hd | tl]; subst.
  - intros mem; left.
    revert xs mem.
    induction ll; simpl; auto.
    intros xs [h1 | h2]; subst; auto.
  - auto.
Qed.

Fixpoint enum_list_len {A} {d : has_depth A} {e : enum A}
         (len : nat) (dpth : nat) : list (list A) :=
  match len with
  | 0 => [[]]
  | S len' =>
      let xs : list A := list_up_to dpth in
      let rec := enum_list_len len' dpth in
      rec ++ (cons_all xs rec)
  end.


Lemma enum_list_list_in : forall A (d : has_depth A) (e : enum A) l m n,
    depth l <= n -> length l <= m -> In l (enum_list_len m n).
Proof.
  intros A d e l m; revert l.
  induction m; simpl;
    intros l; assert (h := depth_list_len _ _ l).
  - intros; 
      assert (len_l_zero : length l = 0) by lia.
    left; symmetry; apply length_zero_iff_nil; auto.
  - intros n depth_l.
    rewrite PeanoNat.Nat.le_succ_r.
    rewrite in_app_iff.
    intros [h1 | h2].
    + left; auto.
    + right.
      destruct l; [simpl in *; lia | ].
      simpl in depth_l.
      apply in_cons_all.
      -- apply list_has_all; lia.
      -- simpl in h2;
           unfold depth in IHm; simpl in IHm;
           apply IHm; lia.
Qed.
      

Definition enum_list {A} {d : has_depth A} {e : enum A} : enum (list A).
Proof.
  refine {| list_up_to n := enum_list_len n n |}.
  intros; apply enum_list_list_in; auto.
  rewrite (depth_list_len A d) ; auto.
Defined.

Eval vm_compute in (@enum_list_len fin _ _ 3 3).

Fixpoint depth_derives {Γ P} (d : Γ ⊢ P) : nat :=
  match d with
  | axiom n Γ P _ => S (depth Γ)
  | imp_intro Γ P Q p => S (depth Γ + depth P + depth Q + depth_derives p)
  | forallt_intro Γ P p => S (depth (lift_tm Γ) + depth P + depth_derives p)
  | forallP_intro Γ P p => S (depth (lift_prop Γ) + depth P + depth_derives p)
  | imp_elim Γ P Q p q => S (depth Γ + depth P + depth Q + depth_derives p + depth_derives q)
  | forallt_elim Γ P t p => S (depth Γ + depth P + depth t + depth_derives p)
  | forallP_elim Γ P Q p => S (depth Γ + depth P + depth Q + depth_derives p)
  | compr_intro Γ P t p =>
      S (depth Γ + depth (subst2 (t .: ids) ids P) + depth_derives p)
  | compr_elim Γ P t p => S (depth Γ + depth (t ∈ {{_ | P}}) + depth_derives p)
  | _ => S (depth Γ)
  end.

Record proof_bundle :=
  {
    hyps : ctxt;
    concl : prop;
    proof : hyps ⊢ concl;
  }.

Instance has_depth_proof_bundle : has_depth proof_bundle :=
  {| depth b := depth (hyps b) + depth (concl b) + depth_derives (proof b) |}.

(* Now just gotta prove that we can enumerate those puppies.*)

Instance enum_up_to_derives_0 : enum_up_to proof_bundle 0.
Proof.
  refine {| list_le_n := [] |}.
  destruct a; simpl.
  destruct proof0; simpl; lia.
Defined.

(* Opaque dummy proof, to handle "impossible" cases in our enumeration *)
Definition dummy_proof : proof_bundle.
  refine
    (let h := [var_tm 0 ∈ var_pred 0] in
     let c := var_tm 0 ∈ var_pred 0 in
     {|
       hyps := h;
       concl := c;
       proof := axiom 0 h c Logic.eq_refl
     |}).
Qed.


(* Check (fin * ctxt * prop)%type. *)

Search ({ _ < _} + { _ }).
About Nat.ltb.

Instance enum_up_to_ctxt n : enum_up_to ctxt n.
Proof.
  apply @enum_enum_up_to; apply @enum_list; apply _.
Defined.

Definition axiom_enum_component n : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := fin * ctxt;
      constr '(pair n Γ) :=
      if Compare_dec.lt_dec n (length Γ) then _ else dummy_proof
    |}.
  econstructor.
  apply (axiom n).
  apply nth_error_nth' with (d := (var_tm 0 ∈ var_pred 0)).
  exact l.
Defined.

Definition imp_intro_enum_component n (h: enum_up_to proof_bundle n) : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := proof_bundle;
      constr pr :=
      let '{| hyps := hyps; concl := concl; proof := proof |} := pr in
      (match hyps as h return hyps = h -> proof_bundle with
       | [] => fun _ => dummy_proof
       | P::Ps =>
           fun _ =>
             let new_proof := imp_intro _ _ _ _ in
             {| hyps := Ps; concl := P ⇒ concl; proof := new_proof |}
       end) (Logic.eq_refl)
    |}.
  rewrite<- e.
  apply proof.
Defined.

Record has_shape {A B : Type}(unshape : B -> A) :=
  {
    shape : A -> option B;
    shape_correct :
    forall a b, shape a = Some b <-> unshape b = a
  }.


Definition lower : fin -> fin := Nat.pred.

Require Import ha2.

Definition lower_tm (Γ : ctxt) := map (fun P => P⟨lower; id⟩) Γ.
Definition lower_prop (Γ : ctxt) := map (fun P => P⟨id; lower⟩) Γ.

Require Import Classes.EquivDec.


Lemma dec_prop_eq : forall (p q : prop), {p = q} + {p <> q}
with dec_pred_eq : forall (p q : pred), {p = q} + {p <> q}.
Proof.
  repeat decide equality.
  repeat decide equality.
Defined.

Instance eqdec_prop : EqDec prop eq.
Proof.
  exact dec_prop_eq.
Defined.

Instance eqdec_ctxt : EqDec ctxt eq.
Proof.
  apply _.
Defined.

Lemma lower_lift_tm : forall Γ, lower_tm (lift_tm Γ) = Γ.
Proof.
  induction Γ; simpl; auto.
  asimpl.
  rewrite IHΓ; f_equal; auto.
  erewrite extRen_prop.
  - rewrite rinstId_prop.
    reflexivity.
  - auto.
  - auto.
Qed.


Lemma lower_lift_prop : forall Γ, lower_prop (lift_prop Γ) = Γ.
Proof.
  induction Γ; simpl; auto.
  asimpl.
  rewrite IHΓ; f_equal; auto.
  erewrite extRen_prop.
  - rewrite rinstId_prop.
    reflexivity.
  - auto.
  - auto.
Qed.


Search (sumbool).

Search (EqDec).

Print equiv_decb.

Print sigT.
Search sig.

Definition bool_of_sumbool {A B} (o : {A} + {B}) : bool := proj1_sig (Sumbool.bool_of_sumbool o).

Definition has_shape_lift_tm : has_shape lift_tm.
Proof.
  refine {| shape Γ :=
           if lift_tm (lower_tm Γ) ==b Γ then Some (lower_tm Γ) else None
         |}.
  intros; split.
  - unfold "==b".
    destruct (lift_tm (lower_tm a) == a).
    + intros h; inversion h.
      subst; auto.
    + intros h; inversion h.
  - intros h; subst.
    rewrite lower_lift_tm.
    unfold "==b".
    destruct (lift_tm b == lift_tm b); auto.
    destruct c; auto.
    reflexivity.
Defined.

Definition has_shape_lift_prop : has_shape lift_prop.
Proof.
  refine {| shape Γ :=
           if lift_prop (lower_prop Γ) ==b Γ then Some (lower_prop Γ) else None
         |}.
  unfold "==b".
  intros; split.
  - destruct (lift_prop (lower_prop a) == a).
    + intros h; inversion h.
      subst; auto.
    + intros h; inversion h.
  - intros h; subst.
    rewrite lower_lift_prop.
    destruct (lift_prop b == lift_prop b); auto.
    destruct c; auto.
    reflexivity.
Defined.

Definition forallt_intro_enum_component n (h: enum_up_to proof_bundle n) : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := proof_bundle;
      constr pr :=
      let '{| hyps := hyps; concl := concl; proof := proof |} := pr in
      let hyps_shape := has_shape_lift_tm in
      let lift_hyps := shape lift_tm hyps_shape hyps in
      _
    |}.
  destruct hyps_shape.
  simpl in lift_hyps.
  destruct lift_hyps as [lift_hyps' |] eqn:eq; [ |  exact dummy_proof].
  econstructor; apply forallt_intro.
  assert (shape_correct0 := shape_correct0 hyps lift_hyps').
  assert (shape_correct : shape0 hyps = Some lift_hyps' -> lift_tm lift_hyps' = hyps) by (apply shape_correct0).
  rewrite shape_correct; auto.
  exact proof.
Defined.



Definition forallP_intro_enum_component n (h : enum_up_to proof_bundle n) : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := proof_bundle;
      constr pr :=
      let '{| hyps := hyps; concl := concl; proof := proof |} := pr in
      let hyps_shape := has_shape_lift_prop in
      let lift_hyps := shape lift_prop hyps_shape hyps in
      _
    |}.
  destruct hyps_shape.
  simpl in lift_hyps.
  case_eq lift_hyps; intros lift_hyps'; [ |  exact dummy_proof].
  intros eq; econstructor; apply forallP_intro.
  subst lift_hyps.
  rewrite shape_correct0 in eq.
  subst.
  apply proof.
Defined.

Definition has_shape_impl : has_shape (fun '(pair P Q) => P ⇒ Q).
Proof.
  refine
    {|
      shape P :=
      match P with
      | P ⇒ Q => Some (pair P Q)
      | _ => None
      end
    |}.
  intros a b; destruct a; destruct b; split; intros h; try inversion h; try congruence.
Defined.

Definition imp_elim_enum_component n (h : enum_up_to proof_bundle n) : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := proof_bundle * proof_bundle;
      constr '(pair pr1 pr2) :=
      let '{| hyps := hyps1; concl := concl1; proof := proof1 |} := pr1 in
      let '{| hyps := hyps2; concl := concl2; proof := proof2 |} := pr2 in
      let concl_shape := has_shape_impl in
      let arr_concl := shape _ concl_shape concl1 in
      _
    |}.
  destruct concl_shape.
  simpl in *.
  case_eq arr_concl; [intros (P & Q) eq | intros; apply dummy_proof ].
  subst arr_concl.
  rewrite shape_correct0 in eq.
  destruct (hyps1 == hyps2); [ | apply dummy_proof].
  destruct (concl2 == P); [ | apply dummy_proof].
  subst.
  econstructor; eapply imp_elim.
  - apply proof1.
  - rewrite e.
    rewrite <- e0.
    apply proof2.
Defined.

Print derives.


Definition forallt_elim_enum_component n (h : enum_up_to proof_bundle n) : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := proof_bundle * tm;
      constr '(pair pr t) :=
      let '{| hyps := hyps; concl := concl; proof := proof |} := pr in
      match concl as c return concl = c -> proof_bundle with
      | all P => _
      | _ => fun _ => dummy_proof
      end  (Logic.eq_refl)
    |} .
  intros eq; econstructor.
  apply forallt_elim.
  rewrite eq in proof.
  apply proof.
  Unshelve.
  apply Z.
Defined.


Definition forallP_elim_enum_component n (h : enum_up_to proof_bundle n) : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := proof_bundle * pred;
      constr '(pair pr p) :=
      let '{| hyps := hyps; concl := concl; proof := proof |} := pr in
      match concl as c return concl = c -> proof_bundle with
      | FORALL P => _
      | _ => fun _ => dummy_proof
      end  (Logic.eq_refl)
    |} .
  intros eq; econstructor.
  apply forallP_elim.
  rewrite eq in proof.
  apply proof.
  Unshelve.
  apply (var_pred 0).
Defined.

Print derives.

Print has_shape.

Definition has_shape_tm_subst (P : prop) (t : tm) : has_shape (fun tt : unit => P[t..;ids]).
Proof.
  refine {| shape := fun a => if a == P[t..;ids] then Some tt else None |}.
  intros a [].
  destruct (a == P[t..; ids]).
  - rewrite e; intuition.
  - split; intros h; try congruence.
    inversion h.
Defined.


Definition compr_intro_enum_component n (h : enum_up_to proof_bundle n) : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := proof_bundle * prop * tm;
      constr '(pair (pair pr p) t) :=
      let '{| hyps := hyps; concl := concl; proof := proof |} := pr in
      _
    |}.
  pose (shape_p_t := (has_shape_tm_subst p t)).
  destruct shape_p_t.
  case_eq (shape0 concl).
  - intros tt eq.
    econstructor.
    apply compr_intro.
    assert (h': p[t..;ids] = concl) by (eapply shape_correct0; eauto).
    rewrite<- h' in proof.
    apply proof.
  - intros _; exact dummy_proof.
Defined.

Print derives.

Definition has_shape_mem_compr (P : prop) (t : tm) : has_shape (fun tt : unit => t ∈ {{ _ | P }}).
Proof.
  refine {| shape := fun a => if a == t ∈ {{ _ | P }} then Some tt else None |}.
  intros a [].
  destruct (a == t ∈ {{ _ | P }}).
  - rewrite e; intuition.
  - split; intros h; try congruence.
    inversion h.
Defined.

Definition compr_elim_enum_component n (h : enum_up_to proof_bundle n) : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := proof_bundle * prop * tm;
      constr '(pair (pair pr p) t) :=
      let '{| hyps := hyps; concl := concl; proof := proof |} := pr in
      _
    |}.
  pose (shape_p_t := (has_shape_mem_compr p t)).
  destruct shape_p_t.
  case_eq (shape0 concl).
  - intros tt eq.
    econstructor.
    Check compr_elim.
    Print pred.
    apply compr_elim.
    assert (h': (t ∈ {{ _ | p }}) = concl) by (eapply shape_correct0; eauto).
    rewrite<- h' in proof.
    apply proof.
  - intros _; exact dummy_proof.
Defined.

Print derives.

(* Ugh this is tedious. I should have put axioms into a list or something... *)
Definition zero_S_enum_component n : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := ctxt;
      constr Γ := {| hyps := Γ; concl := all Succ (var_tm 0) ≄ Z; proof := zero_S Γ |}
    |}.
Defined.

Definition inj_S_enum_component n : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := ctxt;
      constr Γ := {| hyps := Γ; concl := all (all Succ (var_tm 1) ≃ Succ (var_tm 0) ⇒ var_tm 1 ≃ var_tm 0); proof := inj_S Γ |}
    |}.
Defined.

Definition plus_Z_enum_component n : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := ctxt;
      constr Γ := {| hyps := Γ; concl := all Add (var_tm 0) Z ≃ var_tm 0; proof := plus_Z Γ |}
    |}.
Defined.

Definition plus_S_enum_component n : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := ctxt;
      constr Γ := {| hyps := Γ; concl := all (all Add (var_tm 1) (Succ (var_tm 0)) ≃ Succ (Add (var_tm 1) (var_tm 0))); proof := plus_S Γ |}
    |}.
Defined.

Definition times_Z_enum_component n : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := ctxt;
      constr Γ := {| hyps := Γ; concl := all Mult (var_tm 0) Z ≃ Z; proof := times_Z Γ |}
    |}.
Defined.

Definition times_S_enum_component n : enum_component_1 proof_bundle n.
Proof.
  refine
    {|
      enum_ty := ctxt;
      constr Γ := {| hyps := Γ; concl := all (all Mult (var_tm 1) (Succ (var_tm 0)) ≃ Add (var_tm 1) (Mult (var_tm 1) (var_tm 0))); proof := times_S Γ |}
    |}.
Defined.

Check incr_enum_pred_enum_up_to.

Print enum_up_to.

Print incr_enum_pred_fun.
Check apply_all_1.
Print derives.

Definition incr_enum_proof_bundle_fun n (h : enum_up_to proof_bundle n) :=
  apply_all_1
    ([
        axiom_enum_component n;
        imp_intro_enum_component n h;
        forallt_intro_enum_component n h;
        forallP_intro_enum_component n h;
        imp_elim_enum_component n h;
        forallt_elim_enum_component n h;
        forallP_elim_enum_component n h;
        compr_intro_enum_component n h;
        compr_elim_enum_component n h;
        zero_S_enum_component n;
        inj_S_enum_component n;
        plus_Z_enum_component n;
        plus_S_enum_component n;
        times_Z_enum_component n;
        times_S_enum_component n
    ]).

Check EqDec.
Lemma EqDec_prop : forall A, EqDec A eq -> forall (a b : A), a = b \/ a <> b.
Proof.
  intros A eq a b; destruct (eq a b).
  - rewrite e; auto.
  - right; auto.
Qed.

Require Import Eqdep_dec.

Definition transport_1 {A} {a1 a2} (F : A -> Type) : a1 = a2 -> F a2 -> F a1.
Proof.
  intros e; rewrite e; exact (fun x => x).
Defined.

Definition transport_2 {A B} {a1 a2 : A}{b1 b2 :  B} (F : A -> B -> Type) : a1 = a2 -> b1 = b2 -> F a2 b2 -> F a1 b1.
Proof.
  intros e1 e2; rewrite e1; rewrite e2; exact (fun x => x).
Defined.

Lemma transport_2_refl_l : forall {A B} {a : A}{b1 b2 :  B} (F : A -> B -> Type) (eq: b1 = b2) (x : F a b2), transport_2 F Logic.eq_refl eq x = transport_1 (fun b => F a b) eq x.
Proof.
  reflexivity.
Qed.

Definition eq_bundle (b1 b2 : proof_bundle) :=
  exists (ph : hyps b1 = hyps b2)(pc : concl b1 = concl b2), (proof b1 = transport_2 (fun a b => a ⊢ b) ph pc (proof b2)).

Theorem eq_bundle_eq : forall b1 b2, eq_bundle b1 b2 -> b1 = b2.
Proof.
  destruct b1; destruct b2.
  unfold eq_bundle; intros (eq1 & eq2 & eq3).
  simpl in *.
  rewrite eq3.
  destruct eq1.
  destruct eq2.
  unfold transport_2.
  unfold eq_rect_r.
  simpl.
  reflexivity.
Qed.


Lemma eq_axiom : forall n Γ P Q e1 e2 (eqpq : P = Q),
    axiom n Γ P e1 = transport_1 _ eqpq (axiom n Γ Q e2).
Proof.
  intros until eqpq.
  destruct eqpq.
  unfold transport_1, eq_rect_r; simpl.
  f_equal.
  apply eq_proofs_unicity.
  decide equality.
  apply EqDec_prop; apply _.
Qed.

Search (_ = left _).

Lemma eq_dec_refl `{EqDec A eq} : forall (x : A), (x == x) = left Logic.eq_refl.
Proof.
  intros x.
  destruct (x == x) as [ |  c]; [f_equal | destruct c; reflexivity ].
  pattern e at 1.
  apply K_dec; auto.
  intros a b; destruct (H a b); auto.
Qed.

Lemma eqb_refl `{EqDec A eq} : forall (x : A), (x ==b x) = true.
Proof.
  intros x; unfold "==b"; destruct (x == x); [ now auto |].
  destruct c; reflexivity.
Qed.

Instance eq_dec_ctxt : EqDec ctxt eq := ltac:(apply _).


Definition incr_enum_proof_bundle_enum_up_to n (h : enum_up_to proof_bundle n) : enum_up_to proof_bundle (S n).
Proof.
  refine
    {|
      list_le_n := incr_enum_proof_bundle_fun n h
    |}.
  apply all_of_depth_n; simpl; auto.
  (* This is going to sting *)
  intros a; remember a as bndl.
  destruct a as [hyps concl proof].
  destruct proof; intros.
  - subst; simpl in *.
    exists (axiom_enum_component n).
    exists (pair n0 Γ).
    split; [simpl; left; now auto | ].
    split; simpl.
    + simpl in *.
      assert (n0 <= depth_list Γ).
      {
        assert (n0 < length Γ) by (apply nth_error_Some; destruct (nth_error Γ n0); auto; inversion e; try congruence).
        assert (len_depth := depth_list_len _ _ Γ); simpl in *.
        lia.
      }
      lia.
    + destruct (Compare_dec.lt_dec n0 (length Γ));
        [ |
          clear H;
          assert (n0 < length Γ);
          try apply nth_error_Some;
          try (intros e'; rewrite e' in e; inversion e);
          contradiction].
      apply eq_bundle_eq.
      assert (e' : P = nth n0 Γ (var_tm 0 ∈ var_pred 0)) by (symmetry; apply nth_error_nth; auto).
      exists Logic.eq_refl, e'.
      rewrite transport_2_refl_l.
      simpl.
      apply eq_axiom.
  - exists (imp_intro_enum_component n h).
    exists {| hyps := P :: Γ; concl := Q; proof := proof0 |}.
    split; [right; left; now auto | ].
    split; [ | subst; simpl; now auto].
    subst.
    simpl in *.
    lia.
  - exists (forallt_intro_enum_component n h).
    exists {| hyps := lift_tm Γ; concl := P; proof := proof0 |}.
    split; [right; right; left; now auto |].
    split.
    + simpl.
      subst; simpl in *.
      lia.
    + subst.
      clear H.
      simpl.
      rewrite lower_lift_tm.
      rewrite eqb_refl.
      Search (_ ==b _).
      
      dependent destruction (lift_tm (lower_tm (lift_tm Γ)) ==b lift_tm Γ).
      pattern (if @equiv_decb _ eq _ eqdec_ctxt (lift_tm (lower_tm (lift_tm Γ))) (lift_tm Γ)
               then Some (lower_tm (lift_tm Γ))
               else None).

      replace (if @equiv_decb _ eq _ eqdec_ctxt (lift_tm (lower_tm (lift_tm Γ))) (lift_tm Γ)
               then Some (lower_tm (lift_tm Γ))
               else None)
        with (Some (lower_tm (lift_tm Γ))).


      pattern (lift_tm (lower_tm (lift_tm Γ)) ==b lift_tm Γ) at 2.
      
      (* replace (lift_tm (lower_tm (lift_tm Γ))) with (lift_tm Γ). *)
      (* rewrite lower_lift_tm. *)
      (* pose (my_case := *)
      (*         (if lift_tm (lower_tm (lift_tm Γ)) == lift_tm Γ *)
      (*          then Some (lower_tm (lift_tm Γ)) *)
      (*          else None)). *)
      (* assert (my_case = Some Γ). *)
      (* { unfold my_case. *)
      (*   rewrite lower_lift_tm. *)
      (*   rewrite eq_dec_refl; auto. *)
      (* }. *)
      (* unfold my_case in H0; rewrite H0. *)
