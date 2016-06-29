Require Import Reals.
Require Import List.
Require Import Fourier.

(* Only tested with coq 8.4pl6 *)

Local Open Scope R_scope.

(* my own version of non-negative reals, I think just for the better names *)
Record NNR : Type := mkNNR { NNRr : R; NNR_pos : 0 <= NNRr }.

Program Definition NNR_0 := @mkNNR 0 _.
Solve Obligations using fourier.
Program Definition NNR_1 := @mkNNR 1 _.
Solve Obligations using fourier.

Program Definition NNR_plus (a b : NNR) : NNR := @mkNNR (NNRr a + NNRr b) _.
Next Obligation.
  case a, b.
  simpl.
  fourier.
Defined.
Infix "+++" := NNR_plus (at level 50, left associativity).

Program Definition NNR_mult (a b : NNR) : NNR := @mkNNR (NNRr a * NNRr b) _.
Next Obligation.
  case a, b.
  apply Rmult_le_pos; auto.
Defined.
Infix "***" := NNR_mult (at level 40, left associativity).

(* Shorthand for decidability of T *)
Definition dec_def (T : Type) := forall a b : T, {a = b} + {a <> b}.
Hint Transparent dec_def.
Hint Unfold dec_def.

Module Type PCFG_params.
  Parameter Σ : Type. (* The terminal type *)
  Parameter Σ_dec : forall a b : Σ, {a = b} + {a <> b}.
End PCFG_params.

Module PCFG (params : PCFG_params).
  Import params.

  Let string := list Σ.

  Hint Resolve Σ_dec.

  Definition string_dec : dec_def string.
    unfold dec_def.
    decide equality.
  Defined.
  Opaque string_dec.

  (* a useful definition of monotonic functions ℕ -> ℝ⁺, eqivalent (not needed
     or proven here) to the standard (a <= b -> f(a) <= f(b)). *)
  Definition natNNRMono (f : nat -> NNR) :=
    forall d, NNRr (f d) <= NNRr (f (S d)).
  Transparent natNNRMono.

  Record monoFn := mkMonoFn { monoFnFn : nat -> NNR;
                              monoFnMono : natNNRMono monoFnFn }.

  (* definition of expressions, ideally U would take (Expr * NNR), but depth
     indexing causes some awkwardness here. Nullability calculations will be
     placed in this position, and they will need a depth index. This is saved as
     a function to make the derivative depth-agnostic; only language generation
     will muck with depth. While only nullability and constant functions will
     appear here, it's generalized to all monotonic (nat -> NNR). *)
  Inductive Expr {NT} :=
  | emp : Expr
  | ε : Expr
  | term : Σ -> Expr
  | U : Expr * monoFn -> Expr * monoFn -> Expr
  | seq : Expr -> Expr -> Expr
  | nonterm : NT -> Expr.
  Arguments Expr : clear implicits.

  Notation "∅" := emp.
  Infix "·" := seq (right associativity, at level 80).

  Print Expr_rect.
  (* Coq has trouble with noticing structurality of products within an
    inductive, but since it's prettier to have the grouping we define our own
    rect *)
  Definition Expr'_rect :=
    fun (NT : Type) (P : Expr NT -> Type) (f : P emp) (f0 : P ε)
        (f1 : forall σ : Σ, P (term σ))
        (f2 : forall r : Expr NT,
                P r ->
                forall (r0 : monoFn) (r1 : Expr NT),
                  P r1 -> forall r2 : monoFn, P (U (r, r0) (r1, r2)))
        (f3 : forall r : Expr NT, P r -> forall r0 : Expr NT, P r0 -> P (seq r r0))
        (f4 : forall n : NT, P (nonterm n)) =>
      fix F (r : Expr NT) : P r :=
    match r as r0 return (P r0) with
      | emp => f
      | ε => f0
      | term σ => f1 σ
      | U (r0, r1) (r2, r3) => f2 r0 (F r0) r1 r2 (F r2) r3
      | seq r0 r1 => f3 r0 (F r0) r1 (F r1)
      | nonterm y => f4 y
    end.

  (* A mapping from non-terminals to expressions is almost a grammar, we'll add
  the start expression later *)
  Definition rules NT := NT -> Expr NT.

  (* We need a stronger induction hypothesis that takes into account both
  structural recursion and depth-indexed non-terminal recursion *)
  Program Definition pcfg_super_rect
          {NT : Type}
          (rho : rules NT)
          (P : nat -> Expr NT -> Type)
          (f5 : forall r, P O r)
          (f : forall d, P d emp)
          (f0 : forall d, P d ε)
          (f1 : forall σ d, P d (term σ))
          (f2 : forall (d : nat)
                       (r0 r1 : Expr NT)
                       (p0 p1 : monoFn),
                    P d r0 -> P d r1 ->
                    P d (U (r0, p0) (r1, p1)))
          (f3 : forall r d,
                  P d r ->
                  forall r0 : Expr NT,
                    P d r0 -> P d (seq r r0))
          (f4 : forall d nt, P d (rho nt) -> P (S d) (nonterm nt))
  : forall r d, P d r :=
    fix F r d : P d r :=
    match r as r0 return (P d r0) with
      | emp => f d
      | ε => f0 d
      | term σ => f1 σ d
      | U (r0, p0) (r1, p1) => f2 d r0 r1 p0 p1 (F r0 d) (F r1 d)
      | seq r0 r1 => f3 r0 d (F r0 d) r1 (F r1 d)
      | nonterm y => _
    end.
  Next Obligation.
    revert y.
    induction d; intros.
    apply f5.
    apply f4.
    induction (rho y) using Expr'_rect; auto.
  Defined.

  (* instance Functor Expr *)
  Fixpoint exprMap {A B} (f : A -> B) (a : Expr A) : Expr B :=
    match a with
      | ∅ => ∅
      | ε => ε
      | term σ => term σ
      | U (l, l_prob) (r, r_prob) => U (exprMap f l, l_prob) (exprMap f r, r_prob)
      | l · r => exprMap f l · exprMap f r
      | nonterm nt => nonterm (f nt)
    end.
  Hint Unfold exprMap.

  Definition const {A B} : A -> B -> A :=
    fun x _ => x.

  Program Definition constMono (x : NNR) : monoFn := mkMonoFn (const x) _.
  Next Obligation.
    unfold const, natNNRMono.
    intros.
    fourier.
  Qed.

  Record pcfg {NT} := mkPcfg { pcfgRules : rules NT ;
                               pcfgStart : Expr NT }.
  Arguments pcfg : clear implicits.
  Arguments mkPcfg [NT] _ _.

  (* Now that PCFGs are defined, we define the languages they generate *)

  (* a language is a discrete measure on strings *)
  Definition lang := string -> NNR.

  (* First, some list/real utilities *)
  Fixpoint finite_sum (l : list NNR) : NNR :=
    match l with
      | nil => NNR_0
      | x :: xs => x +++ finite_sum xs
    end.

  Program Fixpoint finite_sum_eq_proof_irrelevence
          (l0 l1 : list NNR)
          (map_eq : map NNRr l0 = map NNRr l1)
  : NNRr (finite_sum l0) = NNRr (finite_sum l1) :=
    match l0, l1 with
      | nil, nil => _
      | x :: xs, y :: ys => _ (finite_sum_eq_proof_irrelevence xs ys)
      | nil, _ :: _ => False_rect _ _
      | _ :: _, nil => False_rect _ _
    end.
  Next Obligation.
    apply f_equal2; auto.
  Defined.

  Fixpoint relate_lists {A B} (P : A -> B -> Prop) (la : list A) (lb : list B) : Prop :=
    match la, lb with
      | nil, nil => True
      | nil, _ :: _ => False
      | _ :: _, nil => False
      | a :: la', b :: lb' => P a b /\ relate_lists P la' lb'
    end.

  Lemma relate_lists_map {A B} (P : B -> B -> Prop) (f g : A -> B) :
    forall (l : list A),
      (forall a, P (f a) (g a)) ->
      relate_lists P (map f l) (map g l).
  Proof.
    intros.
    induction l; simpl; auto.
  Qed.

  Program Fixpoint finite_sum_all_le
          (l0 l1 : list NNR)
          (map_le : relate_lists (Rle) (map NNRr l0) (map NNRr l1))
  : NNRr (finite_sum l0) <= NNRr (finite_sum l1) :=
    match l0, l1 with
      | nil, nil => _
      | x :: xs, y :: ys => _ (finite_sum_all_le xs ys)
      | nil, _ :: _ => False_rect _ _
      | _ :: _, nil => False_rect _ _
    end.
  Next Obligation.
    fourier.
  Qed.
  Next Obligation.
    inversion map_le.
    apply Rplus_le_compat; auto.
  Defined.

  Fixpoint all_splits {A} (l : list A) : list (list A * list A) :=
  match l with
    | nil => (nil, nil) :: nil
    | c :: l' =>
      let splits := all_splits l' in
      (nil, l) :: map (fun x => (c :: (fst x), snd x)) splits
  end.

  (* SECTION: language generation *)

  (* gen will be a depth-indexed function that converts a PCFG into a language.
     We can't tie the depth-indexed knot yet, so we need to take in both the
     depth recursive part (gen) and the current depth (d) for any suspended
     nullabilities. *)
  Fixpoint gen_unfixed {NT}
           (gen : Expr NT -> lang)
           (d : nat)
           (rho : rules NT)
           (e : Expr NT)
           (s : string)
  : NNR :=
    match e with
      | ∅ => NNR_0
      | ε => if string_dec s nil then NNR_1 else NNR_0
      | term c => if string_dec s (c :: nil) then NNR_1 else NNR_0
      | U (l, pl) (r, pr) =>
        monoFnFn pl d *** gen_unfixed gen d rho l s +++
        monoFnFn pr d *** gen_unfixed gen d rho r s
      | l · r =>
        finite_sum
          (map (fun (s1s2 : string * string) =>
                  let (s1, s2) := s1s2 in
                  gen_unfixed gen d rho l s1 *** gen_unfixed gen d rho r s2)
               (all_splits s))
      | nonterm nt => gen (rho nt) s
    end.

  Lemma gen_unfixed_mono {NT}
        (gen' : nat -> Expr NT -> lang)
        (gen'_mono : forall e s, natNNRMono (fun d => gen' d e s))
        (rho : rules NT)
        (e : Expr NT)
        (s : string)
  : natNNRMono (fun d => gen_unfixed (gen' d) d rho e s).
  Proof.
    unfold natNNRMono.
    intros.
    revert s.
    induction e using Expr'_rect;
      intros;
      simpl;
      try fourier.
    +
      destruct r0, r2.
      apply Rplus_le_compat;
        apply Rmult_le_compat;
        try apply NNR_pos;
        auto.
    +
      apply finite_sum_all_le.
      repeat rewrite map_map.
      apply relate_lists_map.
      destruct a.
      apply Rmult_le_compat; try apply NNR_pos; auto.
    +
      apply gen'_mono.
  Qed.

  (* Tie the knot *)
  Fixpoint gen {NT} (d : nat) (rho : rules NT) (e : Expr NT) : lang :=
    match d with
      | O => (fun s => NNR_0)
      | S d' => gen_unfixed (gen d' rho) d' rho e
    end.

  (* TODO: this proof is largely duplicated from genn_mono *)
  Lemma gen_mono {NT} (rho : rules NT) (e : Expr NT) (s : string)
  : natNNRMono (fun d => gen d rho e s).
    unfold natNNRMono.
    intros.
    revert s.
    induction e, d using (pcfg_super_rect rho);
      intros;
      try (induction d; [apply NNR_pos; fail|]);
      try apply NNR_pos;
      simpl;
      try fourier.
    -
      apply Rplus_le_compat;
      apply Rmult_le_compat;
      try apply NNR_pos.
      +
        induction p0; auto.
      +
        apply IHd.
      +
        induction p1; auto.
      +
        apply IHd0.
    -
      apply finite_sum_all_le.
      repeat rewrite map_map.
      apply relate_lists_map.
      induction a.
      apply Rmult_le_compat; try apply NNR_pos.
      apply IHd.
      apply IHd0.
    -
      apply IHd.
  Qed.

  Definition pcfg_gen {NT} (depth : nat) (gr : pcfg NT) : lang :=
    gen depth (pcfgRules gr) (pcfgStart gr).

  (* nullability is easily defined in terms of gen *)
  Definition δ {NT} (d : nat) (rho : rules NT) (e : Expr NT) : NNR :=
    gen_unfixed (gen d rho) d rho e nil.

  Lemma δ_mono {NT} {rho : rules NT} {e : Expr NT}
  : natNNRMono (fun d => δ d rho e).
  Proof.
    unfold natNNRMono, δ.
    apply gen_unfixed_mono.
    apply gen_mono.
  Qed.

  (* SECTION: definition for derivatives of PCFGs *)

  (* A differentiated (or not) non-terminal, after deriving an expression by
  'x', any non-terminals N become either N_ε or N_'x' *)
  Inductive dNT {NT} :=
  | justNT : NT -> dNT
  | derived : Σ -> NT -> dNT.
  Arguments dNT : clear implicits.

  (* The expression derivative: remove σ from expr, rho is needed for the
  nullability computation that takes place in sequencing *)
  Fixpoint eD {NT} (σ : Σ) (rho : rules NT) (e : Expr NT) : Expr (dNT NT) :=
    match e with
      | ∅ => ∅
      | ε => ∅
      | term σ' => if Σ_dec σ σ' then ε else ∅
      | U (l, l_prob) (r, r_prob) => U (eD σ rho l, l_prob) (eD σ rho r, r_prob)
      | l · r => U (eD σ rho r, mkMonoFn (fun d => δ d rho l) δ_mono)
                   (eD σ rho l · exprMap justNT r, constMono NNR_1)
      | nonterm n => nonterm (derived σ n)
    end.

  (* lift the definition of derivatives to rules *)
  Definition liftedD {NT} (rho : rules NT) : rules (dNT NT) :=
    fun s =>
      match s with
        | justNT s' => exprMap justNT (rho s')
        | derived σ s' => eD σ rho (rho s')
      end.

  (* derivative of PCFGs *)
  Definition gD {NT} (d : nat) (σ : Σ) (g : pcfg NT) : pcfg (dNT NT) :=
    mkPcfg (liftedD (pcfgRules g))
           (eD σ (pcfgRules g) (pcfgStart g)).

  (* SECTION: correctness of gD *)

  (* Definition of language derivative, this is the standard of correctness *)
  Definition lD (c : Σ) (l : lang) : lang :=
    fun s => l (c :: s).
  Transparent lD.

  (* definition of correctness for one expression: lD(gen(e)) = gen(gD(e)) *)
  Definition eD_gen_commute_defn NT (d : nat) (rho : rules NT) (e : Expr NT) :=
    forall (σ : Σ) (s : string),
      NNRr (lD σ (gen d rho e) s) = NNRr (gen d (liftedD rho) (eD σ rho e) s).
  Transparent eD_gen_commute_defn.
  Hint Unfold eD_gen_commute_defn.

  (* case by case on e *)
  Lemma emp_commutes {NT} d rho : eD_gen_commute_defn NT d rho ∅ .
  Proof.
    induction d; auto.
  Qed.

  Lemma eps_commutes {NT} d rho : eD_gen_commute_defn NT d rho ε.
  Proof.
    induction d; auto.
  Qed.

  Lemma term_commutes {NT} σ d rho : eD_gen_commute_defn NT d rho (term σ).
  Proof.
    unfold eD_gen_commute_defn; intros.
    induction d; auto.
    unfold lD.
    simpl.
    induction string_dec; simpl.
    +
      injection a.
      intros.
      rewrite H, H0.
      induction Σ_dec; tauto.
    +
      induction Σ_dec.
      -
        simpl.
        induction string_dec; auto.
        rewrite a, a0 in *.
        contradict b; auto.
      -
        auto.
  Qed.

  Lemma U_commutes {NT} :
    forall d rho l lp r rp,
      eD_gen_commute_defn NT d rho l ->
      eD_gen_commute_defn NT d rho r ->
      eD_gen_commute_defn NT d rho (U (l, lp) (r, rp)).
  Proof.
    unfold eD_gen_commute_defn.
    intros.
    induction d; auto.
    unfold lD in *.
    simpl in *.
    repeat apply f_equal2; auto.
  Qed.

  Lemma seq_commutes {NT} :
    forall rho d l r,
      eD_gen_commute_defn NT d rho l ->
      eD_gen_commute_defn NT d rho r ->
      eD_gen_commute_defn NT d rho (l · r).
  Proof.
    unfold eD_gen_commute_defn.
    intros.
    revert s.
    induction d; intros; auto.
    unfold lD in *.
    simpl in *.

    repeat apply f_equal2; auto.

    rewrite Rmult_1_l.

    apply finite_sum_eq_proof_irrelevence.
    repeat rewrite map_map.
    apply map_ext.
    induction a.
    simpl.
    apply f_equal2; auto.

    replace (gen_unfixed (gen d rho) d rho r b) with (gen (S d) rho r b) by tauto.

    (* liftedD should return a superset of the existing rules *)
    Lemma liftedD_preserves {NT} (e : Expr NT) (rho : rules NT) (s : string) (d : nat) :
      gen d rho e s = gen d (liftedD rho) (exprMap justNT e) s.
    Proof.
      revert s.
      induction e, d using (pcfg_super_rect rho);
        unfold exprMap;
        fold @exprMap;
        intros;
        auto;
        try (induction d; tauto).
      +
        induction d; [tauto|].
        simpl in *.
        rewrite IHd, IHd0.
        auto.
      +
        induction d; [tauto|].
        simpl in *.
        apply f_equal.
        apply map_ext.
        induction a.
        apply f_equal2; auto.
      +
        simpl.
        rewrite IHd.
        auto.
    Qed.

    rewrite (liftedD_preserves r rho b (S d)).
    simpl.
    auto.
  Qed.

  (* glue all the cases together *)
  Lemma eD_comutes {NT} e (rho : rules NT) d : eD_gen_commute_defn NT d rho e.
  Proof.
    induction e, d using (pcfg_super_rect rho).
    +
      auto.
    +
      apply emp_commutes.
    +
      apply eps_commutes.
    +
      apply term_commutes.
    +
      apply U_commutes; auto.
    +
      apply seq_commutes; auto.
    +
      apply IHd.
  Qed.

  Theorem gD_commutes :
    forall {NT} (pg : pcfg NT) (σ : Σ) (s : list Σ) (d : nat),
      NNRr (lD σ (pcfg_gen d pg) s) = NNRr (pcfg_gen d (gD d σ pg) s).
  Proof.
    intros.
    case pg as [e rho].
    unfold pcfg_gen.
    simpl.
    apply eD_comutes.
  Qed.

  Print Assumptions gD_commutes.
End PCFG.

(* --- definitions complete, examples and scratch space below --- *)

Inductive aΣ := Σx.
Module aPCFG_params <: PCFG_params.
  Definition Σ := aΣ.
  Definition Σ_dec : dec_def Σ.
    unfold dec_def.
    decide equality.
  Defined.
End aPCFG_params.
Module aPCFG := PCFG aPCFG_params.
Import aPCFG.

Print Assumptions gD_commutes.

Inductive NT := SS.
Definition NT_dec : dec_def NT.
  unfold dec_def.
  decide equality.
Defined.

Definition prod_start : Expr NT := nonterm SS.
Definition prod_1 : Expr NT := nonterm SS · nonterm SS.
Definition prod_2 : Expr NT := nonterm SS · term Σx.
Definition prod_3 : Expr NT := ε.

Program Definition NNR_1_3 := @mkNNR (1/3) _.
Next Obligation.
  SearchPattern (_ * _ <= _ * _ -> _ <= _).
  apply (Rmult_le_reg_l 3); fourier.
Defined.

Fixpoint list_U {NT} (m : list (Expr NT * NNR)) : Expr NT :=
  match m with
    | nil => ∅
    | (r, p) :: m' => U (r, constMono p) (list_U m', constMono NNR_1)
  end.

Definition rho : rules NT :=
  (fun nt =>
     match nt with
       | SS =>
         list_U
           ((prod_1, NNR_1_3) ::
            (prod_2, NNR_1_3) ::
            (prod_3, NNR_1_3) :: nil)
     end).

Definition g : pcfg NT := mkPcfg rho (rho SS).

(* scratch computations *)

Lemma computation a :
  let d := 2%nat in
  let (g', e) := (gD d Σx g) in
  a = NNRr (gen d g' e nil).

  compute; field_simplify.
Abort.

Lemma computation :
  let d := 2%nat in
  NNRr (lD Σx (gen d rho (rho SS)) nil)
  = NNRr (pcfg_gen d (gD d Σx g) nil).
Proof.
  compute; field_simplify.
Abort.
