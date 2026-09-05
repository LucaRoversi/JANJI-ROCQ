(** * The Hard-KLAIM type-and-effect system

    The judgement below encodes T-Obs, T-Derive, T-Propose, T-Commit,
    T-Call, and T-Seq.  Every atomic rule carries the closed admissibility
    check for the extended trace.  In T-Seq the second premise receives the
    complete prefix and updated dynamic environment produced by the first. *)

(** ** Correspondence with [GianluigiFerrari_tribute_2026.pdf]

    The constructors of [typed_atomic] map one-for-one to T-Obs, T-Derive,
    T-Propose, T-Commit, and T-Call in Section 6.1 (PDF pp. 19--20), and
    [typed_program] maps to T-Seq (PDF p. 20).  [obs_fragment] is the
    observation fragment of Definition 9 (PDF p. 16), while [call_guard]
    maps to Definition 17 (PDF p. 20).

    [extends_with] and [names_fresh] implement the simultaneous immutable
    extension described by Definition 8 (PDF p. 15).  [result_bindings],
    [binds_exactly], and [conservative_tool_dependencies] spell out the exact
    output-shape and conservative-source premises summarized below T-Call and
    used explicitly in Appendix B (PDF pp. 20 and 34--35).

    [typing_preserves_admissibility] maps to the first safety property in
    Section 6.2 (PDF pp. 20--21).  The small projection lemmas and the concrete
    list representation of result shapes are proof-assistant details required
    by the mechanization but not stated separately in the paper. *)

From Coq Require Import Lists.List.
From Janji Require Import Prelude Syntax Trace Policy.
Import ListNotations.

(** A dynamic update must describe the entire finite delta.  Besides preserving
    old entries and excluding unlisted target entries, it requires every added
    value name to be globally absent from the source and requires added names
    to be pairwise distinct.  These clauses rule out overwriting and cross-
    context aliases at the typing boundary. *)
Definition extends_with (old new : dynamic_env)
                       (added : list (context * value * ty)) : Prop :=
  Forall
    (fun b => let '(_, y, _) := b in forall q, old q y = None)
    added /\
  NoDup (map (fun b => let '(_, y, _) := b in y) added) /\
  forall q y t,
    new q y = Some t <-> old q y = Some t \/ In (q, y, t) added.

Definition names_fresh (g : static_env) (dlt : dynamic_env)
                       (e : trace) (xs : list value) : Prop :=
  Forall (fun x => static_type g x = None /\
                   (forall q, dlt q x = None) /\ ~ produced e x) xs /\
  NoDup xs.

(** Tool results carry an exact type-shaped binding list.  The relation rules
    out an untyped or extra output binding while retaining the paper's support
    for unit, singleton, and product-shaped result tuples. *)
Inductive result_bindings (q : context) :
    list value -> ty -> list (context * value * ty) -> Prop :=
| ResultBindingsUnit :
    result_bindings q [] TyUnit []
| ResultBindingsSingle : forall y t,
    (match t with TyProduct _ _ | TyUnit => False | _ => True end) ->
    result_bindings q [y] t [(q, y, t)]
| ResultBindingsProduct : forall xs ys tx ty bxs bys,
    result_bindings q xs tx bxs ->
    result_bindings q ys ty bys ->
    result_bindings q (xs ++ ys) (TyProduct tx ty) (bxs ++ bys).

(** [binds_exactly] strengthens the paper's one-way [binds] check.  Every
    declared result is produced exactly once, and every production target in
    the reported fragment is one of those declared results. *)
Definition binds_exactly (f : fragment) (results : list value) : Prop :=
  binds f results /\
  forall sources y l, In (ECompute sources y l) f -> In y results.

(** Every value supplied to a tool is a potential influence on each produced
    result.  Requiring the complete input tuple in every reported production
    dependency set gives a finite conservative lower bound; a sound schema may
    and should add executable, configuration, or external-state names. *)
Definition conservative_tool_dependencies
           (inputs : list value) (f : fragment) : Prop :=
  forall sources y l,
    In (ECompute sources y l) f -> subset inputs sources.

Definition obs_fragment (y : value) (source delegate_loc : locality) : fragment :=
  if Nat.eqb source delegate_loc
  then [ERead y source]
  else [ERead y source; EExpose y source delegate_loc].

Definition nonproduction_stage dlt e q : Prop :=
  stage_of dlt e q Observe \/ stage_of dlt e q Propose.

Definition call_guard (dlt : dynamic_env) (e : trace) (q : context)
                      (f : fragment) (inputs : list value) : Prop :=
  ((has_act f /\ stage_of dlt e q Commit) \/
   (~ has_act f /\ nonproduction_stage dlt e q)) /\
  no_commit f /\
  subset (proposal_ids f) inputs.

Inductive typed_atomic (g : static_env) (o : oracle)
                       (a : delegate) (delegate_loc q : name) :
                       dynamic_env -> trace -> atomic_action ->
                       trace -> dynamic_env -> Prop :=
| TObserve : forall dlt e y source f t,
    f = obs_fragment y source delegate_loc ->
    has_capability g a CapRead ->
    subset (required_capabilities f)
           (match delegate_caps g a with Some cs => cs | None => [] end) ->
    nonproduction_stage dlt e q ->
    value_has_type g dlt q y t ->
    admissible g o a (e ++ label q f) ->
    typed_atomic g o a delegate_loc q dlt e
      (AObserve y source) (label q f) dlt
| TDerive : forall dlt dlt' e y t sources,
    data_type t ->
    has_capability g a CapDerive ->
    nonproduction_stage dlt e q ->
    names_fresh g dlt e [y] ->
    subset (visible_values g q delegate_loc) sources ->
    admissible g o a (e ++ [(q, ECompute sources y delegate_loc)]) ->
    extends_with dlt dlt' [(q, y, t)] ->
    dlt' q y = Some t ->
    typed_atomic g o a delegate_loc q dlt e
      (ADerive y t sources) [(q, ECompute sources y delegate_loc)] dlt'
| TPropose : forall dlt dlt' e p w d,
    has_capability g a CapPropose ->
    nonproduction_stage dlt e q ->
    names_fresh g dlt e [p] ->
    value_has_type g dlt q d (TyPatch w) ->
    o g e (QPropose a w d delegate_loc) = true ->
    admissible g o a (e ++ [(q, ECompute [w; d] p delegate_loc)]) ->
    extends_with dlt dlt' [(q, p, TyProposal w d)] ->
    dlt' q p = Some (TyProposal w d) ->
    typed_atomic g o a delegate_loc q dlt e
      (APropose p w d) [(q, ECompute [w; d] p delegate_loc)] dlt'
| TCommit : forall dlt e p w d alpha,
    has_capability g a CapCommit ->
    stage_of dlt e q Propose ->
    dlt q p = Some (TyProposal w d) ->
    proposed e q p w d ->
    (** The general value-typing judgment also admits declared or previously
        stored values.  Commitment needs the stronger deployment fact that the
        authoritative verifier accepted this evidence for this exact tuple. *)
    evidence_ok g alpha a q p w d = true ->
    value_has_type g dlt q alpha (TyApproval a q p w d) ->
    admissible g o a (e ++ [(q, ECommit p w d alpha delegate_loc)]) ->
    typed_atomic g o a delegate_loc q dlt e
      (ACommit p w d alpha) [(q, ECommit p w d alpha delegate_loc)] dlt
| TCall : forall dlt dlt' e ys t xs eta reported td out_bindings,
    tool_decl g t = Some td ->
    values_have_type g dlt q xs (input_type td) ->
    names_fresh g dlt e ys ->
    result_bindings q ys (output_type td) out_bindings ->
    In reported (effect_schema td xs ys eta) ->
    o g e (QCall a t delegate_loc (tool_locality td) eta) = true ->
    (forall f, In f (effect_schema td xs ys eta) ->
       admissible g o a (e ++ label q f) /\
       subset (required_capabilities f)
              (match delegate_caps g a with Some cs => cs | None => [] end) /\
       call_guard dlt e q f xs /\
       binds_exactly f ys /\
       conservative_tool_dependencies xs f) ->
    extends_with dlt dlt' out_bindings ->
    typed_atomic g o a delegate_loc q dlt e
      (ACall ys t xs eta reported) (label q reported) dlt'.

Inductive typed_program (g : static_env) (o : oracle)
                        (a : delegate) (delegate_loc q : name) :
                        dynamic_env -> trace -> program ->
                        trace -> dynamic_env -> Prop :=
| TPAtomic : forall dlt dlt' e action f,
    typed_atomic g o a delegate_loc q dlt e action f dlt' ->
    typed_program g o a delegate_loc q dlt e [action] f dlt'
| TPSeq : forall d0 d1 d2 e a1 rest f1 f2,
    typed_atomic g o a delegate_loc q d0 e a1 f1 d1 ->
    typed_program g o a delegate_loc q d1 (e ++ f1) rest f2 d2 ->
    typed_program g o a delegate_loc q d0 e (a1 :: rest) (f1 ++ f2) d2.

Lemma typed_atomic_admissible g o a ld q dlt e action f dlt' :
  typed_atomic g o a ld q dlt e action f dlt' ->
  admissible g o a (e ++ f).
Proof.
  intros H; inversion H; subst; auto.
  match goal with
  | Hall : forall f, In f _ -> _ |- _ =>
      specialize (Hall reported ltac:(assumption)); tauto
  end.
Qed.

Theorem typing_preserves_admissibility g o a ld q dlt e prog f dlt' :
  typed_program g o a ld q dlt e prog f dlt' ->
  admissible g o a (e ++ f).
Proof.
  intros Htyping; induction Htyping.
  - now apply typed_atomic_admissible in H.
  - specialize (IHHtyping).
    rewrite <- app_assoc in IHHtyping. exact IHHtyping.
Qed.
