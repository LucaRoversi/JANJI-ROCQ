(** * Operational semantics at the workflow boundary

    The semantics does not model internal LLM reasoning or reproduce the
    workflow engine.  It records model-mediated boundary actions, attested
    tool calls, security-relevant runtime events, and protection-irrelevant
    internal events.  The exact call tuple [t,x,ys,eta] occurs in typing,
    invocation, and the transition label. *)

(** ** Correspondence with [GianluigiFerrari_tribute_2026.pdf]

    [runtime_event], typed runtime outputs, and [lift] map to the runtime
    abstraction and SWIRL lifting in Section 7.1 (PDF pp. 21--22, equation
    (10)).  [configuration] maps to Definition 18 (PDF p. 22).

    The constructors of [step] map one-for-one to R-Observe, R-Derive,
    R-Propose, R-Commit, R-Call, R-Runtime, and R-Internal in Sections
    7.2--7.3 (PDF pp. 22--23).  [boundary_label] and the exact history view map
    to Strengthened boundary transition, Definition 19 (PDF p. 23).
    [invocation_semantics], [runtime_semantics], [internal_semantics], and
    [runtime_environment_update] are the abstract trusted interfaces described
    around those rules.

    [reaches] and [reachable_trace_admissible] provide the core finite-step
    bridge later strengthened by Definitions 27--30 (PDF pp. 26--27).
    [faithful_transition] and [every_step_is_boundary_faithful] map to Boundary
    fidelity in Section 6.2 and to Exact boundary fidelity, Definition 25
    (PDF pp. 21 and 25).  Binding projections and constructor-specific helper
    lemmas are technical proof support. *)

From Coq Require Import Lists.List.
From Janji Require Import Prelude Syntax Trace Policy Typing.
Import ListNotations.

Definition runtime_state := nat.

(** Runtime results carry their authoritative types across the trusted runtime
    boundary.  A bare list of names is insufficient to construct the exact
    dynamic-environment extension required by the confinement proof. *)
Definition runtime_output := (value * ty)%type.

Definition runtime_output_value (out : runtime_output) : value := fst out.
Definition runtime_output_type (out : runtime_output) : ty := snd out.

Inductive runtime_event :=
| RuntimeExec (q : context) (p : proposal) (w : workflow) (d : patch)
              (payload : value) (l : locality)
              (dependencies : list value) (outputs : list runtime_output)
| RuntimeSend (q : context) (p : proposal) (w : workflow) (d : patch)
              (payload : value) (from to : locality).

Definition runtime_context (mu : runtime_event) : context :=
  match mu with RuntimeExec q _ _ _ _ _ _ _ | RuntimeSend q _ _ _ _ _ _ => q end.

Definition runtime_proposal (mu : runtime_event) : proposal :=
  match mu with RuntimeExec _ p _ _ _ _ _ _ | RuntimeSend _ p _ _ _ _ _ => p end.

Definition runtime_workflow (mu : runtime_event) : workflow :=
  match mu with RuntimeExec _ _ w _ _ _ _ _ | RuntimeSend _ _ w _ _ _ _ => w end.

Definition runtime_patch (mu : runtime_event) : patch :=
  match mu with RuntimeExec _ _ _ d _ _ _ _ | RuntimeSend _ _ _ d _ _ _ => d end.

Definition runtime_outputs (mu : runtime_event) : list value :=
  match mu with
  | RuntimeExec _ _ _ _ _ _ _ outputs => map runtime_output_value outputs
  | RuntimeSend _ _ _ _ _ _ _ => []
  end.

Fixpoint bind_runtime_outputs
         (q : context) (outputs : list runtime_output) :
         list (context * value * ty) :=
  match outputs with
  | [] => []
  | out :: rest =>
      (q, runtime_output_value out, runtime_output_type out) ::
      bind_runtime_outputs q rest
  end.

(** The exact runtime binding delta is empty for a transfer and is obtained by
    pairing every execution result with its event context and attested type. *)
Definition runtime_output_bindings
           (mu : runtime_event) : list (context * value * ty) :=
  match mu with
  | RuntimeExec q _ _ _ _ _ _ outputs => bind_runtime_outputs q outputs
  | RuntimeSend _ _ _ _ _ _ _ => []
  end.

Fixpoint compute_outputs
         (deps : list value) (outputs : list runtime_output)
         (l : locality) : fragment :=
  match outputs with
  | [] => []
  | out :: rest =>
      ECompute deps (runtime_output_value out) l ::
      compute_outputs deps rest l
  end.

(** Equation (10): an execution is lifted to the exact production action and
    conservative output dependencies; a send is lifted to one exposure. *)
Definition lift (mu : runtime_event) : fragment :=
  match mu with
  | RuntimeExec _ p w d payload l deps outputs =>
      EAct p Execute w d payload l :: compute_outputs deps outputs l
  | RuntimeSend _ _ _ _ payload l1 l2 => [EExpose payload l1 l2]
  end.

Record configuration := {
  cfg_runtime : runtime_state;
  cfg_delegate : delegate;
  cfg_locality : locality;
  cfg_dynamic : dynamic_env;
  cfg_trace : trace
}.

Inductive boundary_label :=
| LObserve (q : context) (y : value) (source : locality)
| LDerive (q : context) (y : value) (sources : list value)
| LPropose (q : context) (p : proposal) (d : patch)
| LCommit (q : context) (p : proposal) (alpha : approval)
| LCall (q : context) (t : tool) (inputs results : list value)
        (eta : metadata) (reported : fragment)
| LRuntime (mu : runtime_event)
| LInternal (tag : nat).

(** Labels identify the exact binding list introduced at the boundary.
    Derivation and proposal labels omit types in the paper syntax, so the
    relation records the type supplied by their typing derivation.  Tool labels
    use the type-shaped binding relation, while runtime labels use the typed
    result tuple carried by the trusted runtime event. *)
Inductive label_output_bindings :
    boundary_label -> list (context * value * ty) -> Prop :=
| LabelOutputsObserve : forall q y source,
    label_output_bindings (LObserve q y source) []
| LabelOutputsDerive : forall q y sources t,
    label_output_bindings (LDerive q y sources) [(q, y, t)]
| LabelOutputsPropose : forall q p w d,
    label_output_bindings (LPropose q p d) [(q, p, TyProposal w d)]
| LabelOutputsCommit : forall q p alpha,
    label_output_bindings (LCommit q p alpha) []
| LabelOutputsCall : forall q t inputs results eta reported output_ty bindings,
    result_bindings q results output_ty bindings ->
    label_output_bindings
      (LCall q t inputs results eta reported) bindings
| LabelOutputsRuntime : forall mu,
    label_output_bindings (LRuntime mu) (runtime_output_bindings mu)
| LabelOutputsInternal : forall tag,
    label_output_bindings (LInternal tag) [].

Definition invocation_semantics :=
  runtime_state -> tool -> list value -> list value -> metadata ->
  fragment -> runtime_state -> Prop.

Definition runtime_semantics :=
  runtime_state -> runtime_event -> runtime_state -> Prop.

Definition internal_semantics :=
  runtime_state -> nat -> runtime_state -> Prop.

(** Runtime execution extends the environment with precisely its typed output
    tuple.  The output names are fresh from both environments and trace, and
    their types are ordinary data types.  A transfer introduces no name and
    therefore leaves the dynamic environment definitionally unchanged. *)
Definition runtime_environment_update
           (g : static_env) (dlt : dynamic_env) (e : trace)
           (mu : runtime_event) (dlt' : dynamic_env) : Prop :=
  match mu with
  | RuntimeExec _ _ _ _ _ _ _ outputs =>
      names_fresh g dlt e (map runtime_output_value outputs) /\
      Forall (fun out => data_type (runtime_output_type out)) outputs /\
      extends_with dlt dlt' (runtime_output_bindings mu)
  | RuntimeSend _ _ _ _ _ _ _ => dlt' = dlt
  end.

Inductive step (g : static_env) (o : oracle)
               (invoke : invocation_semantics)
               (run : runtime_semantics)
               (internal : internal_semantics) :
               configuration -> boundary_label -> configuration -> Prop :=
| RObserve : forall r a ld dlt e q y source f dlt',
    typed_atomic g o a ld q dlt e (AObserve y source) f dlt' ->
    step g o invoke run internal
      {| cfg_runtime := r; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt; cfg_trace := e |}
      (LObserve q y source)
      {| cfg_runtime := r; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt'; cfg_trace := e ++ f |}
| RDerive : forall r a ld dlt e q y t sources f dlt',
    typed_atomic g o a ld q dlt e (ADerive y t sources) f dlt' ->
    step g o invoke run internal
      {| cfg_runtime := r; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt; cfg_trace := e |}
      (LDerive q y sources)
      {| cfg_runtime := r; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt'; cfg_trace := e ++ f |}
| RPropose : forall r a ld dlt e q p w d f dlt',
    typed_atomic g o a ld q dlt e (APropose p w d) f dlt' ->
    step g o invoke run internal
      {| cfg_runtime := r; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt; cfg_trace := e |}
      (LPropose q p d)
      {| cfg_runtime := r; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt'; cfg_trace := e ++ f |}
| RCommit : forall r a ld dlt e q p w d alpha f dlt',
    typed_atomic g o a ld q dlt e (ACommit p w d alpha) f dlt' ->
    step g o invoke run internal
      {| cfg_runtime := r; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt; cfg_trace := e |}
      (LCommit q p alpha)
      {| cfg_runtime := r; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt'; cfg_trace := e ++ f |}
| RCall : forall r r' a ld dlt e q ys t xs eta reported dlt',
    typed_atomic g o a ld q dlt e (ACall ys t xs eta reported)
                 (label q reported) dlt' ->
    invoke r t xs ys eta reported r' ->
    call_guard dlt e q reported xs ->
    step g o invoke run internal
      {| cfg_runtime := r; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt; cfg_trace := e |}
      (LCall q t xs ys eta reported)
      {| cfg_runtime := r'; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt'; cfg_trace := e ++ label q reported |}
| RRuntime : forall r r' a ld dlt dlt' e mu alpha lc,
    run r mu r' ->
    stage_of dlt e (runtime_context mu) ExecuteStage ->
    In (runtime_context mu,
        ECommit (runtime_proposal mu) (runtime_workflow mu)
                (runtime_patch mu) alpha lc) e ->
    no_commit (lift mu) ->
    subset (required_capabilities (lift mu))
           (match delegate_caps g a with Some cs => cs | None => [] end) ->
    runtime_environment_update g dlt e mu dlt' ->
    admissible g o a (e ++ label (runtime_context mu) (lift mu)) ->
    step g o invoke run internal
      {| cfg_runtime := r; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt; cfg_trace := e |}
      (LRuntime mu)
      {| cfg_runtime := r'; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt';
         cfg_trace := e ++ label (runtime_context mu) (lift mu) |}
| RInternal : forall r r' a ld dlt e tag,
    internal r tag r' ->
    step g o invoke run internal
      {| cfg_runtime := r; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt; cfg_trace := e |}
      (LInternal tag)
      {| cfg_runtime := r'; cfg_delegate := a; cfg_locality := ld;
         cfg_dynamic := dlt; cfg_trace := e |}.

Inductive reaches g o invoke run internal (initial : configuration) :
                  list boundary_label -> configuration -> Prop :=
| ReachesRefl : reaches g o invoke run internal initial [] initial
| ReachesStep : forall labels c1 lab c2,
    reaches g o invoke run internal initial labels c1 ->
    step g o invoke run internal c1 lab c2 ->
    reaches g o invoke run internal initial (labels ++ [lab]) c2.

Lemma step_preserves_admissibility g o invoke run internal c lab c' :
  admissible g o (cfg_delegate c) (cfg_trace c) ->
  step g o invoke run internal c lab c' ->
  admissible g o (cfg_delegate c') (cfg_trace c').
Proof.
  intros Hadm Hstep; inversion Hstep; subst; simpl in *;
    try (eapply typed_atomic_admissible; eassumption);
    assumption.
Qed.

Theorem reachable_trace_admissible g o invoke run internal c0 labels c :
  cfg_trace c0 = [] ->
  reaches g o invoke run internal c0 labels c ->
  admissible g o (cfg_delegate c) (cfg_trace c).
Proof.
  intros Hempty Hreach; induction Hreach.
  - rewrite Hempty; apply admissible_nil.
  - eapply step_preserves_admissibility; eauto.
Qed.

(** Boundary fidelity is a property of labelled transitions. *)
Definition faithful_transition (invoke : invocation_semantics)
              (c : configuration) (lab : boundary_label)
              (c' : configuration) : Prop :=
  match lab with
  | LCall q t xs ys eta f =>
      invoke (cfg_runtime c) t xs ys eta f (cfg_runtime c') /\
      (has_act f -> stage_of (cfg_dynamic c) (cfg_trace c) q Commit)
  | LRuntime mu =>
      stage_of (cfg_dynamic c) (cfg_trace c)
               (runtime_context mu) ExecuteStage
  | _ => True
  end.

Lemma call_guard_production_stage dlt e q f inputs :
  call_guard dlt e q f inputs ->
  has_act f ->
  stage_of dlt e q Commit.
Proof.
  intros [[[Hact Hstage] | [Hnoact Hstage]] [Hnocommit Hpids]] Hhas.
  - exact Hstage.
  - contradiction.
Qed.

Theorem every_step_is_boundary_faithful g o invoke run internal c lab c' :
  step g o invoke run internal c lab c' ->
  faithful_transition invoke c lab c'.
Proof.
  intros H; inversion H; subst; simpl.
  all: try exact I.
  - split; [assumption |].
    eapply call_guard_production_stage; eassumption.
  - assumption.
Qed.
