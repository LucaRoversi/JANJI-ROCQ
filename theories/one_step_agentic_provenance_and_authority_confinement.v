(** * One-step agentic provenance-and-authority confinement

    This module proves one-step confinement from origins, exact dynamic
    extension, configuration well-formedness, monotone protocol stages, single
    assignment, unique production, conservative provenance, exact
    proposal--approval--commitment binding, capability non-amplification,
    source-closed exposure, and boundary fidelity. *)

(** ** Correspondence with [GianluigiFerrari_tribute_2026.pdf]

    This file is the detailed mechanization behind Section 7.4.1 (physical PDF
    pp. 24--25).  Its numbered groups correspond at theorem-family granularity:

    - Group 1 corresponds to Strengthened boundary transition, Origins, and Complete
      well-formedness (Definitions 19, 20, and 26);
    - Group 2 corresponds to Proposition 1, deterministic and monotone stage
      reconstruction, and to the first conclusion of Theorem 1;
    - Group 3 corresponds to Proposition 2, single assignment and unique production,
      Exact production delta (Definition 21), and the corresponding conclusions
      of Theorem 1;
    - Groups 4--8 correspond respectively to Conservative provenance (Definition 20),
      Exact proposal--approval--commitment binding (Definition 22), Capability
      non-amplification (Definition 23), Source-closed exposure (Definition 24),
      and Exact boundary fidelity (Definition 25);
    - Group 9, headed by [hard_klaim_one_step_confinement], corresponds to Theorem 1,
      One-step provenance-and-authority confinement (PDF p. 25).

    The many auxiliary records, inversion lemmas, exact-list decompositions,
    and preservation corollaries expose obligations that the paper compresses
    into the Proof justification paragraph on PDF p. 25.  Those proof objects
    support the displayed definitions and theorem but have no separately named
    paper counterparts. *)

From Coq Require Import Lists.List Bool.Bool Arith.PeanoNat.
From Janji Require Import Prelude Syntax Trace Policy Typing Semantics.
Import ListNotations.

Set Implicit Arguments.

(** ** Group 1. State required by the confinement theorem *)

(** A security proof must distinguish a value produced by the model from a
    value returned by a tool or by the workflow runtime.  The distinction does
    not expose the internal reasoning of the model.  It records which trusted
    boundary rule introduced the name and therefore which provenance premise
    was responsible for its dependency set.  A proposal has its own origin
    because it is a protocol witness rather than an ordinary data result. *)
Inductive value_origin :=
| OriginModel (q : context)
| OriginTool (q : context) (t : tool) (eta : metadata)
| OriginRuntime (q : context) (mu : runtime_event)
| OriginProposal (q : context).

(** [runtime_outputs], defined with the operational boundary event, projects
    the names of typed execution results.  Transfers return the empty list and
    therefore preserve the identity of the transferred value. *)

(** [label_introduces lab q y o] is the local evidence that boundary label
    [lab] introduced [y] in context [q] with origin [o].  Membership in result
    tuples is explicit because one tool or runtime step may return several
    fresh values. *)
Inductive label_introduces :
    boundary_label -> context -> value -> value_origin -> Prop :=
| IntroducesModel : forall q y sources,
    label_introduces (LDerive q y sources) q y (OriginModel q)
| IntroducesTool : forall q t inputs results eta fragment y,
    In y results ->
    label_introduces (LCall q t inputs results eta fragment)
                     q y (OriginTool q t eta)
| IntroducesRuntime : forall mu y,
    In y (runtime_outputs mu) ->
    label_introduces (LRuntime mu) (runtime_context mu) y
                     (OriginRuntime (runtime_context mu) mu)
| IntroducesProposal : forall q p d,
    label_introduces (LPropose q p d) q p (OriginProposal q).

(** An origin is part of the execution history only when the corresponding
    boundary label actually occurs in that history. *)
Definition has_origin (history : list boundary_label)
                      (q : context) (y : value) (o : value_origin) : Prop :=
  exists lab, In lab history /\ label_introduces lab q y o.

(** Dynamic names are immutable identities.  Hence a well-formed history must
    assign one boundary origin to a dynamic name, not one origin per use. *)
Definition has_unique_origin (history : list boundary_label)
                             (q : context) (y : value) : Prop :=
  exists o,
    has_origin history q y o /\
    forall q' o', has_origin history q' y o' -> q' = q /\ o' = o.

(** Bindings are written as triples because an atomic transition may introduce
    a tuple of results simultaneously. *)
Definition dynamic_binding := (context * value * ty)%type.

Definition binding_context (b : dynamic_binding) : context :=
  let '(q, _, _) := b in q.

Definition binding_value (b : dynamic_binding) : value :=
  let '(_, y, _) := b in y.

Definition binding_type (b : dynamic_binding) : ty :=
  let '(_, _, t) := b in t.

(** [exact_dynamic_extension old new added] excludes underspecified updates.
    Old bindings are preserved, each added name was globally absent from the
    old environment, added names are pairwise distinct, and the bindings of
    [new] are exactly the union of the old bindings and [added].  In particular,
    [new] cannot contain an unrelated binding chosen by the operational rule. *)
Definition exact_dynamic_extension
           (old new : dynamic_env) (added : list dynamic_binding) : Prop :=
  Forall
    (fun b => forall q, old q (binding_value b) = None)
    added /\
  NoDup (map binding_value added) /\
  forall q y t,
    new q y = Some t <-> old q y = Some t \/ In (q, y, t) added.

(** The typing judgement now exposes the same four clauses through
    [extends_with].  This equivalence closes the former gap between a typed
    output update and the exact extension consumed by the confinement proof. *)
Lemma extends_with_is_exact_dynamic_extension old new added :
  extends_with old new added ->
  exact_dynamic_extension old new added.
Proof.
  intros [Hfresh [Hdistinct Hexact]].
  split.
  - eapply Forall_impl; [| exact Hfresh].
    intros [[q y] t] Hnone; exact Hnone.
  - split; [exact Hdistinct | exact Hexact].
Qed.

Lemma exact_extension_preserves_old old new added :
  exact_dynamic_extension old new added ->
  forall q y t, old q y = Some t -> new q y = Some t.
Proof.
  intros [_ [_ Hexact]] q y t Hold.
  apply Hexact; auto.
Qed.

Lemma exact_extension_contains_added old new added :
  exact_dynamic_extension old new added ->
  forall q y t, In (q, y, t) added -> new q y = Some t.
Proof.
  intros [_ [_ Hexact]] q y t Hadd.
  apply Hexact; auto.
Qed.

Lemma exact_extension_has_no_other_bindings old new added :
  exact_dynamic_extension old new added ->
  forall q y t,
    new q y = Some t -> old q y = Some t \/ In (q, y, t) added.
Proof.
  intros [_ [_ Hexact]] q y t Hnew.
  now apply Hexact.
Qed.

Lemma exact_extension_added_names_are_fresh old new added :
  exact_dynamic_extension old new added ->
  forall b q, In b added -> old q (binding_value b) = None.
Proof.
  intros [Hfresh _] b q Hin.
  apply Forall_forall with (x := b) in Hfresh; auto.
Qed.

Lemma exact_extension_added_names_are_distinct old new added :
  exact_dynamic_extension old new added -> NoDup (map binding_value added).
Proof. intros [_ [Hdistinct _]]; exact Hdistinct. Qed.

(** The paper permits an active context with no dynamic values.  A function
    [context -> value -> option ty] cannot represent that distinction by
    itself, because an inactive context and an active empty context both map
    every name to [None].  The strengthened configuration therefore stores the
    finite active-context set and the boundary-label history explicitly. *)
Record agentic_configuration := {
  agentic_core : configuration;
  active_contexts : list context;
  boundary_history : list boundary_label
}.

Definition active_context (c : agentic_configuration) (q : context) : Prop :=
  In q (active_contexts c).

Definition context_has_no_values
           (c : agentic_configuration) (q : context) : Prop :=
  forall y, cfg_dynamic (agentic_core c) q y = None.

(** A protocol stage is meaningful only for an active context.  This wrapper
    supplies the activity premise that is intentionally absent from the raw
    trace projection [stage_of]. *)
Definition active_stage (c : agentic_configuration)
                        (q : context) (s : stage) : Prop :=
  active_context c q /\
  stage_of (cfg_dynamic (agentic_core c)) (cfg_trace (agentic_core c)) q s.

Lemma active_context_dec c q :
  {active_context c q} + {~ active_context c q}.
Proof.
  unfold active_context; apply in_dec; apply Nat.eq_dec.
Qed.

(** The context carried by a boundary label is available without inspecting
    the runtime state.  Internal labels have no delegation context. *)
Definition label_context (lab : boundary_label) : option context :=
  match lab with
  | LObserve q _ _ => Some q
  | LDerive q _ _ => Some q
  | LPropose q _ _ => Some q
  | LCommit q _ _ => Some q
  | LCall q _ _ _ _ _ => Some q
  | LRuntime mu => Some (runtime_context mu)
  | LInternal _ => None
  end.

(** Locality declarations are checked for every protection-relevant effect.
    An exposure mentions two protection domains; all other effects mention the
    locality at which the event takes place. *)
Definition effect_localities (eff : effect) : list locality :=
  match eff with
  | ERead _ l => [l]
  | ECompute _ _ l => [l]
  | ECommit _ _ _ _ l => [l]
  | EAct _ _ _ _ _ l => [l]
  | EExpose _ l1 l2 => [l1; l2]
  end.

Definition trace_uses_declared_localities
           (g : static_env) (e : trace) : Prop :=
  forall q eff,
    In (q, eff) e ->
    Forall (fun l => locality_decl g l = true) (effect_localities eff).

(** A value name is global even though its binding is indexed by a delegation
    context.  This condition prevents the same immutable name from denoting
    different values in two contexts. *)
Definition dynamic_names_are_global
           (dlt : dynamic_env) : Prop :=
  forall q1 q2 y t1 t2,
    dlt q1 y = Some t1 ->
    dlt q2 y = Some t2 ->
    q1 = q2 /\ t1 = t2.

(** Dynamic names must not alias authoritative static values or names with an
    initial placement.  Otherwise freshness of a produced value would depend
    on which environment was consulted. *)
Definition dynamic_names_are_fresh_from_static
           (g : static_env) (dlt : dynamic_env) : Prop :=
  forall q y t,
    dlt q y = Some t ->
    static_type g y = None /\
    forall l, initial_placement g y l = false.

(** A dynamic name has a unique producing [Compute] event.  The quantification
    over all contexts makes uniqueness global, matching the global freshness
    condition imposed when names are introduced. *)
Definition has_unique_producer
           (e : trace) (q : context) (y : value) : Prop :=
  exists sources l,
    In (q, ECompute sources y l) e /\
    forall q' sources' l',
      In (q', ECompute sources' y l') e ->
      q' = q /\ sources' = sources /\ l' = l.

(** Proposal bindings are persistent protocol evidence.  They are sound only
    when the trace contains the computation that named the immutable proposal
    from the workflow version and patch. *)
Definition proposal_bindings_have_provenance
           (dlt : dynamic_env) (e : trace) : Prop :=
  forall q p w d,
    dlt q p = Some (TyProposal w d) -> proposed e q p w d.

(** A commitment is consistent when its proposal binding still contains the
    same workflow version and patch, its evidence verifies for the same
    delegate and context, and the proposal-producing event occurs earlier in
    the trace. *)
Definition commitments_are_consistent
           (g : static_env) (c : configuration) : Prop :=
  forall q p w d alpha lc,
    In (q, ECommit p w d alpha lc) (cfg_trace c) ->
    cfg_dynamic c q p = Some (TyProposal w d) /\
    evidence_ok g alpha (cfg_delegate c) q p w d = true /\
    exists lp,
      occurs_before (q, ECompute [w; d] p lp)
                    (q, ECommit p w d alpha lc) (cfg_trace c).

Definition is_production_call (q : context) (lab : boundary_label) : Prop :=
  exists t inputs results eta fragment,
    lab = LCall q t inputs results eta fragment /\ has_act fragment.

(** Once a context has entered execution, exactly one model-mediated call is
    responsible for the transition from commitment to execution.  Runtime
    events belonging to the submitted run do not count as additional calls. *)
Definition has_unique_production_call
           (history : list boundary_label) (q : context) : Prop :=
  exists lab,
    In lab history /\
    is_production_call q lab /\
    forall lab',
      In lab' history -> is_production_call q lab' -> lab' = lab.

(** An execution effect is justified by the exact commitment already present
    in its trace prefix.  Matching all of [p], [w], and [d] rules out replacing
    an approved patch or workflow version between commitment and use. *)
Definition production_actions_have_prior_commitment (e : trace) : Prop :=
  forall q p k w d payload l,
    In (q, EAct p k w d payload l) e ->
    exists alpha lc,
      occurs_before (q, ECommit p w d alpha lc)
                    (q, EAct p k w d payload l) e.

(** The following record is the invariant preserved by the one-step theorem.
    It implements Complete well-formedness, Definition 26 in Section 7.4.1 of
    the final paper (PDF p. 25), including the representation conditions needed
    to state it without ambiguity: declared localities, explicit context
    activity, global dynamic names, and unique boundary origins. *)
Record well_formed_configuration
       (g : static_env) (c : agentic_configuration) : Prop := {
  wf_active_contexts_distinct :
    NoDup (active_contexts c);

  wf_delegate_declared :
    exists caps, delegate_caps g (cfg_delegate (agentic_core c)) = Some caps;

  wf_localities_declared :
    trace_uses_declared_localities g (cfg_trace (agentic_core c));

  wf_dynamic_contexts_active :
    forall q y t,
      cfg_dynamic (agentic_core c) q y = Some t -> active_context c q;

  wf_trace_contexts_active :
    forall q eff,
      In (q, eff) (cfg_trace (agentic_core c)) -> active_context c q;

  wf_history_contexts_active :
    forall lab q,
      In lab (boundary_history c) ->
      label_context lab = Some q -> active_context c q;

  wf_dynamic_names_global :
    dynamic_names_are_global (cfg_dynamic (agentic_core c));

  wf_dynamic_names_fresh :
    dynamic_names_are_fresh_from_static
      g (cfg_dynamic (agentic_core c));

  wf_dynamic_names_produced_once :
    forall q y t,
      cfg_dynamic (agentic_core c) q y = Some t ->
      has_unique_producer (cfg_trace (agentic_core c)) q y;

  wf_dynamic_names_have_one_origin :
    forall q y t,
      cfg_dynamic (agentic_core c) q y = Some t ->
      has_unique_origin (boundary_history c) q y;

  wf_proposal_bindings :
    proposal_bindings_have_provenance
      (cfg_dynamic (agentic_core c)) (cfg_trace (agentic_core c));

  wf_commitments :
    commitments_are_consistent g (agentic_core c);

  wf_actions_follow_commitment :
    production_actions_have_prior_commitment
      (cfg_trace (agentic_core c));

  wf_execution_has_one_call :
    forall q,
      has_context_act (cfg_trace (agentic_core c)) q ->
      has_unique_production_call (boundary_history c) q
}.

(** An initial boundary configuration has no effect or boundary history, and
    every initially active context has an empty dynamic environment.  Activity
    is retained explicitly so such a context has derived stage [Observe]
    rather than being confused with an inactive context. *)
Definition initial_agentic_configuration
           (c : agentic_configuration) : Prop :=
  cfg_trace (agentic_core c) = [] /\
  boundary_history c = [] /\
  forall q, active_context c q -> context_has_no_values c q.

Lemma initial_configuration_has_no_origins c :
  initial_agentic_configuration c ->
  forall q y o, ~ has_origin (boundary_history c) q y o.
Proof.
  intros [_ [Hhistory _]] q y o [lab [Hin _]].
  rewrite Hhistory in Hin; inversion Hin.
Qed.

Lemma initial_configuration_has_no_producers c :
  initial_agentic_configuration c ->
  forall y, ~ produced (cfg_trace (agentic_core c)) y.
Proof.
  intros [Htrace _] y Hproduced.
  rewrite Htrace in Hproduced.
  destruct Hproduced as [q' [sources [l Hin]]].
  inversion Hin.
Qed.

(** ** Group 2. Deterministic and monotone protocol stages *)

(** The protocol order records progress rather than numerical time.  Observation
    is the least stage and execution is the greatest.  The definition is given
    by cases because the domain has four elements and no arithmetic encoding is
    needed by the metatheory. *)
Definition stage_le (s1 s2 : stage) : Prop :=
  match s1, s2 with
  | Observe, _ => True
  | Propose, Observe => False
  | Propose, _ => True
  | Commit, Commit => True
  | Commit, ExecuteStage => True
  | Commit, _ => False
  | ExecuteStage, ExecuteStage => True
  | ExecuteStage, _ => False
  end.

Notation "s1 <=s s2" := (stage_le s1 s2) (at level 70).

Lemma stage_le_reflexive : forall s, s <=s s.
Proof. destruct s; simpl; exact I. Qed.

Lemma stage_le_transitive :
  forall s1 s2 s3, s1 <=s s2 -> s2 <=s s3 -> s1 <=s s3.
Proof. destruct s1, s2, s3; simpl; tauto. Qed.

Lemma stage_le_antisymmetric :
  forall s1 s2, s1 <=s s2 -> s2 <=s s1 -> s1 = s2.
Proof. destruct s1, s2; simpl; intuition. Qed.

(** A trace extension appends a finite suffix and does not edit the prefix.
    Naming the suffix is useful in preservation proofs because the precise
    events introduced by one step remain available as a proof object. *)
Definition exact_trace_extension
           (old new added : trace) : Prop :=
  new = old ++ added.

Definition trace_extends (old new : trace) : Prop :=
  exists added, exact_trace_extension old new added.

Lemma exact_trace_extension_preserves_events old new added ev :
  exact_trace_extension old new added ->
  In ev old -> In ev new.
Proof.
  intros Hextension Hin; unfold exact_trace_extension in Hextension.
  subst new; apply in_or_app; auto.
Qed.

Lemma trace_extension_preserves_events old new ev :
  trace_extends old new -> In ev old -> In ev new.
Proof.
  intros [added Hextension] Hin.
  eapply exact_trace_extension_preserves_events; eauto.
Qed.

(** The existential wrapper hides the concrete list of bindings when only
    preservation is relevant.  The underlying relation remains
    [exact_dynamic_extension], so the target environment cannot contain an
    unlisted binding. *)
Definition dynamic_environment_extends
           (old new : dynamic_env) : Prop :=
  exists added, exact_dynamic_extension old new added.

Lemma dynamic_environment_extension_preserves_binding old new q y t :
  dynamic_environment_extends old new ->
  old q y = Some t -> new q y = Some t.
Proof.
  intros [added Hextension] Hold.
  eapply exact_extension_preserves_old; eauto.
Qed.

(** Active contexts grow by an explicit finite suffix.  Requiring the complete
    target list to have no duplicates prevents re-activating an already active
    context under a second list occurrence. *)
Definition exact_active_context_extension
           (old new : agentic_configuration)
           (added : list context) : Prop :=
  active_contexts new = active_contexts old ++ added /\
  NoDup (active_contexts new).

Definition active_contexts_extend
           (old new : agentic_configuration) : Prop :=
  exists added, exact_active_context_extension old new added.

Lemma active_context_extension_preserves_activity old new q :
  active_contexts_extend old new ->
  active_context old q -> active_context new q.
Proof.
  intros [added [Hcontexts Hdistinct]] Hactive.
  unfold active_context in *; rewrite Hcontexts.
  apply in_or_app; auto.
Qed.

(** Stage reconstruction depends on three monotone components: the trace, the
    dynamic environment, and the active-context set.  Runtime state and label
    history do not enter [active_stage].  Delegate and control-locality equality
    ensure that the extension still describes one step of the same delegate. *)
Record stage_state_extension
       (old new : agentic_configuration) : Prop := {
  stage_extension_same_delegate :
    cfg_delegate (agentic_core new) = cfg_delegate (agentic_core old);
  stage_extension_same_locality :
    cfg_locality (agentic_core new) = cfg_locality (agentic_core old);
  stage_extension_trace :
    trace_extends (cfg_trace (agentic_core old))
                  (cfg_trace (agentic_core new));
  stage_extension_dynamic :
    dynamic_environment_extends (cfg_dynamic (agentic_core old))
                                (cfg_dynamic (agentic_core new));
  stage_extension_active :
    active_contexts_extend old new
}.

(** The source configuration is required to satisfy the invariant established
    in point 1.  Target well-formedness is deliberately not assumed: proving it
    will be part of the later one-step confinement theorem. *)
Definition well_formed_exact_stage_extension
           (g : static_env)
           (old new : agentic_configuration) : Prop :=
  well_formed_configuration g old /\ stage_state_extension old new.

Lemma stage_extension_preserves_activity old new q :
  stage_state_extension old new ->
  active_context old q -> active_context new q.
Proof.
  intros Hextension Hactive.
  eapply active_context_extension_preserves_activity; eauto.
  exact (stage_extension_active Hextension).
Qed.

Lemma stage_extension_preserves_context_act old new q :
  stage_state_extension old new ->
  has_context_act (cfg_trace (agentic_core old)) q ->
  has_context_act (cfg_trace (agentic_core new)) q.
Proof.
  intros Hextension [p [k [w [d [y [l Hin]]]]]].
  exists p, k, w, d, y, l.
  eapply trace_extension_preserves_events; eauto.
  exact (stage_extension_trace Hextension).
Qed.

Lemma stage_extension_preserves_context_commit old new q :
  stage_state_extension old new ->
  has_context_commit (cfg_trace (agentic_core old)) q ->
  has_context_commit (cfg_trace (agentic_core new)) q.
Proof.
  intros Hextension [p [w [d [alpha [l Hin]]]]].
  exists p, w, d, alpha, l.
  eapply trace_extension_preserves_events; eauto.
  exact (stage_extension_trace Hextension).
Qed.

Lemma stage_extension_preserves_proposal_binding old new q :
  stage_state_extension old new ->
  has_proposal_binding (cfg_dynamic (agentic_core old)) q ->
  has_proposal_binding (cfg_dynamic (agentic_core new)) q.
Proof.
  intros Hextension [p [w [d Hbinding]]].
  exists p, w, d.
  eapply dynamic_environment_extension_preserves_binding; eauto.
  exact (stage_extension_dynamic Hextension).
Qed.

(** The clauses defining [stage_of] are mutually exclusive: an action
    dominates a commitment, a commitment dominates a proposal binding, and a
    proposal binding dominates observation. *)
Theorem stage_of_deterministic dlt e q s1 s2 :
  stage_of dlt e q s1 ->
  stage_of dlt e q s2 ->
  s1 = s2.
Proof.
  intros H1 H2.
  inversion H1; inversion H2; subst; try reflexivity; contradiction.
Qed.

Theorem active_stage_deterministic c q s1 s2 :
  active_stage c q s1 ->
  active_stage c q s2 ->
  s1 = s2.
Proof.
  intros [_ H1] [_ H2].
  eapply stage_of_deterministic; eauto.
Qed.

(** The following three lemmas isolate the dominance arguments used in the
    monotonicity proof.  They avoid a case analysis on how the later stage was
    derived at every use site. *)
Lemma stage_with_action_is_execute dlt e q s :
  stage_of dlt e q s ->
  has_context_act e q ->
  s = ExecuteStage.
Proof.
  intros Hstage Hact; inversion Hstage; subst; auto; contradiction.
Qed.

Lemma stage_with_commit_is_at_least_commit dlt e q s :
  stage_of dlt e q s ->
  has_context_commit e q ->
  Commit <=s s.
Proof.
  intros Hstage Hcommit; inversion Hstage; subst; simpl; auto; contradiction.
Qed.

Lemma stage_with_proposal_is_at_least_propose dlt e q s :
  stage_of dlt e q s ->
  has_proposal_binding dlt q ->
  Propose <=s s.
Proof.
  intros Hstage Hproposal; inversion Hstage; subst; simpl; auto; contradiction.
Qed.

(** Appending events, preserving dynamic bindings, and retaining context
    activity can only maintain or advance a derived protocol stage.  The
    theorem compares derivable stages rather than computing a stage; it is
    therefore constructive and independent of a finite-map implementation. *)
Theorem active_stage_monotone g old new q s_old s_new :
  well_formed_exact_stage_extension g old new ->
  active_stage old q s_old ->
  active_stage new q s_new ->
  s_old <=s s_new.
Proof.
  intros [_ Hextension] [_ Hold] [_ Hnew].
  inversion Hold; subst.
  - pose proof (stage_extension_preserves_context_act Hextension H) as Hact.
    pose proof (stage_with_action_is_execute Hnew Hact) as ->.
    simpl; exact I.
  - pose proof (stage_extension_preserves_context_commit Hextension H0)
      as Hcommit.
    eapply stage_with_commit_is_at_least_commit; eauto.
  - pose proof (stage_extension_preserves_proposal_binding Hextension H1)
      as Hproposal.
    eapply stage_with_proposal_is_at_least_propose; eauto.
  - destruct s_new; simpl; exact I.
Qed.

(** Activity itself is preserved by the same extension.  This corollary is
    stated separately because later rules will often need activity before they
    need the stage comparison. *)
Corollary well_formed_stage_extension_preserves_activity g old new q :
  well_formed_exact_stage_extension g old new ->
  active_context old q -> active_context new q.
Proof.
  intros [_ Hextension].
  now apply stage_extension_preserves_activity.
Qed.

(** ** Group 3. Single assignment and unique production *)

(** A dynamic environment is a function, so one context cannot return two
    types for the same lookup.  That fact alone is too weak for immutable
    global names: the same value name could still be installed in two distinct
    contexts.  [single_assignment] gives the required global reading. *)
Definition single_assignment (dlt : dynamic_env) : Prop :=
  dynamic_names_are_global dlt.

(** Unique production is stated for every installed dynamic binding.  Keeping
    this predicate separate from the configuration record makes it available
    as the conclusion of a preservation theorem and as a premise of later
    provenance arguments. *)
Definition every_dynamic_binding_has_unique_producer
           (dlt : dynamic_env) (e : trace) : Prop :=
  forall q y t, dlt q y = Some t -> has_unique_producer e q y.

(** A binding and a trace event correspond when the event produces the bound
    name in the binding's context.  Sources and locality remain existential
    here because their exact values are supplied by the boundary rule. *)
Definition binding_has_unique_added_producer
           (added_events : trace) (b : dynamic_binding) : Prop :=
  exists sources l,
    In (binding_context b,
        ECompute sources (binding_value b) l) added_events /\
    forall q' sources' l',
      In (q', ECompute sources' (binding_value b) l') added_events ->
      q' = binding_context b /\ sources' = sources /\ l' = l.

(** The same finite result tuple is viewed once as names reported at the
    boundary and once as typed dynamic bindings.  Both directions are needed:
    one prevents unreported bindings, and the other prevents an unbound
    production event. *)
Definition bindings_match_results
           (q : context) (results : list value)
           (bindings : list dynamic_binding) : Prop :=
  (forall b,
      In b bindings ->
      binding_context b = q /\ In (binding_value b) results) /\
  (forall y,
      In y results ->
      exists t, In (q, y, t) bindings).

Lemma result_bindings_values q results result_ty bindings :
  result_bindings q results result_ty bindings ->
  map binding_value bindings = results.
Proof.
  intros Hbindings; induction Hbindings.
  - reflexivity.
  - reflexivity.
  - change (map binding_value (bxs ++ bys) = xs ++ ys).
    rewrite map_app.
    apply f_equal2; assumption.
Qed.

Lemma result_bindings_contexts q results result_ty bindings :
  result_bindings q results result_ty bindings ->
  Forall (fun b => binding_context b = q) bindings.
Proof.
  intros Hbindings; induction Hbindings; simpl; auto.
  now apply Forall_app.
Qed.

Lemma result_bindings_find_type q results result_ty bindings y :
  result_bindings q results result_ty bindings ->
  In y results ->
  exists t, In (q, y, t) bindings.
Proof.
  intros Hbindings; induction Hbindings; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [-> | Hin]; [eauto | contradiction].
  - apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
    + destruct (IHHbindings1 Hin) as [t Hin_t].
      exists t; apply in_or_app; auto.
    + destruct (IHHbindings2 Hin) as [t Hin_t].
      exists t; apply in_or_app; auto.
Qed.

Lemma result_bindings_match_results q results result_ty bindings :
  result_bindings q results result_ty bindings ->
  bindings_match_results q results bindings.
Proof.
  intros Hbindings; split.
  - intros b Hin; split.
    + pose proof (result_bindings_contexts Hbindings) as Hcontexts.
      now apply Forall_forall with (x := b) in Hcontexts.
    + rewrite <- (result_bindings_values Hbindings).
      now apply in_map.
  - intros y Hin; eapply result_bindings_find_type; eauto.
Qed.

(** Labelling a fragment changes only the context component of each event.
    These two directions allow the fragment-level exactness check to be reused
    for the context-labelled trace suffix. *)
Lemma label_contains_effect q f eff :
  In eff f -> In (q, eff) (label q f).
Proof.
  induction f as [|head rest IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [-> | Hin]; auto.
Qed.

Lemma label_event_inv q q' f eff :
  In (q', eff) (label q f) -> q' = q /\ In eff f.
Proof.
  induction f as [|head rest IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [Hequal | Hin].
    + inversion Hequal; subst; auto.
    + destruct (IH Hin) as [-> Hin']; auto.
Qed.

(** A zero target count excludes every production occurrence for that name.
    The lemma is used below to turn the Boolean-looking count in [binds] into a
    propositional uniqueness result. *)
Lemma target_count_zero_excludes_compute :
  forall f y,
    target_count y f = 0 ->
    forall sources l, ~ In (ECompute sources y l) f.
Proof.
  induction f as [|eff rest IH]; intros y Hzero sources l Hin.
  - inversion Hin.
  - destruct eff as [z loc | sources0 z loc | p w d alpha loc |
                     p k w d payload loc | z from to].
    + simpl in Hzero, Hin; destruct Hin as [Hequal | Hin].
      * discriminate.
      * eapply IH; eauto.
    + simpl in Hzero, Hin.
      destruct (Nat.eqb y z) eqn:Heq.
      * discriminate Hzero.
      * destruct Hin as [Hequal | Hin].
        -- inversion Hequal; subst.
           rewrite Nat.eqb_refl in Heq; discriminate.
        -- eapply IH; eauto.
    + simpl in Hzero, Hin; destruct Hin as [Hequal | Hin].
      * discriminate.
      * eapply IH; eauto.
    + simpl in Hzero, Hin; destruct Hin as [Hequal | Hin].
      * discriminate.
      * eapply IH; eauto.
    + simpl in Hzero, Hin; destruct Hin as [Hequal | Hin].
      * discriminate.
      * eapply IH; eauto.
Qed.

(** A target count of one determines a producer's context-independent event
    data: source list and locality.  Any second event for the same name would
    either contradict the zero count of the remaining suffix or the induction
    hypothesis. *)
Lemma target_count_one_unique :
  forall f y,
    target_count y f = 1 ->
    exists sources l,
      In (ECompute sources y l) f /\
      forall sources' l',
        In (ECompute sources' y l') f ->
        sources' = sources /\ l' = l.
Proof.
  induction f as [|eff rest IH]; intros y Hone.
  - discriminate.
  - destruct eff as [z loc | sources0 z loc | p w d alpha loc |
                     p k w d payload loc | z from to]; simpl in Hone;
      try (destruct (IH y Hone) as [sources [l [Hin Hunique]]];
           exists sources, l; split; [right; exact Hin |];
           intros sources' l' Hin'; simpl in Hin';
           destruct Hin' as [Hequal | Hin'];
           [discriminate | now apply Hunique]).
    destruct (Nat.eqb y z) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst z.
      inversion Hone as [Hrest].
      exists sources0, loc; split; [left; reflexivity |].
      intros sources' l' Hin'; simpl in Hin'.
      destruct Hin' as [Hequal | Hin'].
      * inversion Hequal; subst; auto.
      * exfalso.
        eapply target_count_zero_excludes_compute; eauto.
    + destruct (IH y Hone) as [sources [l [Hin Hunique]]].
      exists sources, l; split; [right; exact Hin |].
      intros sources' l' Hin'; simpl in Hin'.
      destruct Hin' as [Hequal | Hin'].
      * inversion Hequal; subst.
        rewrite Nat.eqb_refl in Heq; discriminate.
      * now apply Hunique.
Qed.

(** Exact fragment binding plus exact result bindings yields one producer for
    every added binding after the fragment is labelled with its context. *)
Lemma matching_binding_has_unique_labelled_producer
      q results bindings f b :
  bindings_match_results q results bindings ->
  binds_exactly f results ->
  In b bindings ->
  binding_has_unique_added_producer (label q f) b.
Proof.
  intros [Hbinding Hresult] [Hbinds Hclosed] Hin.
  destruct (Hbinding b Hin) as [Hcontext Hvalue].
  destruct (target_count_one_unique f (binding_value b)
              (Hbinds (binding_value b) Hvalue))
    as [sources [l [Hproducer Hunique]]].
  exists sources, l; split.
  - rewrite Hcontext; now apply label_contains_effect.
  - intros q' sources' l' Hproducer'.
    destruct
      (label_event_inv q q' f
         (ECompute sources' (binding_value b) l') Hproducer')
      as [Hq Hin_fragment].
    destruct (Hunique sources' l' Hin_fragment) as [Hsources Hl].
    split; [congruence | now split].
Qed.

Lemma matching_labelled_compute_has_binding
      q results bindings f q' sources y l :
  bindings_match_results q results bindings ->
  binds_exactly f results ->
  In (q', ECompute sources y l) (label q f) ->
  exists t, In (q', y, t) bindings.
Proof.
  intros [Hbinding Hresult] [Hbinds Hclosed] Hin.
  destruct (label_event_inv q q' f (ECompute sources y l) Hin)
    as [-> Hin_fragment].
  now apply Hresult, Hclosed with (sources := sources) (l := l).
Qed.

Lemma matching_bindings_fresh_from_trace
      g dlt e q results bindings :
  names_fresh g dlt e results ->
  bindings_match_results q results bindings ->
  Forall (fun b => ~ produced e (binding_value b)) bindings.
Proof.
  intros [Hfresh Hdistinct] [Hbinding Hresult].
  apply Forall_forall; intros b Hin.
  destruct (Hbinding b Hin) as [_ Hvalue].
  apply Forall_forall with (x := binding_value b) in Hfresh; auto.
  tauto.
Qed.

(** Exact list extension does not by itself relate a new environment entry to
    a new trace event.  The following record supplies that missing bridge.  It
    requires each new binding to have one producer in the appended suffix and
    requires every producer in that suffix to name a new binding.  Freshness
    from the old trace prevents reuse of a name that was produced previously
    but was not installed in the old dynamic environment. *)
Record exact_production_delta
       (old_dynamic new_dynamic : dynamic_env)
       (old_trace new_trace : trace)
       (added_bindings : list dynamic_binding)
       (added_events : trace) : Prop := {
  production_delta_dynamic :
    exact_dynamic_extension old_dynamic new_dynamic added_bindings;
  production_delta_trace :
    exact_trace_extension old_trace new_trace added_events;
  production_delta_fresh_from_old_trace :
    Forall (fun b => ~ produced old_trace (binding_value b)) added_bindings;
  production_delta_bindings_are_produced :
    forall b,
      In b added_bindings ->
      binding_has_unique_added_producer added_events b;
  production_delta_events_are_bound :
    forall q sources y l,
      In (q, ECompute sources y l) added_events ->
      exists t, In (q, y, t) added_bindings
}.

Lemma exact_dynamic_extension_reflexive dlt :
  exact_dynamic_extension dlt dlt [].
Proof.
  split; [constructor |].
  split; [constructor |].
  intros q y t; simpl; tauto.
Qed.

(** This constructor packages the common proof shared by derivation, proposal,
    tool return, and runtime execution.  Exact environment extension supplies
    single assignment; the binding/result correspondence and closed fragment
    supply both directions of unique production. *)
Lemma exact_production_delta_from_exact_outputs
      old_dynamic new_dynamic old_trace new_trace
      q results bindings f :
  exact_dynamic_extension old_dynamic new_dynamic bindings ->
  exact_trace_extension old_trace new_trace (label q f) ->
  Forall (fun y => ~ produced old_trace y) results ->
  bindings_match_results q results bindings ->
  binds_exactly f results ->
  exact_production_delta old_dynamic new_dynamic old_trace new_trace
                         bindings (label q f).
Proof.
  intros Hdynamic Htrace Hfresh Hmatching Hbinds.
  constructor; auto.
  - apply Forall_forall; intros b Hin.
    pose proof Hmatching as Hmatching'.
    destruct Hmatching' as [Hbinding Hresult].
    destruct (Hbinding b Hin) as [_ Hvalue].
    now apply Forall_forall with (x := binding_value b) in Hfresh.
  - intros b Hin.
    eapply matching_binding_has_unique_labelled_producer; eauto.
  - intros q' sources y l Hin.
    eapply matching_labelled_compute_has_binding; eauto.
Qed.

(** Non-producing transitions have an empty binding delta and a suffix without
    [ECompute].  Observation, commitment, transfer, and internal transitions
    are instances of this constructor. *)
Lemma exact_production_delta_without_outputs
      dlt old_trace new_trace added_events :
  exact_trace_extension old_trace new_trace added_events ->
  (forall q sources y l,
      ~ In (q, ECompute sources y l) added_events) ->
  exact_production_delta dlt dlt old_trace new_trace [] added_events.
Proof.
  intros Htrace Hnone; constructor.
  - apply exact_dynamic_extension_reflexive.
  - exact Htrace.
  - constructor.
  - intros b Hin; inversion Hin.
  - intros q sources y l Hin; exfalso.
    exact (Hnone q sources y l Hin).
Qed.

Lemma names_fresh_excludes_old_production g dlt e results :
  names_fresh g dlt e results ->
  Forall (fun y => ~ produced e y) results.
Proof.
  intros [Hfresh Hdistinct].
  eapply Forall_impl; [| exact Hfresh].
  intros y [_ [_ Hnot_produced]]; exact Hnot_produced.
Qed.

Lemma singleton_binding_matches_result q y t :
  bindings_match_results q [y] [(q, y, t)].
Proof.
  split.
  - intros [[q' y'] t'] Hin; simpl in Hin.
    destruct Hin as [Hequal | Hin]; [| contradiction].
    inversion Hequal; subst; split; simpl; auto.
  - intros y' Hin; simpl in Hin.
    destruct Hin as [-> | Hin].
    + exists t; simpl; auto.
    + contradiction.
Qed.

Lemma singleton_compute_binds_exactly sources y l :
  binds_exactly [ECompute sources y l] [y].
Proof.
  split.
  - unfold binds; intros y' Hin; simpl in Hin.
    destruct Hin as [-> | Hin]; [| contradiction].
    simpl; now rewrite Nat.eqb_refl.
  - intros sources' y' l' Hin; simpl in Hin.
    destruct Hin as [Hequal | Hin]; [| contradiction].
    inversion Hequal; subst; simpl; auto.
Qed.

Lemma obs_fragment_has_no_compute y source delegate_loc
      q q' sources result l :
  ~ In (q', ECompute sources result l)
       (label q (obs_fragment y source delegate_loc)).
Proof.
  unfold obs_fragment; destruct (Nat.eqb source delegate_loc); simpl.
  - intros [Hequal | Hin]; [discriminate | contradiction].
  - intros [Hequal | [Hequal | Hin]];
      [discriminate | discriminate | contradiction].
Qed.

(** The runtime binding list and the runtime name tuple contain the same
    outputs in the same order, with the event context attached to each typed
    result. *)
Lemma bind_runtime_outputs_match_results q outputs :
  bindings_match_results
    q (map runtime_output_value outputs) (bind_runtime_outputs q outputs).
Proof.
  induction outputs as [|[y t] rest IH]; simpl.
  - split; intros; contradiction.
  - destruct IH as [IHbindings IHresults].
    split.
    + intros [[q' y'] t'] Hin; simpl in Hin.
      destruct Hin as [Hequal | Hin].
      * inversion Hequal; subst; simpl; auto.
      * destruct (IHbindings (q', y', t') Hin) as [Hq Hvalue].
        simpl in Hq, Hvalue; split; [exact Hq | now right].
    + intros y' Hin; simpl in Hin.
      destruct Hin as [Hequal | Hin].
      * subst y'; exists t; simpl; auto.
      * destruct (IHresults y' Hin) as [t' Hin_binding].
        exists t'; simpl; auto.
Qed.

Lemma runtime_output_bindings_match_results mu :
  bindings_match_results
    (runtime_context mu) (runtime_outputs mu) (runtime_output_bindings mu).
Proof.
  destruct mu; simpl.
  - apply bind_runtime_outputs_match_results.
  - split; intros; contradiction.
Qed.

Lemma compute_outputs_target_count_zero deps outputs l y :
  ~ In y (map runtime_output_value outputs) ->
  target_count y (compute_outputs deps outputs l) = 0.
Proof.
  induction outputs as [|[z t] rest IH]; simpl; intros Hnotin.
  - reflexivity.
  - assert (y <> z) as Hneq.
    { intro Hequal; subst y; apply Hnotin; simpl; auto. }
    apply Nat.eqb_neq in Hneq; rewrite Hneq.
    apply IH; intro Hin; apply Hnotin; auto.
Qed.

Lemma compute_outputs_bind_declared_results deps outputs l :
  NoDup (map runtime_output_value outputs) ->
  binds (compute_outputs deps outputs l) (map runtime_output_value outputs).
Proof.
  induction outputs as [|[z t] rest IH]; simpl; intros Hdistinct y Hin.
  - contradiction.
  - inversion Hdistinct as [|z' values Hnotin Htail]; subst.
    destruct Hin as [-> | Hin].
    + cbn [target_count].
      rewrite Nat.eqb_refl; simpl.
      rewrite (compute_outputs_target_count_zero deps rest l y Hnotin).
      reflexivity.
    + assert (y <> z) as Hneq.
      { intro Hequal; subst y; apply Hnotin; exact Hin. }
      apply Nat.eqb_neq in Hneq.
      cbn [target_count].
      rewrite Hneq.
      now apply IH.
Qed.

Lemma compute_outputs_are_declared deps outputs l sources y l' :
  In (ECompute sources y l') (compute_outputs deps outputs l) ->
  In y (map runtime_output_value outputs).
Proof.
  induction outputs as [|[z t] rest IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [Hequal | Hin].
    + inversion Hequal; subst; auto.
    + right; exact (IH Hin).
Qed.

Lemma runtime_lift_binds_exactly mu :
  NoDup (runtime_outputs mu) ->
  binds_exactly (lift mu) (runtime_outputs mu).
Proof.
  destruct mu as [q p w d payload loc deps outputs |
                  q p w d payload from to]; simpl; intros Hdistinct.
  - split.
    + exact (compute_outputs_bind_declared_results deps outputs loc Hdistinct).
    + intros sources y l Hin; simpl in Hin.
      destruct Hin as [Hequal | Hin]; [discriminate |].
      now apply compute_outputs_are_declared in Hin.
  - split.
    + unfold binds; intros y Hin; contradiction.
    + intros sources y l Hin; simpl in Hin.
      destruct Hin as [Hequal | Hin]; contradiction || discriminate.
Qed.

Lemma runtime_update_excludes_old_production g dlt e mu dlt' :
  runtime_environment_update g dlt e mu dlt' ->
  Forall (fun y => ~ produced e y) (runtime_outputs mu).
Proof.
  destruct mu; simpl; intros Hupdate.
  - destruct Hupdate as [Hfresh [Hdata Hextension]].
    now apply names_fresh_excludes_old_production in Hfresh.
  - constructor.
Qed.

Lemma runtime_update_is_exact_dynamic_extension g dlt e mu dlt' :
  runtime_environment_update g dlt e mu dlt' ->
  exact_dynamic_extension dlt dlt' (runtime_output_bindings mu).
Proof.
  destruct mu; simpl; intros Hupdate.
  - destruct Hupdate as [Hfresh [Hdata Hextension]].
    now apply extends_with_is_exact_dynamic_extension.
  - subst dlt'; apply exact_dynamic_extension_reflexive.
Qed.

Lemma runtime_update_output_names_distinct g dlt e mu dlt' :
  runtime_environment_update g dlt e mu dlt' ->
  NoDup (runtime_outputs mu).
Proof.
  destruct mu; simpl; intros Hupdate.
  - destruct Hupdate as [[Hfresh Hdistinct] [Hdata Hextension]].
    exact Hdistinct.
  - constructor.
Qed.

(** The boundary label corresponding to a typed atomic action is determined by
    the action and its delegation context.  Result types remain in the typing
    derivation and are related to the label by [label_output_bindings]. *)
Definition atomic_boundary_label (q : context) (action : atomic_action) :
    boundary_label :=
  match action with
  | AObserve y source => LObserve q y source
  | ADerive y _ sources => LDerive q y sources
  | APropose p _ d => LPropose q p d
  | ACommit p _ _ alpha => LCommit q p alpha
  | ACall results t inputs eta reported =>
      LCall q t inputs results eta reported
  end.

(** Every strengthened typing rule now constructs the finite production delta
    of its emitted trace suffix.  The theorem covers non-producing atomic
    actions as well: their exact binding list is empty and their suffix contains
    no computation event. *)
Lemma typed_atomic_constructs_exact_production_delta
      g o a delegate_loc q old_dynamic old_trace action
      added_events new_dynamic :
  typed_atomic g o a delegate_loc q old_dynamic old_trace
               action added_events new_dynamic ->
  exists added_bindings,
    label_output_bindings (atomic_boundary_label q action) added_bindings /\
    exact_production_delta
      old_dynamic new_dynamic old_trace (old_trace ++ added_events)
      added_bindings added_events.
Proof.
  intros Htyping; destruct Htyping.
  - match goal with
    | Hfragment : ?f = obs_fragment ?y ?source ?delegate_loc |- _ =>
        subst f
    end.
    exists []; split; [constructor |].
    eapply exact_production_delta_without_outputs.
    + reflexivity.
    + intros q' sources result l Hin.
      eapply obs_fragment_has_no_compute; exact Hin.
  - exists [(q, y, t)]; split; [constructor |].
    eapply exact_production_delta_from_exact_outputs
      with (q := q) (results := [y])
           (f := [ECompute sources y delegate_loc]).
    + now apply extends_with_is_exact_dynamic_extension.
    + reflexivity.
    + eapply names_fresh_excludes_old_production
        with (g := g) (dlt := dlt); eassumption.
    + apply singleton_binding_matches_result.
    + apply singleton_compute_binds_exactly.
  - exists [(q, p, TyProposal w d)]; split; [constructor |].
    eapply exact_production_delta_from_exact_outputs
      with (q := q) (results := [p])
           (f := [ECompute [w; d] p delegate_loc]).
    + now apply extends_with_is_exact_dynamic_extension.
    + reflexivity.
    + eapply names_fresh_excludes_old_production
        with (g := g) (dlt := dlt); eassumption.
    + apply singleton_binding_matches_result.
    + apply singleton_compute_binds_exactly.
  - exists []; split; [constructor |].
    eapply exact_production_delta_without_outputs.
    + reflexivity.
    + intros q' sources result l Hin; simpl in Hin.
      destruct Hin as [Hequal | Hin]; [discriminate | contradiction].
  - exists out_bindings; split.
    + econstructor; eassumption.
    + eapply exact_production_delta_from_exact_outputs
        with (q := q) (results := ys) (f := reported).
      * now apply extends_with_is_exact_dynamic_extension.
      * reflexivity.
      * eapply names_fresh_excludes_old_production
          with (g := g) (dlt := dlt); eassumption.
      * eapply result_bindings_match_results; eassumption.
      * specialize (H5 reported H3); tauto.
Qed.

(** The runtime update contract supplies exactly the same evidence as a typed
    tool return.  Execution uses its typed output tuple; transfer is covered by
    the empty tuple and unchanged-environment branch of the contract. *)
Lemma runtime_constructs_exact_production_delta g dlt e mu dlt' :
  runtime_environment_update g dlt e mu dlt' ->
  exact_production_delta
    dlt dlt' e (e ++ label (runtime_context mu) (lift mu))
    (runtime_output_bindings mu)
    (label (runtime_context mu) (lift mu)).
Proof.
  intros Hupdate.
  eapply exact_production_delta_from_exact_outputs
    with (q := runtime_context mu)
         (results := runtime_outputs mu)
         (f := lift mu).
  - eapply runtime_update_is_exact_dynamic_extension; eassumption.
  - reflexivity.
  - eapply runtime_update_excludes_old_production; eassumption.
  - apply runtime_output_bindings_match_results.
  - apply runtime_lift_binds_exactly.
    eapply runtime_update_output_names_distinct; eassumption.
Qed.

(** This theorem discharges the bridge obligation for the operational
    semantics.  It does not assume a production delta: it constructs the exact
    binding list and trace suffix by inversion of the strengthened transition.
    Thus later confinement theorems can be instantiated with every actual
    boundary step rather than with a separately postulated certificate. *)
Theorem every_operational_step_constructs_exact_production_delta
        g o invoke run internal c lab c' :
  step g o invoke run internal c lab c' ->
  exists added_bindings added_events,
    label_output_bindings lab added_bindings /\
    exact_production_delta
      (cfg_dynamic c) (cfg_dynamic c')
      (cfg_trace c) (cfg_trace c')
      added_bindings added_events.
Proof.
  intros Hstep; destruct Hstep.
  all: try match goal with
  | Htyping : typed_atomic _ _ _ _ _ _ _ ?action ?events ?new_dynamic |- _ =>
      destruct (typed_atomic_constructs_exact_production_delta Htyping)
        as [bindings [Hlabel Hdelta]];
      exists bindings, events; split; assumption
  end.
  - exists (runtime_output_bindings mu),
      (label (runtime_context mu) (lift mu)); split.
    + constructor.
    + eapply runtime_constructs_exact_production_delta with (g := g);
        eassumption.
  - exists [], []; split; [constructor |].
    eapply exact_production_delta_without_outputs.
    + unfold exact_trace_extension; now rewrite app_nil_r.
    + intros q sources y l Hin; contradiction.
Qed.

(** The delta is attached to an actual transition of the operational
    semantics.  This prevents a caller from presenting two arbitrarily related
    configurations as a certified production step.  The strengthened typing
    and runtime premises make the delta a proved consequence of a transition,
    rather than an additional assumption of the confinement theorem. *)
Definition exact_production_step
           (g : static_env) (o : oracle)
           (invoke : invocation_semantics)
           (run : runtime_semantics)
           (internal : internal_semantics)
           (old : agentic_configuration) (lab : boundary_label)
           (new : agentic_configuration)
           (added_bindings : list dynamic_binding)
           (added_events : trace) : Prop :=
  step g o invoke run internal (agentic_core old) lab (agentic_core new) /\
  label_output_bindings lab added_bindings /\
  exact_production_delta
    (cfg_dynamic (agentic_core old)) (cfg_dynamic (agentic_core new))
    (cfg_trace (agentic_core old)) (cfg_trace (agentic_core new))
    added_bindings added_events.

(** Preservation starts from the full invariant of point 1.  The existential
    lists are witnesses, not an executable enumeration of the functional
    environment; a later finite-map layer may compute the same witnesses. *)
Definition well_formed_exact_production_step
           (g : static_env) (o : oracle)
           (invoke : invocation_semantics)
           (run : runtime_semantics)
           (internal : internal_semantics)
           (old : agentic_configuration) (lab : boundary_label)
           (new : agentic_configuration) : Prop :=
  well_formed_configuration g old /\
  exists added_bindings added_events,
    exact_production_step g o invoke run internal old lab new
                          added_bindings added_events.

(** No additional certificate is assumed here.  The preceding theorem extracts
    the witnesses directly from the operational derivation and packages them
    with the corresponding boundary-label relation. *)
Corollary every_operational_step_constructs_exact_production_step
          g o invoke run internal old lab new :
  step g o invoke run internal (agentic_core old) lab (agentic_core new) ->
  exists added_bindings added_events,
    exact_production_step g o invoke run internal old lab new
                          added_bindings added_events.
Proof.
  intros Hstep.
  destruct
    (every_operational_step_constructs_exact_production_delta Hstep)
    as [added_bindings [added_events [Hlabel Hdelta]]].
  exists added_bindings, added_events.
  unfold exact_production_step; split.
  - exact Hstep.
  - split; [exact Hlabel | exact Hdelta].
Qed.

Corollary well_formed_operational_step_has_exact_production_step
          g o invoke run internal old lab new :
  well_formed_configuration g old ->
  step g o invoke run internal (agentic_core old) lab (agentic_core new) ->
  well_formed_exact_production_step
    g o invoke run internal old lab new.
Proof.
  intros Hwf Hstep; split; [exact Hwf |].
  now apply every_operational_step_constructs_exact_production_step.
Qed.

(** Pairwise distinct values in the finite binding delta make the entire
    binding triples unique when their value projections agree.  This lemma is
    the list-level fact used to rule out two assignments of one fresh name. *)
Lemma NoDup_binding_values_unique :
  forall bindings b1 b2,
    NoDup (map binding_value bindings) ->
    In b1 bindings ->
    In b2 bindings ->
    binding_value b1 = binding_value b2 ->
    b1 = b2.
Proof.
  induction bindings as [|b bindings IH];
    intros b1 b2 Hdistinct Hin1 Hin2 Hvalue.
  - inversion Hin1.
  - inversion Hdistinct as [|value values Hnotin Htail]; subst.
    simpl in Hin1, Hin2.
    destruct Hin1 as [-> | Hin1]; destruct Hin2 as [-> | Hin2].
    + reflexivity.
    + exfalso; apply Hnotin; rewrite Hvalue.
      now apply in_map.
    + exfalso; apply Hnotin; rewrite <- Hvalue.
      now apply in_map.
    + eapply IH; eauto.
Qed.

(** An exact extension retains the old lookup result.  Thus a transition
    cannot overwrite an installed binding with a different type. *)
Lemma production_delta_preserves_old_binding
      old_dynamic new_dynamic old_trace new_trace added_bindings added_events
      q y t :
  exact_production_delta old_dynamic new_dynamic old_trace new_trace
                         added_bindings added_events ->
  old_dynamic q y = Some t ->
  new_dynamic q y = Some t.
Proof.
  intros Hdelta Hold.
  eapply exact_extension_preserves_old; eauto.
  exact (production_delta_dynamic Hdelta).
Qed.

(** Freshness is global across contexts.  In particular, an old value name
    cannot occur among the newly assigned bindings. *)
Lemma production_delta_does_not_reassign_old_name
      old_dynamic new_dynamic old_trace new_trace added_bindings added_events
      q y t b :
  exact_production_delta old_dynamic new_dynamic old_trace new_trace
                         added_bindings added_events ->
  old_dynamic q y = Some t ->
  In b added_bindings ->
  binding_value b = y ->
  False.
Proof.
  intros Hdelta Hold Hin Hvalue.
  pose proof
    (exact_extension_added_names_are_fresh
       (production_delta_dynamic Hdelta) b q Hin) as Hnone.
  rewrite Hvalue in Hnone; congruence.
Qed.

(** Distinctness of the value projection rules out two new bindings for one
    name, including assignments attempted in different contexts. *)
Lemma production_delta_new_bindings_are_unique
      old_dynamic new_dynamic old_trace new_trace added_bindings added_events
      b1 b2 :
  exact_production_delta old_dynamic new_dynamic old_trace new_trace
                         added_bindings added_events ->
  In b1 added_bindings ->
  In b2 added_bindings ->
  binding_value b1 = binding_value b2 ->
  b1 = b2.
Proof.
  intros Hdelta Hin1 Hin2 Hvalue.
  eapply NoDup_binding_values_unique; eauto.
  eapply exact_extension_added_names_are_distinct.
  exact (production_delta_dynamic Hdelta).
Qed.

(** Single assignment is preserved because any two target lookups are either
    both old, both new, or one of each.  Old--old equality follows from source
    well-formedness, new--new equality follows from finite-delta distinctness,
    and the mixed cases contradict global freshness. *)
Lemma exact_dynamic_extension_preserves_single_assignment
      old_dynamic new_dynamic added_bindings :
  single_assignment old_dynamic ->
  exact_dynamic_extension old_dynamic new_dynamic added_bindings ->
  single_assignment new_dynamic.
Proof.
  intros Hold_assignment Hextension q1 q2 y t1 t2 Hnew1 Hnew2.
  pose proof
    (exact_extension_has_no_other_bindings Hextension q1 y Hnew1)
    as Hcase1.
  pose proof
    (exact_extension_has_no_other_bindings Hextension q2 y Hnew2)
    as Hcase2.
  destruct Hcase1 as [Hold1 | Hadd1];
    destruct Hcase2 as [Hold2 | Hadd2].
  - eapply Hold_assignment; eauto.
  - exfalso.
    pose proof
      (exact_extension_added_names_are_fresh
         Hextension (q2, y, t2) q1 Hadd2) as Hnone.
    simpl in Hnone; congruence.
  - exfalso.
    pose proof
      (exact_extension_added_names_are_fresh
         Hextension (q1, y, t1) q2 Hadd1) as Hnone.
    simpl in Hnone; congruence.
  - pose proof
      (NoDup_binding_values_unique
         added_bindings (q1, y, t1) (q2, y, t2)
         (exact_extension_added_names_are_distinct Hextension)
         Hadd1 Hadd2 eq_refl) as Hequal.
    inversion Hequal; subst; auto.
Qed.

(** Appending a suffix that contains no producer for [y] preserves the old
    unique producer.  This is the trace analogue of retaining an old binding. *)
Lemma unique_producer_preserved_by_irrelevant_suffix e added q y :
  has_unique_producer e q y ->
  (forall q' sources l, ~ In (q', ECompute sources y l) added) ->
  has_unique_producer (e ++ added) q y.
Proof.
  intros [sources [l [Hin Hunique]]] Habsent.
  exists sources, l; split.
  - apply in_or_app; auto.
  - intros q' sources' l' Hin'.
    apply in_app_iff in Hin'.
    destruct Hin' as [Hin' | Hin'].
    + now apply Hunique.
    + exfalso; eapply Habsent; eauto.
Qed.

(** Completeness of the binding--event bridge makes a fresh added name unique
    in the whole extended trace, rather than only in the appended suffix. *)
Lemma unique_added_producer_extends_to_trace e added q y :
  ~ produced e y ->
  (exists sources l,
      In (q, ECompute sources y l) added /\
      forall q' sources' l',
        In (q', ECompute sources' y l') added ->
        q' = q /\ sources' = sources /\ l' = l) ->
  has_unique_producer (e ++ added) q y.
Proof.
  intros Hfresh [sources [l [Hin Hunique]]].
  exists sources, l; split.
  - apply in_or_app; auto.
  - intros q' sources' l' Hin'.
    apply in_app_iff in Hin'.
    destruct Hin' as [Hin' | Hin'].
    + exfalso; apply Hfresh.
      exists q', sources', l'; exact Hin'.
    + now apply Hunique.
Qed.

(** Closure of the delta implies that an appended producer cannot target an
    old binding: it would have to correspond to a fresh added binding with the
    same globally absent name. *)
Lemma production_delta_suffix_does_not_produce_old_binding
      old_dynamic new_dynamic old_trace new_trace added_bindings added_events
      q y t :
  exact_production_delta old_dynamic new_dynamic old_trace new_trace
                         added_bindings added_events ->
  old_dynamic q y = Some t ->
  forall q' sources l, ~ In (q', ECompute sources y l) added_events.
Proof.
  intros Hdelta Hold q' sources l Hin.
  destruct
    (production_delta_events_are_bound Hdelta q' sources y l Hin)
    as [t' Hadd].
  eapply production_delta_does_not_reassign_old_name
    with (q := q) (t := t) (b := (q', y, t')); eauto.
Qed.

(** The producer of an existing binding remains unique after an exact
    production delta.  The result uses the closed-suffix condition above to
    exclude a second producer in the appended events. *)
Lemma production_delta_preserves_existing_unique_producer
      old_dynamic new_dynamic old_trace new_trace added_bindings added_events
      q y t :
  exact_production_delta old_dynamic new_dynamic old_trace new_trace
                         added_bindings added_events ->
  old_dynamic q y = Some t ->
  has_unique_producer old_trace q y ->
  has_unique_producer new_trace q y.
Proof.
  intros Hdelta Hold Hproducer.
  rewrite (production_delta_trace Hdelta).
  eapply unique_producer_preserved_by_irrelevant_suffix; eauto.
  eapply production_delta_suffix_does_not_produce_old_binding; eauto.
Qed.

(** Each newly installed binding has exactly the producer named by the delta.
    Freshness from the complete old trace excludes a prior producer, while
    uniqueness inside the suffix excludes another new producer. *)
Lemma production_delta_new_binding_has_unique_producer
      old_dynamic new_dynamic old_trace new_trace added_bindings added_events
      q y t :
  exact_production_delta old_dynamic new_dynamic old_trace new_trace
                         added_bindings added_events ->
  In (q, y, t) added_bindings ->
  has_unique_producer new_trace q y.
Proof.
  intros Hdelta Hin.
  pose proof (production_delta_fresh_from_old_trace Hdelta) as Hfresh.
  apply Forall_forall with (x := (q, y, t)) in Hfresh; auto.
  pose proof
    (production_delta_bindings_are_produced Hdelta (q, y, t) Hin)
    as Hproducer.
  unfold binding_has_unique_added_producer in Hproducer; simpl in Hproducer.
  rewrite (production_delta_trace Hdelta).
  now apply unique_added_producer_extends_to_trace.
Qed.

(** The unique-production invariant is therefore preserved for every binding
    in the target environment.  Exactness leaves only two cases: a retained old
    binding or one of the explicitly listed new bindings. *)
Lemma production_delta_preserves_unique_production
      g old new added_bindings added_events :
  well_formed_configuration g old ->
  exact_production_delta
    (cfg_dynamic (agentic_core old)) (cfg_dynamic (agentic_core new))
    (cfg_trace (agentic_core old)) (cfg_trace (agentic_core new))
    added_bindings added_events ->
  every_dynamic_binding_has_unique_producer
    (cfg_dynamic (agentic_core new)) (cfg_trace (agentic_core new)).
Proof.
  intros Hwf Hdelta q y t Hnew.
  pose proof
    (exact_extension_has_no_other_bindings
       (production_delta_dynamic Hdelta) q y Hnew) as Hcase.
  destruct Hcase as [Hold | Hadd].
  - eapply production_delta_preserves_existing_unique_producer; eauto.
    eapply wf_dynamic_names_produced_once; eauto.
  - eapply production_delta_new_binding_has_unique_producer; eauto.
Qed.

(** This is the point-3 preservation result.  It combines the global
    single-assignment property with unique production for every target binding.
    The operational-step premise is retained in the interface even though the
    preservation proof itself consumes only its certified finite delta. *)
Theorem single_assignment_and_unique_production_preserved
        g o invoke run internal old lab new :
  well_formed_exact_production_step
    g o invoke run internal old lab new ->
  single_assignment (cfg_dynamic (agentic_core new)) /\
  every_dynamic_binding_has_unique_producer
    (cfg_dynamic (agentic_core new)) (cfg_trace (agentic_core new)).
Proof.
  intros [Hwf [added_bindings [added_events [_ [_ Hdelta]]]]].
  split.
  - eapply exact_dynamic_extension_preserves_single_assignment.
    + exact (wf_dynamic_names_global Hwf).
    + exact (production_delta_dynamic Hdelta).
  - eapply production_delta_preserves_unique_production; eauto.
Qed.

(** The certificate-free form is the bridge's final result.  A well-formed
    source and an ordinary strengthened operational step are sufficient; the
    exact finite witnesses are constructed internally and then consumed by the
    point-3 preservation theorem. *)
Corollary every_well_formed_operational_step_preserves_point3
          g o invoke run internal old lab new :
  well_formed_configuration g old ->
  step g o invoke run internal (agentic_core old) lab (agentic_core new) ->
  single_assignment (cfg_dynamic (agentic_core new)) /\
  every_dynamic_binding_has_unique_producer
    (cfg_dynamic (agentic_core new)) (cfg_trace (agentic_core new)).
Proof.
  intros Hwf Hstep.
  eapply single_assignment_and_unique_production_preserved
    with (g := g) (o := o) (invoke := invoke) (run := run)
         (internal := internal) (old := old) (lab := lab).
  eapply well_formed_operational_step_has_exact_production_step; eassumption.
Qed.

(** ** Group 4. Conservative provenance *)

(** Conservative provenance is a boundary claim, not an assertion about the
    internal causal semantics of an LLM, tool, or workflow engine.  For model
    outputs the host-visible lower bound must be included; for tool outputs the
    complete input tuple must be included; and for runtime outputs the trace
    must reproduce the dependency tuple reported by the trusted adapter. *)
Inductive label_supports_conservative_production
          (g : static_env) (delegate_loc : locality) :
    boundary_label -> context -> value -> value_origin ->
    list value -> locality -> Prop :=
| ConservativeModelProduction : forall q y sources,
    subset (visible_values g q delegate_loc) sources ->
    label_supports_conservative_production g delegate_loc
      (LDerive q y sources) q y (OriginModel q) sources delegate_loc
| ConservativeToolProduction :
    forall q t inputs results eta fragment y sources l,
    In y results ->
    In (ECompute sources y l) fragment ->
    subset inputs sources ->
    label_supports_conservative_production g delegate_loc
      (LCall q t inputs results eta fragment)
      q y (OriginTool q t eta) sources l
| ConservativeRuntimeProduction :
    forall q p w d payload l dependencies outputs y output_ty,
    In (y, output_ty) outputs ->
    label_supports_conservative_production g delegate_loc
      (LRuntime
         (RuntimeExec q p w d payload l dependencies outputs))
      q y
      (OriginRuntime q
         (RuntimeExec q p w d payload l dependencies outputs))
      dependencies l.

(** A conservative source claim becomes persistent provenance only when its
    boundary label is recorded in the history and its corresponding production
    event occurs in the accumulated trace.  Keeping both witnesses prevents a
    label-only assertion or an unrelated [Compute] event from sufficing. *)
Definition has_conservative_provenance
           (g : static_env) (delegate_loc : locality)
           (history : list boundary_label) (e : trace)
           (q : context) (y : value) (origin : value_origin) : Prop :=
  exists lab sources l,
    In lab history /\
    label_introduces lab q y origin /\
    label_supports_conservative_production
      g delegate_loc lab q y origin sources l /\
    In (q, ECompute sources y l) e.

(** Proposal names are protocol witnesses and are handled by the exact
    proposal--approval--commitment point.  Every model, tool, or runtime origin
    must instead carry the conservative production evidence above. *)
Definition configuration_has_conservative_provenance
           (g : static_env) (c : agentic_configuration) : Prop :=
  forall q y origin,
    has_origin (boundary_history c) q y origin ->
    match origin with
    | OriginProposal _ => True
    | _ =>
        has_conservative_provenance
          g (cfg_locality (agentic_core c))
          (boundary_history c) (cfg_trace (agentic_core c))
          q y origin
    end.

(** The core semantics does not store boundary history or the finite active
    context set.  [agentic_boundary_step] supplies their exact wrapper update:
    the emitted label is appended once, and an existing step creates no new
    delegation context. *)
Record agentic_boundary_step
       (g : static_env) (o : oracle)
       (invoke : invocation_semantics)
       (run : runtime_semantics)
       (internal : internal_semantics)
       (old : agentic_configuration) (lab : boundary_label)
       (new : agentic_configuration) : Prop := {
  agentic_step_core :
    step g o invoke run internal
      (agentic_core old) lab (agentic_core new);
  agentic_step_history :
    boundary_history new = boundary_history old ++ [lab];
  agentic_step_active_contexts :
    active_contexts new = active_contexts old
}.

Lemma agentic_boundary_step_preserves_locality
      g o invoke run internal old lab new :
  agentic_boundary_step g o invoke run internal old lab new ->
  cfg_locality (agentic_core new) = cfg_locality (agentic_core old).
Proof.
  intros Hagentic; destruct Hagentic as [Hstep Hhistory Hcontexts].
  inversion Hstep; reflexivity.
Qed.

Lemma agentic_boundary_step_trace_extends
      g o invoke run internal old lab new :
  agentic_boundary_step g o invoke run internal old lab new ->
  trace_extends (cfg_trace (agentic_core old))
                (cfg_trace (agentic_core new)).
Proof.
  intros Hagentic; destruct Hagentic as [Hstep Hhistory Hcontexts].
  destruct (every_operational_step_constructs_exact_production_delta Hstep)
    as [bindings [events [Hlabel Hdelta]]].
  exists events; exact (production_delta_trace Hdelta).
Qed.

Lemma runtime_output_name_has_type outputs y :
  In y (map runtime_output_value outputs) ->
  exists output_ty, In (y, output_ty) outputs.
Proof.
  induction outputs as [|[z t] rest IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + exists t; simpl; auto.
    + destruct (IH Hin) as [t' Hin']; exists t'; simpl; auto.
Qed.

Lemma compute_outputs_contains_typed_output
      dependencies outputs l y output_ty :
  In (y, output_ty) outputs ->
  In (ECompute dependencies y l)
     (compute_outputs dependencies outputs l).
Proof.
  induction outputs as [|[z t] rest IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [Hequal | Hin].
    + inversion Hequal; subst; auto.
    + right; now apply IH.
Qed.

Lemma agentic_boundary_step_records_label
      g o invoke run internal old lab new :
  agentic_boundary_step g o invoke run internal old lab new ->
  In lab (boundary_history new).
Proof.
  intros Hagentic; rewrite (agentic_step_history Hagentic).
  apply in_or_app; right; simpl; auto.
Qed.

(** T-Derive already contains the host-visible lower-bound premise.  The model
    theorem records that premise together with the exact derive label and its
    unique emitted [Compute] event. *)
Theorem model_output_has_conservative_provenance
        g o invoke run internal old new q y sources :
  agentic_boundary_step
    g o invoke run internal old (LDerive q y sources) new ->
  has_conservative_provenance
    g (cfg_locality (agentic_core new))
    (boundary_history new) (cfg_trace (agentic_core new))
    q y (OriginModel q).
Proof.
  intros Hagentic.
  pose proof (agentic_step_core Hagentic) as Hstep.
  inversion Hstep; subst.
  match goal with
  | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
      inversion Htyping; subst
  end.
  exists (LDerive q y sources), sources, ld; repeat split.
  - eapply agentic_boundary_step_records_label; exact Hagentic.
  - constructor.
  - constructor; eassumption.
  - simpl; apply in_or_app; right; simpl; auto.
Qed.

(** A sound tool schema may list more dependencies than the call inputs, but it
    may not omit an input supplied to the invocation.  Exact result binding
    locates the sole producing event for each declared result, and the new
    schema premise supplies its conservative lower bound. *)
Theorem tool_output_has_conservative_provenance
        g o invoke run internal old new
        q t inputs results eta reported y :
  agentic_boundary_step
    g o invoke run internal old
    (LCall q t inputs results eta reported) new ->
  In y results ->
  has_conservative_provenance
    g (cfg_locality (agentic_core new))
    (boundary_history new) (cfg_trace (agentic_core new))
    q y (OriginTool q t eta).
Proof.
  intros Hagentic Hy.
  pose proof (agentic_step_core Hagentic) as Hstep.
  inversion Hstep; subst.
  match goal with
  | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
      inversion Htyping; subst
  end.
  match goal with
  | Hbranches : forall f, In f ?schema -> _,
    Hreported : In reported ?schema |- _ =>
      pose proof (Hbranches reported Hreported) as Hchecked
  end.
  destruct Hchecked as [Hadmissible [Hcapabilities
    [Hguard [Hbinds Hconservative]]]].
  destruct Hbinds as [Htargets Hclosed].
  destruct (target_count_one_unique reported y (Htargets y Hy))
    as [dependencies [l [Hcompute Hunique]]].
  exists (LCall q t inputs results eta reported), dependencies, l.
  repeat split.
  - eapply agentic_boundary_step_records_label; exact Hagentic.
  - constructor; exact Hy.
  - constructor; auto.
    now apply Hconservative with (y := y) (l := l).
  - simpl; apply in_or_app; right.
    now apply label_contains_effect.
Qed.

(** Runtime execution uses the adapter's dependency tuple verbatim for every
    typed output.  A send has no output and therefore makes the theorem's
    premise impossible. *)
Theorem runtime_output_has_conservative_provenance
        g o invoke run internal old new mu y :
  agentic_boundary_step
    g o invoke run internal old (LRuntime mu) new ->
  In y (runtime_outputs mu) ->
  has_conservative_provenance
    g (cfg_locality (agentic_core new))
    (boundary_history new) (cfg_trace (agentic_core new))
    (runtime_context mu) y
    (OriginRuntime (runtime_context mu) mu).
Proof.
  intros Hagentic Hy.
  pose proof (agentic_step_core Hagentic) as Hstep.
  inversion Hstep; subst.
  destruct mu as [q p w d payload l dependencies outputs |
                  q p w d payload from to]; simpl in Hy |- *.
  - destruct (runtime_output_name_has_type outputs y Hy)
      as [output_ty Htyped].
    exists (LRuntime
      (RuntimeExec q p w d payload l dependencies outputs)), dependencies, l.
    repeat split.
    + eapply agentic_boundary_step_records_label; exact Hagentic.
    + constructor; exact Hy.
    + eapply ConservativeRuntimeProduction with (output_ty := output_ty).
      exact Htyped.
    + apply in_or_app; right.
      simpl; right.
      apply label_contains_effect.
      now apply compute_outputs_contains_typed_output with
        (output_ty := output_ty).
  - contradiction.
Qed.

(** Conservative provenance survives extension because its two historical
    witnesses are positive facts: a boundary label remains in an appended
    history, and a production event remains in an extended trace.  The support
    judgment itself is independent of later execution. *)
Lemma has_conservative_provenance_monotone
      g delegate_loc old_history new_history old_trace new_trace q y origin :
  (exists added_labels,
      new_history = old_history ++ added_labels) ->
  trace_extends old_trace new_trace ->
  has_conservative_provenance
    g delegate_loc old_history old_trace q y origin ->
  has_conservative_provenance
    g delegate_loc new_history new_trace q y origin.
Proof.
  intros [added_labels Hhistory] Htrace
    [lab [sources [l [Hin [Hintroduces [Hsupports Hcompute]]]]]].
  exists lab, sources, l; repeat split.
  - rewrite Hhistory; apply in_or_app; left; exact Hin.
  - exact Hintroduces.
  - exact Hsupports.
  - eapply trace_extension_preserves_events; eauto.
Qed.

(** This local theorem packages the three origin-specific results.  Its premise
    refers only to a value introduced by the current label; proposal names are
    intentionally discharged without a data-provenance obligation because
    their protocol binding belongs to the next proof point. *)
Theorem agentic_boundary_step_introduced_value_has_conservative_provenance
        g o invoke run internal old lab new :
  agentic_boundary_step g o invoke run internal old lab new ->
  forall q y origin,
    label_introduces lab q y origin ->
    match origin with
    | OriginProposal _ => True
    | _ =>
        has_conservative_provenance
          g (cfg_locality (agentic_core new))
          (boundary_history new) (cfg_trace (agentic_core new))
          q y origin
    end.
Proof.
  intros Hagentic q y origin Hintroduction.
  inversion Hintroduction; subst; simpl.
  - eapply model_output_has_conservative_provenance; exact Hagentic.
  - eapply tool_output_has_conservative_provenance; eauto.
  - eapply runtime_output_has_conservative_provenance; eauto.
  - exact I.
Qed.

(** A complete one-step preservation statement must cover both portions of the
    updated history.  An older origin uses monotonicity; an origin introduced by
    the appended label uses the local theorem above.  The core step preserves
    the delegate locality, so a model-visible lower bound proved before the
    step remains the same lower bound afterwards. *)
Theorem agentic_boundary_step_preserves_conservative_provenance
        g o invoke run internal old lab new :
  configuration_has_conservative_provenance g old ->
  agentic_boundary_step g o invoke run internal old lab new ->
  configuration_has_conservative_provenance g new.
Proof.
  intros Hold Hagentic q y origin
    [origin_label [Hin_history Hintroduction]].
  rewrite (agentic_step_history Hagentic) in Hin_history.
  apply in_app_iff in Hin_history.
  destruct Hin_history as [Hin_old | Hin_current].
  - assert (Horigin_old :
        has_origin (boundary_history old) q y origin).
    { exists origin_label; auto. }
    pose proof (Hold q y origin Horigin_old) as Hprovenance.
    destruct origin; simpl in Hprovenance |- *; try exact I.
    all: rewrite (agentic_boundary_step_preserves_locality Hagentic).
    all: eapply has_conservative_provenance_monotone.
    all: try (exists [lab]; exact (agentic_step_history Hagentic)).
    all: try (exact (agentic_boundary_step_trace_extends Hagentic)).
    all: exact Hprovenance.
  - simpl in Hin_current.
    destruct Hin_current as [Hequal | Hfalse].
    + subst origin_label.
      eapply agentic_boundary_step_introduced_value_has_conservative_provenance;
        eauto.
    + contradiction.
Qed.

(** ** Group 5. Exact proposal--approval--commitment binding *)

(** The binding property joins the three persistent views of authority.  A
    proposal-typed name must be backed by its exact production event; every
    commitment must retain that binding and verified tuple-specific evidence;
    and every production action must be preceded by the matching commitment.
    The workflow version and patch occur syntactically in all three clauses. *)
Definition exact_proposal_approval_commitment_binding
           (g : static_env) (c : agentic_configuration) : Prop :=
  proposal_bindings_have_provenance
    (cfg_dynamic (agentic_core c)) (cfg_trace (agentic_core c)) /\
  commitments_are_consistent g (agentic_core c) /\
  production_actions_have_prior_commitment
    (cfg_trace (agentic_core c)).

(** Appending a trace suffix preserves an existing strict order: the old
    suffix is absorbed into the suffix following the second event. *)
Lemma occurs_before_monotone_under_trace_extension
      old_trace new_trace first second :
  trace_extends old_trace new_trace ->
  occurs_before first second old_trace ->
  occurs_before first second new_trace.
Proof.
  intros [added Hextension] [prefix [suffix [Hold Hin]]].
  unfold exact_trace_extension in Hextension.
  subst new_trace; subst old_trace.
  exists prefix, (suffix ++ added); split.
  - now rewrite <- app_assoc.
  - exact Hin.
Qed.

(** Proposal provenance is also positive trace information and therefore
    remains valid when later boundary effects are appended. *)
Lemma proposed_monotone_under_trace_extension
      old_trace new_trace q p w d :
  trace_extends old_trace new_trace ->
  proposed old_trace q p w d ->
  proposed new_trace q p w d.
Proof.
  intros Hextension [l Hin]; exists l.
  eapply trace_extension_preserves_events; eauto.
Qed.

Lemma agentic_boundary_step_preserves_delegate
      g o invoke run internal old lab new :
  agentic_boundary_step g o invoke run internal old lab new ->
  cfg_delegate (agentic_core new) = cfg_delegate (agentic_core old).
Proof.
  intros Hagentic; destruct Hagentic as [Hstep Hhistory Hcontexts].
  inversion Hstep; reflexivity.
Qed.

(** The exact production bridge supplies an environment extension for every
    operational rule, including the empty extension of non-producing rules. *)
Lemma agentic_boundary_step_dynamic_extends
      g o invoke run internal old lab new :
  agentic_boundary_step g o invoke run internal old lab new ->
  dynamic_environment_extends
    (cfg_dynamic (agentic_core old))
    (cfg_dynamic (agentic_core new)).
Proof.
  intros Hagentic.
  destruct (every_operational_step_constructs_exact_production_delta
              (agentic_step_core Hagentic))
    as [bindings [events [Hlabel Hdelta]]].
  exists bindings; exact (production_delta_dynamic Hdelta).
Qed.

(** Tool result shapes inherit the declaration's data-type restriction at
    every leaf.  This rules out manufacturing a proposal through an ordinary
    tool output while retaining product-shaped result tuples. *)
Lemma result_binding_types_are_data q results result_ty bindings :
  result_bindings q results result_ty bindings ->
  data_type result_ty ->
  forall b, In b bindings -> data_type (binding_type b).
Proof.
  intros Hbindings; induction Hbindings; intros Hdata b Hin.
  - contradiction.
  - simpl in Hin; destruct Hin as [Hequal | Hin].
    + inversion Hequal; subst; simpl; exact Hdata.
    + contradiction.
  - simpl in Hdata; destruct Hdata as [Hleft Hright].
    apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
    + eapply IHHbindings1; eauto.
    + eapply IHHbindings2; eauto.
Qed.

(** The runtime analogue consumes the adapter's typed output tuple.  Its
    [Forall] premise is exactly the contract that runtime results are ordinary
    data rather than authority witnesses. *)
Lemma runtime_binding_types_are_data q outputs :
  Forall (fun out => data_type (runtime_output_type out)) outputs ->
  forall b,
    In b (bind_runtime_outputs q outputs) -> data_type (binding_type b).
Proof.
  intros Hdata; induction outputs as [|[y t] rest IH]; intros b Hin; simpl in *.
  - contradiction.
  - inversion Hdata as [|out outputs' Hhead Htail]; subst.
    destruct Hin as [Hequal | Hin].
    + inversion Hequal; subst; exact Hhead.
    + now apply IH.
Qed.

(** A proposal binding can arise only from [TPropose].  Derivation, tool, and
    runtime results are restricted to data types; observation, commitment,
    transfer, and internal steps do not add bindings.  An old proposal binding
    retains its exact production witness by trace monotonicity. *)
Theorem operational_step_preserves_proposal_binding_provenance
        g o invoke run internal old lab new :
  proposal_bindings_have_provenance
    (cfg_dynamic old) (cfg_trace old) ->
  step g o invoke run internal old lab new ->
  proposal_bindings_have_provenance
    (cfg_dynamic new) (cfg_trace new).
Proof.
  intros Hold Hstep; destruct Hstep; simpl.
  all: intros q0 p0 w0 d0 Hnew.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    eapply proposed_monotone_under_trace_extension.
    + exists (label q (obs_fragment y source ld)); reflexivity.
    + eapply Hold; exact Hnew.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    destruct (exact_extension_has_no_other_bindings
      (extends_with_is_exact_dynamic_extension H13)
      q0 p0 Hnew) as [Hbinding | Hadded].
    + eapply proposed_monotone_under_trace_extension.
      * exists [(q, ECompute sources y ld)]; reflexivity.
      * eapply Hold; exact Hbinding.
    + simpl in Hadded; destruct Hadded as [Hequal | Hfalse].
      * inversion Hequal; subst.
        simpl in H3; contradiction.
      * contradiction.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    match goal with
    | Hextension : extends_with _ _ [(?q, ?p, TyProposal ?w ?d)] |- _ =>
        destruct (exact_extension_has_no_other_bindings
          (extends_with_is_exact_dynamic_extension Hextension)
          q0 p0 Hnew) as [Hbinding | Hadded]
    end.
    + eapply proposed_monotone_under_trace_extension.
      * exists [(q, ECompute [w; d] p ld)]; reflexivity.
      * eapply Hold; exact Hbinding.
    + simpl in Hadded; destruct Hadded as [Hequal | Hfalse].
      * inversion Hequal; subst.
        exists ld; apply in_or_app; right; simpl; auto.
      * contradiction.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    eapply proposed_monotone_under_trace_extension.
    + exists [(q, ECommit p w d alpha ld)]; reflexivity.
    + eapply Hold; exact Hnew.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    destruct (exact_extension_has_no_other_bindings
      (extends_with_is_exact_dynamic_extension H17)
      q0 p0 Hnew) as [Hbinding | Hadded].
    + eapply proposed_monotone_under_trace_extension.
      * exists (label q reported); reflexivity.
      * eapply Hold; exact Hbinding.
    + pose proof
        (result_binding_types_are_data H12
          (schema_output_data td) (q0, p0, TyProposal w0 d0) Hadded)
        as Hdata.
      simpl in Hdata; contradiction.
  - destruct mu as [q p w d payload l dependencies outputs |
                    q p w d payload from to]; simpl in *.
    + destruct H4 as [Hfresh [Hdata Hextension]].
      destruct (exact_extension_has_no_other_bindings
        (extends_with_is_exact_dynamic_extension Hextension)
        q0 p0 Hnew) as [Hbinding | Hadded].
      * eapply proposed_monotone_under_trace_extension.
        -- exists (label q (lift
             (RuntimeExec q p w d payload l dependencies outputs)));
           reflexivity.
        -- eapply Hold; exact Hbinding.
      * pose proof
          (runtime_binding_types_are_data q Hdata
            (q0, p0, TyProposal w0 d0) Hadded) as Hordinary.
        simpl in Hordinary; contradiction.
    + subst dlt'.
      eapply proposed_monotone_under_trace_extension.
      * exists (label q [EExpose payload from to]); reflexivity.
      * eapply Hold; exact Hnew.
  - eapply Hold; exact Hnew.
Qed.

Corollary agentic_boundary_step_preserves_proposal_binding_provenance
          g o invoke run internal old lab new :
  proposal_bindings_have_provenance
    (cfg_dynamic (agentic_core old)) (cfg_trace (agentic_core old)) ->
  agentic_boundary_step g o invoke run internal old lab new ->
  proposal_bindings_have_provenance
    (cfg_dynamic (agentic_core new)) (cfg_trace (agentic_core new)).
Proof.
  intros Hold Hagentic.
  eapply operational_step_preserves_proposal_binding_provenance; eauto.
  exact (agentic_step_core Hagentic).
Qed.

(** [no_commit] is the executable structural guard used by tool and runtime
    fragments.  This logical form is convenient when a trace-membership proof
    must be split between an old prefix and a labelled suffix. *)
Lemma no_commit_excludes_commit f p w d alpha l :
  no_commit f -> ~ In (ECommit p w d alpha l) f.
Proof.
  induction f as [|eff rest IH]; simpl; intros Hnone Hin.
  - contradiction.
  - destruct eff; simpl in Hnone.
    + destruct Hin as [Hequal | Hin]; [discriminate | exact (IH Hnone Hin)].
    + destruct Hin as [Hequal | Hin]; [discriminate | exact (IH Hnone Hin)].
    + contradiction.
    + destruct Hin as [Hequal | Hin]; [discriminate | exact (IH Hnone Hin)].
    + destruct Hin as [Hequal | Hin]; [discriminate | exact (IH Hnone Hin)].
Qed.

(** If a step adds no commitment, consistency follows by monotonicity.  The
    proposal binding is preserved by the exact environment extension, the
    evidence tuple is unchanged because the delegate is unchanged, and the
    earlier proposal event retains its strict order in the longer trace. *)
Lemma commitments_are_consistent_monotone_without_new_commit
      g old new :
  commitments_are_consistent g old ->
  cfg_delegate new = cfg_delegate old ->
  dynamic_environment_extends (cfg_dynamic old) (cfg_dynamic new) ->
  trace_extends (cfg_trace old) (cfg_trace new) ->
  (forall q p w d alpha l,
      In (q, ECommit p w d alpha l) (cfg_trace new) ->
      In (q, ECommit p w d alpha l) (cfg_trace old)) ->
  commitments_are_consistent g new.
Proof.
  intros Hold Hdelegate Hdynamic Htrace Hnone q p w d alpha l Hin.
  destruct (Hold q p w d alpha l (Hnone q p w d alpha l Hin))
    as [Hbinding [Hevidence [lp Hbefore]]].
  split.
  - eapply dynamic_environment_extension_preserves_binding; eauto.
  - split.
    + rewrite Hdelegate; exact Hevidence.
    + exists lp.
      eapply occurs_before_monotone_under_trace_extension; eauto.
Qed.

Lemma commit_in_prefix_of_no_commit_suffix
      prefix q f q' p w d alpha l :
  no_commit f ->
  In (q', ECommit p w d alpha l) (prefix ++ label q f) ->
  In (q', ECommit p w d alpha l) prefix.
Proof.
  intros Hnone Hin; apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
  - exact Hin.
  - destruct (label_event_inv q q' f (ECommit p w d alpha l) Hin)
      as [Hequal Heffect].
    exfalso; eapply no_commit_excludes_commit; eauto.
Qed.

(** The only rule that may append a commitment is [TCommit].  Its premises
    provide the persistent proposal binding, the earlier exact proposal event,
    and verifier acceptance for the same approval tuple. *)
Theorem operational_step_preserves_commitment_consistency
        g o invoke run internal old lab new :
  commitments_are_consistent g old ->
  step g o invoke run internal old lab new ->
  commitments_are_consistent g new.
Proof.
  intros Hold Hstep.
  destruct (every_operational_step_constructs_exact_production_delta Hstep)
    as [bindings [events [Hlabel Hdelta]]].
  assert (Hdynamic :
      dynamic_environment_extends (cfg_dynamic old) (cfg_dynamic new)).
  { exists bindings; exact (production_delta_dynamic Hdelta). }
  assert (Htrace : trace_extends (cfg_trace old) (cfg_trace new)).
  { exists events; exact (production_delta_trace Hdelta). }
  destruct Hstep; simpl in Hdynamic, Htrace |- *.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    eapply commitments_are_consistent_monotone_without_new_commit.
    + exact Hold.
    + reflexivity.
    + exact Hdynamic.
    + exact Htrace.
    + intros; eapply commit_in_prefix_of_no_commit_suffix; eauto.
      unfold obs_fragment; destruct (Nat.eqb source ld); simpl; exact I.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    eapply commitments_are_consistent_monotone_without_new_commit.
    + exact Hold.
    + reflexivity.
    + exact Hdynamic.
    + exact Htrace.
    + intros q0 p0 w0 d0 alpha0 l0 Hin.
      apply in_app_iff in Hin; destruct Hin as [Hin | Hin]; [exact Hin |].
      simpl in Hin; destruct Hin as [Hequal | Hfalse];
        [discriminate | contradiction].
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    eapply commitments_are_consistent_monotone_without_new_commit.
    + exact Hold.
    + reflexivity.
    + exact Hdynamic.
    + exact Htrace.
    + intros q0 p0 w0 d0 alpha0 l0 Hin.
      apply in_app_iff in Hin; destruct Hin as [Hin | Hin]; [exact Hin |].
      simpl in Hin; destruct Hin as [Hequal | Hfalse];
        [discriminate | contradiction].
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    intros q0 p0 w0 d0 alpha0 l0 Hin.
    apply in_app_iff in Hin; destruct Hin as [Hin_old | Hin_new].
    + destruct (Hold q0 p0 w0 d0 alpha0 l0 Hin_old)
        as [Hbinding [Hevidence [lp Hbefore]]].
      split; [exact Hbinding |].
      split; [exact Hevidence |].
      exists lp.
      eapply occurs_before_monotone_under_trace_extension; eauto.
    + simpl in Hin_new; destruct Hin_new as [Hequal | Hfalse].
      * inversion Hequal; subst.
        split; [exact H6 |].
        split; [exact H12 |].
        destruct H9 as [lp Hproposal].
        exists lp; exists e, []; split.
        -- reflexivity.
        -- exact Hproposal.
      * contradiction.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    destruct H1 as [Hstage [Hnone Hpids]].
    eapply commitments_are_consistent_monotone_without_new_commit.
    + exact Hold.
    + reflexivity.
    + exact Hdynamic.
    + exact Htrace.
    + intros; eapply commit_in_prefix_of_no_commit_suffix; eauto.
  - eapply commitments_are_consistent_monotone_without_new_commit.
    + exact Hold.
    + reflexivity.
    + exact Hdynamic.
    + exact Htrace.
    + intros; eapply commit_in_prefix_of_no_commit_suffix; eauto.
  - eapply commitments_are_consistent_monotone_without_new_commit.
    + exact Hold.
    + reflexivity.
    + exact Hdynamic.
    + exact Htrace.
    + intros q0 p0 w0 d0 alpha0 l0 Hin; exact Hin.
Qed.

Corollary agentic_boundary_step_preserves_commitment_consistency
          g o invoke run internal old lab new :
  commitments_are_consistent g (agentic_core old) ->
  agentic_boundary_step g o invoke run internal old lab new ->
  commitments_are_consistent g (agentic_core new).
Proof.
  intros Hold Hagentic.
  eapply operational_step_preserves_commitment_consistency; eauto.
  exact (agentic_step_core Hagentic).
Qed.

(** Every protection-relevant boundary rule carries closed admissibility for
    its target trace.  An internal runtime transition is the sole exception,
    and it leaves the trace unchanged. *)
Lemma operational_step_target_admissible_or_trace_unchanged
      g o invoke run internal old lab new :
  step g o invoke run internal old lab new ->
  admissible g o (cfg_delegate new) (cfg_trace new) \/
  cfg_trace new = cfg_trace old.
Proof.
  intros Hstep; destruct Hstep; simpl.
  all: try (left; eapply typed_atomic_admissible; eassumption).
  - left; assumption.
  - right; reflexivity.
Qed.

(** Prefix admissibility checks every production action against an earlier
    commitment carrying the same proposal, workflow version, and patch.  Thus
    a boundary step either re-establishes the property from its admissible
    target trace or preserves it definitionally across an internal step. *)
Theorem operational_step_preserves_actions_follow_exact_commitment
        g o invoke run internal old lab new :
  production_actions_have_prior_commitment (cfg_trace old) ->
  step g o invoke run internal old lab new ->
  production_actions_have_prior_commitment (cfg_trace new).
Proof.
  intros Hold Hstep.
  destruct (operational_step_target_admissible_or_trace_unchanged Hstep)
    as [Hadmissible | Hunchanged].
  - intros q p k w d payload l Hact.
    destruct (@exact_commitment_from_admissibility
      g o (cfg_delegate new) (cfg_trace new) q p k w d payload l
      Hadmissible Hact)
      as [alpha [lc [Hcommit Hbefore]]].
    exists alpha, lc; exact Hbefore.
  - rewrite Hunchanged; exact Hold.
Qed.

Corollary agentic_boundary_step_preserves_actions_follow_exact_commitment
          g o invoke run internal old lab new :
  production_actions_have_prior_commitment
    (cfg_trace (agentic_core old)) ->
  agentic_boundary_step g o invoke run internal old lab new ->
  production_actions_have_prior_commitment
    (cfg_trace (agentic_core new)).
Proof.
  intros Hold Hagentic.
  eapply operational_step_preserves_actions_follow_exact_commitment; eauto.
  exact (agentic_step_core Hagentic).
Qed.

(** This is the point-5 one-step theorem.  It combines proposal provenance,
    tuple-specific approval verification, consistent commitments, and exact
    commitment order for production actions. *)
Theorem agentic_boundary_step_preserves_exact_proposal_approval_commitment
        g o invoke run internal old lab new :
  exact_proposal_approval_commitment_binding g old ->
  agentic_boundary_step g o invoke run internal old lab new ->
  exact_proposal_approval_commitment_binding g new.
Proof.
  intros [Hproposals [Hcommitments Hactions]] Hagentic.
  split.
  - eapply agentic_boundary_step_preserves_proposal_binding_provenance; eauto.
  - split.
    + eapply agentic_boundary_step_preserves_commitment_consistency; eauto.
    + eapply agentic_boundary_step_preserves_actions_follow_exact_commitment;
        eauto.
Qed.

(** The full well-formedness record introduced in point 1 already contains the
    three source clauses.  This projection makes point 5 directly reusable by
    the eventual combined confinement theorem. *)
Lemma well_formed_configuration_has_exact_proposal_approval_commitment
      g c :
  well_formed_configuration g c ->
  exact_proposal_approval_commitment_binding g c.
Proof.
  intros Hwf; split.
  - exact (wf_proposal_bindings Hwf).
  - split.
    + exact (wf_commitments Hwf).
    + exact (wf_actions_follow_commitment Hwf).
Qed.

Corollary every_well_formed_agentic_boundary_step_preserves_point5
          g o invoke run internal old lab new :
  well_formed_configuration g old ->
  agentic_boundary_step g o invoke run internal old lab new ->
  exact_proposal_approval_commitment_binding g new.
Proof.
  intros Hwf Hagentic.
  eapply agentic_boundary_step_preserves_exact_proposal_approval_commitment;
    eauto.
  now apply well_formed_configuration_has_exact_proposal_approval_commitment.
Qed.

(** ** Group 6. Capability non-amplification *)

(** Direct protocol operations and fragment-mediated operations use different
    capability checks in the paper.  Derivation, proposal, and commitment have
    dedicated capabilities.  Observation, tool calls, and runtime events are
    bounded by [req] of the exact emitted fragment, which additionally records
    remote exposure and production-action kinds. *)
Definition boundary_required_capabilities
           (delegate_loc : locality) (lab : boundary_label) : list capability :=
  match lab with
  | LObserve _ y source =>
      required_capabilities (obs_fragment y source delegate_loc)
  | LDerive _ _ _ => [CapDerive]
  | LPropose _ _ _ => [CapPropose]
  | LCommit _ _ _ => [CapCommit]
  | LCall _ _ _ _ _ fragment => required_capabilities fragment
  | LRuntime mu => required_capabilities (lift mu)
  | LInternal _ => []
  end.

Definition delegate_capabilities (g : static_env) (a : delegate) :
           list capability :=
  match delegate_caps g a with Some caps => caps | None => [] end.

(** A boundary label is capability-bounded when every capability it exercises
    occurs in the immutable declaration of the delegate that emitted it. *)
Definition label_is_capability_bounded
           (g : static_env) (a : delegate) (delegate_loc : locality)
           (lab : boundary_label) : Prop :=
  subset (boundary_required_capabilities delegate_loc lab)
         (delegate_capabilities g a).

(** Non-amplification is persistent: every recorded boundary label must remain
    within the same delegate declaration.  Runtime state and dynamic values do
    not grant capabilities and therefore do not occur in this definition. *)
Definition configuration_has_no_capability_amplification
           (g : static_env) (c : agentic_configuration) : Prop :=
  forall lab,
    In lab (boundary_history c) ->
    label_is_capability_bounded
      g (cfg_delegate (agentic_core c))
      (cfg_locality (agentic_core c)) lab.

Lemma has_capability_is_declared g a capability :
  has_capability g a capability ->
  In capability (delegate_capabilities g a).
Proof.
  intros [caps [Hdeclared Hin]].
  unfold delegate_capabilities; rewrite Hdeclared; exact Hin.
Qed.

Lemma singleton_capability_subset g a capability :
  has_capability g a capability ->
  subset [capability] (delegate_capabilities g a).
Proof.
  intros Hcapability selected Hin.
  simpl in Hin; destruct Hin as [-> | Hfalse].
  - now apply has_capability_is_declared.
  - contradiction.
Qed.

(** Each operational constructor discharges exactly the capability demand of
    its boundary label.  The tool rule checks every schema branch and is then
    instantiated at the reported branch.  The runtime rule carries the same
    check explicitly for its trusted lifting. *)
Theorem operational_step_label_is_capability_bounded
        g o invoke run internal old lab new :
  step g o invoke run internal old lab new ->
  label_is_capability_bounded
    g (cfg_delegate old) (cfg_locality old) lab.
Proof.
  intros Hstep; destruct Hstep; simpl.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    unfold delegate_capabilities; assumption.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    now apply singleton_capability_subset.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    now apply singleton_capability_subset.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    now apply singleton_capability_subset.
  - match goal with
    | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Htyping; subst
    end.
    match goal with
    | Hbranches : forall f, In f ?schema -> _,
      Hreported : In reported ?schema |- _ =>
        destruct (Hbranches reported Hreported)
          as [Hadmissible [Hcapabilities Hrest]]
    end.
    unfold delegate_capabilities; exact Hcapabilities.
  - unfold delegate_capabilities; assumption.
  - intros capability Hin; contradiction.
Qed.

Corollary agentic_boundary_step_current_label_is_capability_bounded
          g o invoke run internal old lab new :
  agentic_boundary_step g o invoke run internal old lab new ->
  label_is_capability_bounded
    g (cfg_delegate (agentic_core old))
      (cfg_locality (agentic_core old)) lab.
Proof.
  intros Hagentic.
  apply operational_step_label_is_capability_bounded with
    (o := o) (invoke := invoke) (run := run) (internal := internal)
    (new := agentic_core new).
  exact (agentic_step_core Hagentic).
Qed.

(** History preservation has two cases.  Old labels retain the same bound
    because a boundary step preserves delegate and control locality.  The sole
    appended label is bounded by the operational theorem above. *)
Theorem agentic_boundary_step_preserves_capability_non_amplification
        g o invoke run internal old lab new :
  configuration_has_no_capability_amplification g old ->
  agentic_boundary_step g o invoke run internal old lab new ->
  configuration_has_no_capability_amplification g new.
Proof.
  intros Hold Hagentic recorded Hin.
  rewrite (agentic_step_history Hagentic) in Hin.
  apply in_app_iff in Hin; destruct Hin as [Hin_old | Hin_current].
  - rewrite (agentic_boundary_step_preserves_delegate Hagentic).
    rewrite (agentic_boundary_step_preserves_locality Hagentic).
    now apply Hold.
  - simpl in Hin_current; destruct Hin_current as [Hequal | Hfalse].
    + subst recorded.
      rewrite (agentic_boundary_step_preserves_delegate Hagentic).
      rewrite (agentic_boundary_step_preserves_locality Hagentic).
      eapply agentic_boundary_step_current_label_is_capability_bounded
        with (o := o) (invoke := invoke) (run := run)
             (internal := internal) (old := old) (new := new).
      exact Hagentic.
    + contradiction.
Qed.

(** An empty history contains no opportunity for amplification.  Together with
    one-step preservation, this is the induction base required by the eventual
    reachable-configuration theorem. *)
Lemma initial_configuration_has_no_capability_amplification g c :
  initial_agentic_configuration c ->
  configuration_has_no_capability_amplification g c.
Proof.
  intros [_ [Hhistory _]] lab Hin.
  rewrite Hhistory in Hin; contradiction.
Qed.

(** This elimination form exposes the practical content of the invariant.  If
    a boundary event was recorded and that event demands a capability, then
    the capability is present in the delegate's immutable declaration. *)
Corollary recorded_boundary_capability_is_declared g c lab capability :
  configuration_has_no_capability_amplification g c ->
  In lab (boundary_history c) ->
  In capability
     (boundary_required_capabilities
        (cfg_locality (agentic_core c)) lab) ->
  In capability (delegate_capabilities g (cfg_delegate (agentic_core c))).
Proof.
  intros Hconfined Hlabel Hrequired.
  exact (Hconfined lab Hlabel capability Hrequired).
Qed.

(** The operational relation itself supplies the capability certificate for
    the newly emitted label.  Consequently, clients of the confinement result
    need carry only the invariant for the preceding configuration. *)
Corollary every_agentic_boundary_step_preserves_point6
          g o invoke run internal old lab new :
  configuration_has_no_capability_amplification g old ->
  agentic_boundary_step g o invoke run internal old lab new ->
  configuration_has_no_capability_amplification g new.
Proof.
  intros Hold Hstep.
  eapply agentic_boundary_step_preserves_capability_non_amplification
    with (g := g) (o := o) (invoke := invoke) (run := run)
         (internal := internal) (old := old) (lab := lab).
  - exact Hold.
  - exact Hstep.
Qed.

(** ** Group 7. Source-closed exposure *)

(** An exposure is checked at its exact trace prefix.  The carrier value must
    already be available at the source locality, and the policy must accept
    the flow separately for every value in its reflexive-transitive source
    closure.  Reflexivity ensures that the carrier itself is checked even when
    it has no recorded computation dependencies. *)
Definition source_closed_exposure_at
           (g : static_env) (o : oracle) (a : delegate)
           (prefix : trace) (y : value) (from to : locality) : Prop :=
  available g prefix y from /\
  forall source_value,
    source prefix source_value y ->
    o g prefix (QFlow a source_value from to) = true.

(** The configuration invariant quantifies over every decomposition of the
    persistent trace.  Consequently each exposure is judged using precisely
    the events that preceded it, rather than using sources discovered only
    after the information had crossed the boundary. *)
Definition configuration_has_source_closed_exposure
           (g : static_env) (o : oracle)
           (c : agentic_configuration) : Prop :=
  forall prefix suffix q y from to,
    cfg_trace (agentic_core c) =
      prefix ++ (q, EExpose y from to) :: suffix ->
    source_closed_exposure_at
      g o (cfg_delegate (agentic_core c)) prefix y from to.

(** Closed admissibility contains exactly the two obligations needed for an
    exposure.  This lemma packages their extraction so later proofs do not
    depend on the constructor layout of [event_obligation]. *)
Lemma admissibility_implies_source_closed_exposure
      g o a e :
  admissible g o a e ->
  forall prefix suffix q y from to,
    e = prefix ++ (q, EExpose y from to) :: suffix ->
    source_closed_exposure_at g o a prefix y from to.
Proof.
  intros Hadmissible prefix suffix q y from to Hdecomposition.
  pose proof
    (Hadmissible prefix q (EExpose y from to) suffix Hdecomposition)
    as Hobligation.
  inversion Hobligation; subst; split; assumption.
Qed.

(** The new formulation deliberately strengthens the paper's reusable
    source-sensitive flow conclusion with availability of the carrier.  Its
    policy component therefore projects directly to the earlier theorem. *)
Lemma source_closed_exposure_implies_source_sensitive_flow_safety
      g o a e :
  (forall prefix suffix q y from to,
      e = prefix ++ (q, EExpose y from to) :: suffix ->
      source_closed_exposure_at g o a prefix y from to) ->
  source_sensitive_flow_safety g o a e.
Proof.
  intros Hclosed prefix suffix q y from to Hdecomposition
         source_value Hsource.
  destruct (Hclosed prefix suffix q y from to Hdecomposition)
    as [_ Hflows].
  now apply Hflows.
Qed.

(** Every non-internal operational constructor supplies admissibility of its
    entire result trace.  This is important for calls and runtime events,
    whose fragments may contain several exposures with different intervening
    computations.  An internal step leaves the trace and delegate unchanged,
    so it retains the preceding invariant. *)
Theorem operational_step_preserves_source_closed_exposure
        g o invoke run internal old lab new :
  (forall prefix suffix q y from to,
      cfg_trace old = prefix ++ (q, EExpose y from to) :: suffix ->
      source_closed_exposure_at
        g o (cfg_delegate old) prefix y from to) ->
  step g o invoke run internal old lab new ->
  forall prefix suffix q y from to,
    cfg_trace new = prefix ++ (q, EExpose y from to) :: suffix ->
    source_closed_exposure_at
      g o (cfg_delegate new) prefix y from to.
Proof.
  intros Hold Hstep.
  inversion Hstep; subst; simpl in *.
  - eapply admissibility_implies_source_closed_exposure.
    eapply typed_atomic_admissible; eassumption.
  - eapply admissibility_implies_source_closed_exposure.
    eapply typed_atomic_admissible; eassumption.
  - eapply admissibility_implies_source_closed_exposure.
    eapply typed_atomic_admissible; eassumption.
  - eapply admissibility_implies_source_closed_exposure.
    eapply typed_atomic_admissible; eassumption.
  - eapply admissibility_implies_source_closed_exposure.
    eapply typed_atomic_admissible; eassumption.
  - eapply admissibility_implies_source_closed_exposure; eassumption.
  - exact Hold.
Qed.

(** The wrapper theorem transports the operational result to the strengthened
    configuration.  Boundary history and active contexts need no additional
    premise because source closure is reconstructed from the core trace. *)
Theorem agentic_boundary_step_preserves_source_closed_exposure
        g o invoke run internal old lab new :
  configuration_has_source_closed_exposure g o old ->
  agentic_boundary_step g o invoke run internal old lab new ->
  configuration_has_source_closed_exposure g o new.
Proof.
  intros Hold Hagentic.
  unfold configuration_has_source_closed_exposure in Hold |- *.
  eapply operational_step_preserves_source_closed_exposure
    with (old := agentic_core old) (lab := lab).
  - exact Hold.
  - exact (agentic_step_core Hagentic).
Qed.

(** The empty trace contains no exposure.  This supplies the induction base
    required when point 7 is later combined with the other confinement
    components. *)
Lemma initial_configuration_has_source_closed_exposure g o c :
  initial_agentic_configuration c ->
  configuration_has_source_closed_exposure g o c.
Proof.
  intros [Htrace _] prefix suffix q y from to Hdecomposition.
  rewrite Htrace in Hdecomposition.
  destruct prefix; discriminate Hdecomposition.
Qed.

(** The carrier side of the invariant excludes a transfer whose value was not
    present at the claimed source locality when the transfer occurred. *)
Corollary recorded_exposure_carrier_is_available g o c
          prefix suffix q y from to :
  configuration_has_source_closed_exposure g o c ->
  cfg_trace (agentic_core c) =
    prefix ++ (q, EExpose y from to) :: suffix ->
  available g prefix y from.
Proof.
  intros Hclosed Hdecomposition.
  exact (proj1 (Hclosed prefix suffix q y from to Hdecomposition)).
Qed.

(** This elimination form is the statement used by a security reviewer: for a
    recorded exposure, every transitive source receives an allow decision at
    the historical prefix at which the exposure occurred. *)
Corollary recorded_exposure_allows_every_source g o c
          prefix suffix q y from to source_value :
  configuration_has_source_closed_exposure g o c ->
  cfg_trace (agentic_core c) =
    prefix ++ (q, EExpose y from to) :: suffix ->
  source prefix source_value y ->
  o g prefix
    (QFlow (cfg_delegate (agentic_core c)) source_value from to) = true.
Proof.
  intros Hclosed Hdecomposition Hsource.
  destruct (Hclosed prefix suffix q y from to Hdecomposition)
    as [_ Hflows].
  now apply Hflows.
Qed.

Corollary every_agentic_boundary_step_preserves_point7
          g o invoke run internal old lab new :
  configuration_has_source_closed_exposure g o old ->
  agentic_boundary_step g o invoke run internal old lab new ->
  configuration_has_source_closed_exposure g o new.
Proof.
  exact (@agentic_boundary_step_preserves_source_closed_exposure
           g o invoke run internal old lab new).
Qed.

(** ** Group 8. Boundary fidelity *)

(** A label is a compact public account of a transition.  This relation
    expands each label class to the exact trace suffix it denotes.  Proposal
    and commitment labels omit fields that remain available in their typed
    effects, so their constructors quantify those fields rather than inventing
    defaults. *)
Inductive boundary_label_emits (delegate_loc : locality) :
          boundary_label -> trace -> Prop :=
| BoundaryEmitsObserve : forall q y source,
    boundary_label_emits delegate_loc (LObserve q y source)
      (label q (obs_fragment y source delegate_loc))
| BoundaryEmitsDerive : forall q y sources,
    boundary_label_emits delegate_loc (LDerive q y sources)
      [(q, ECompute sources y delegate_loc)]
| BoundaryEmitsPropose : forall q p w d,
    boundary_label_emits delegate_loc (LPropose q p d)
      [(q, ECompute [w; d] p delegate_loc)]
| BoundaryEmitsCommit : forall q p w d alpha,
    boundary_label_emits delegate_loc (LCommit q p alpha)
      [(q, ECommit p w d alpha delegate_loc)]
| BoundaryEmitsCall : forall q t inputs results eta reported,
    boundary_label_emits delegate_loc
      (LCall q t inputs results eta reported) (label q reported)
| BoundaryEmitsRuntime : forall mu,
    boundary_label_emits delegate_loc (LRuntime mu)
      (label (runtime_context mu) (lift mu))
| BoundaryEmitsInternal : forall tag,
    boundary_label_emits delegate_loc (LInternal tag) [].

(** Typing fixes the public label and emitted suffix simultaneously.  This
    lemma prevents a later operational proof from pairing a checked action
    with the effects of another action. *)
Lemma typed_atomic_emits_its_boundary_label
      g o a delegate_loc q dlt e action added_events dlt' :
  typed_atomic g o a delegate_loc q dlt e action added_events dlt' ->
  boundary_label_emits delegate_loc
    (atomic_boundary_label q action) added_events.
Proof.
  intros Htyping; destruct Htyping; simpl.
  - subst f; constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
Qed.

(** The operational constructors preserve the same identity at the state
    boundary: the successor trace is the predecessor trace followed by the
    suffix denoted by the emitted label. *)
Lemma operational_step_emits_its_boundary_label
      g o invoke run internal old lab new :
  step g o invoke run internal old lab new ->
  exists added_events,
    boundary_label_emits (cfg_locality old) lab added_events /\
    exact_trace_extension (cfg_trace old) (cfg_trace new) added_events.
Proof.
  intros Hstep; destruct Hstep; simpl.
  - exists f; split.
    + change (boundary_label_emits ld
        (atomic_boundary_label q (AObserve y source)) f).
      eapply typed_atomic_emits_its_boundary_label; eassumption.
    + reflexivity.
  - exists f; split.
    + change (boundary_label_emits ld
        (atomic_boundary_label q (ADerive y t sources)) f).
      eapply typed_atomic_emits_its_boundary_label; eassumption.
    + reflexivity.
  - exists f; split.
    + change (boundary_label_emits ld
        (atomic_boundary_label q (APropose p w d)) f).
      eapply typed_atomic_emits_its_boundary_label; eassumption.
    + reflexivity.
  - exists f; split.
    + change (boundary_label_emits ld
        (atomic_boundary_label q (ACommit p w d alpha)) f).
      eapply typed_atomic_emits_its_boundary_label; eassumption.
    + reflexivity.
  - exists (label q reported); split; [constructor | reflexivity].
  - exists (label (runtime_context mu) (lift mu));
      split; [constructor | reflexivity].
  - exists []; split; [constructor |].
    unfold exact_trace_extension; now rewrite app_nil_r.
Qed.

(** Interface fidelity retains the fields whose equality matters across a
    trusted boundary.  For a tool call, the descriptor fixes the backend
    locality and result type; the checked schema member, metadata, inputs,
    results, proposal guard, and invocation tuple are identical.  For a
    runtime event, the adapter transition, execute stage, committed wrapper,
    and exact environment update all use the same event [mu]. *)
Definition boundary_interface_is_faithful
           (g : static_env) (o : oracle)
           (invoke : invocation_semantics)
           (run : runtime_semantics)
           (internal : internal_semantics)
           (old : configuration) (lab : boundary_label)
           (new : configuration) : Prop :=
  match lab with
  | LCall q t inputs results eta reported =>
      exists td out_bindings,
        tool_decl g t = Some td /\
        result_bindings q results (output_type td) out_bindings /\
        In reported (effect_schema td inputs results eta) /\
        o g (cfg_trace old)
          (QCall (cfg_delegate old) t (cfg_locality old)
                 (tool_locality td) eta) = true /\
        call_guard (cfg_dynamic old) (cfg_trace old) q reported inputs /\
        binds_exactly reported results /\
        invoke (cfg_runtime old) t inputs results eta reported
               (cfg_runtime new)
  | LRuntime mu =>
      run (cfg_runtime old) mu (cfg_runtime new) /\
      stage_of (cfg_dynamic old) (cfg_trace old)
               (runtime_context mu) ExecuteStage /\
      (exists alpha lc,
          In (runtime_context mu,
              ECommit (runtime_proposal mu) (runtime_workflow mu)
                      (runtime_patch mu) alpha lc)
             (cfg_trace old)) /\
      runtime_environment_update
        g (cfg_dynamic old) (cfg_trace old) mu (cfg_dynamic new)
  | LInternal tag =>
      internal (cfg_runtime old) tag (cfg_runtime new)
  | _ => True
  end.

(** The complete certificate joins interface identity with the exact binding
    and trace delta from point 3.  Requiring one common [added_events] witness
    prevents the label account and the production account from describing
    different suffixes. *)
Record exact_boundary_fidelity
       (g : static_env) (o : oracle)
       (invoke : invocation_semantics)
       (run : runtime_semantics)
       (internal : internal_semantics)
       (old : configuration) (lab : boundary_label)
       (new : configuration) : Prop := {
  boundary_fidelity_interface :
    boundary_interface_is_faithful g o invoke run internal old lab new;
  boundary_fidelity_exact_delta :
    exists added_bindings added_events,
      label_output_bindings lab added_bindings /\
      boundary_label_emits (cfg_locality old) lab added_events /\
      exact_production_delta
        (cfg_dynamic old) (cfg_dynamic new)
        (cfg_trace old) (cfg_trace new)
        added_bindings added_events
}.

(** The older boundary theorem is a projection of the stronger certificate:
    its call case retains invocation identity and the production-stage guard,
    while its runtime case retains the execute-stage fact. *)
Lemma exact_boundary_fidelity_implies_faithful_transition
      g o invoke run internal old lab new :
  exact_boundary_fidelity g o invoke run internal old lab new ->
  faithful_transition invoke old lab new.
Proof.
  intros Hfidelity; destruct Hfidelity as [Hinterface Hdelta].
  destruct lab; simpl in *; try exact I.
  - destruct Hinterface as
      [td [bindings [Hdeclared [Hresults [Hschema [Hquery
       [Hguard [Hbinds Hinvoke]]]]]]]].
    split; [exact Hinvoke |].
    eapply call_guard_production_stage; exact Hguard.
  - tauto.
Qed.

(** Every operational step constructs the complete fidelity certificate.  The
    suffix witness from the label theorem is equal to the suffix witness from
    the production delta because both extend the same prefix to the same
    successor trace. *)
Theorem every_operational_step_has_exact_boundary_fidelity
        g o invoke run internal old lab new :
  step g o invoke run internal old lab new ->
  exact_boundary_fidelity g o invoke run internal old lab new.
Proof.
  intros Hstep; constructor.
  - destruct Hstep; simpl; try exact I.
    + match goal with
      | Htyping : typed_atomic _ _ _ _ _ _ _ _ _ _ |- _ =>
          inversion Htyping; subst
      end.
      match goal with
      | Hbranches : forall f, In f ?schema -> _ ,
        Hreported : In reported ?schema |- _ =>
          destruct (Hbranches reported Hreported)
            as [Hbranch_admissible
                [Hbranch_capabilities
                 [Hbranch_guard [Hbranch_binds Hbranch_provenance]]]]
      end.
      exists td, out_bindings.
      split; [assumption |].
      split; [assumption |].
      split; [assumption |].
      split; [assumption |].
      split; [exact Hbranch_guard |].
      split; [exact Hbranch_binds | assumption].
    + split; [assumption |].
      split; [assumption |].
      split.
      * eauto.
      * assumption.
    + assumption.
  - destruct (every_operational_step_constructs_exact_production_delta Hstep)
      as [bindings [delta_events [Hbindings Hdelta]]].
    destruct (operational_step_emits_its_boundary_label Hstep)
      as [label_events [Hemits Htrace]].
    assert (Hevents : delta_events = label_events).
    { apply app_inv_head with (l := cfg_trace old).
      rewrite <- (production_delta_trace Hdelta).
      exact Htrace. }
    subst label_events.
    exists bindings, delta_events.
    split; [exact Hbindings |].
    split; [exact Hemits | exact Hdelta].
Qed.

(** The strengthened wrapper adds the exact public history update and active
    context preservation to the core fidelity certificate. *)
Definition agentic_step_has_exact_boundary_fidelity
           g o invoke run internal old lab new : Prop :=
  exact_boundary_fidelity
    g o invoke run internal (agentic_core old) lab (agentic_core new) /\
  boundary_history new = boundary_history old ++ [lab] /\
  active_contexts new = active_contexts old.

Theorem every_agentic_boundary_step_has_exact_boundary_fidelity
        g o invoke run internal old lab new :
  agentic_boundary_step g o invoke run internal old lab new ->
  agentic_step_has_exact_boundary_fidelity
    g o invoke run internal old lab new.
Proof.
  intros Hagentic.
  unfold agentic_step_has_exact_boundary_fidelity.
  split.
  - apply every_operational_step_has_exact_boundary_fidelity.
    exact (agentic_step_core Hagentic).
  - split.
    + exact (agentic_step_history Hagentic).
    + exact (agentic_step_active_contexts Hagentic).
Qed.

Corollary every_agentic_boundary_step_satisfies_point8
          g o invoke run internal old lab new :
  agentic_boundary_step g o invoke run internal old lab new ->
  agentic_step_has_exact_boundary_fidelity
    g o invoke run internal old lab new.
Proof.
  exact (@every_agentic_boundary_step_has_exact_boundary_fidelity
           g o invoke run internal old lab new).
Qed.

(** ** Group 9. Combined one-step confinement *)

(** A strengthened boundary step preserves every component on which stage
    reconstruction depends.  Exact trace and environment extension were
    established by the production bridge; the wrapper supplies equality of
    delegate, locality, and active-context lists.  Distinctness of the target
    active list follows from source well-formedness because no context is
    created by an existing-context step. *)
Lemma agentic_boundary_step_is_well_formed_stage_extension
      g o invoke run internal old lab new :
  well_formed_configuration g old ->
  agentic_boundary_step g o invoke run internal old lab new ->
  well_formed_exact_stage_extension g old new.
Proof.
  intros Hwell_formed Hagentic; split; [exact Hwell_formed |].
  constructor.
  - exact (agentic_boundary_step_preserves_delegate Hagentic).
  - exact (agentic_boundary_step_preserves_locality Hagentic).
  - exact (agentic_boundary_step_trace_extends Hagentic).
  - exact (agentic_boundary_step_dynamic_extends Hagentic).
  - exists []; split.
    + rewrite app_nil_r; exact (agentic_step_active_contexts Hagentic).
    + rewrite (agentic_step_active_contexts Hagentic).
      exact (wf_active_contexts_distinct Hwell_formed).
Qed.

(** The conclusion record names the independent guarantees rather than hiding
    them in a deeply nested conjunction.  This shape lets later proofs select
    one security fact without destructing unrelated evidence. *)
Record hard_klaim_one_step_guarantees
       (g : static_env) (o : oracle)
       (invoke : invocation_semantics)
       (run : runtime_semantics)
       (internal : internal_semantics)
       (old : agentic_configuration) (lab : boundary_label)
       (new : agentic_configuration) : Prop := {
  confinement_stage_extension :
    well_formed_exact_stage_extension g old new;

  confinement_target_stage_deterministic :
    forall q first second,
      active_stage new q first ->
      active_stage new q second ->
      first = second;

  confinement_stage_monotone :
    forall q before after,
      active_stage old q before ->
      active_stage new q after ->
      before <=s after;

  confinement_single_assignment :
    single_assignment (cfg_dynamic (agentic_core new));

  confinement_unique_production :
    every_dynamic_binding_has_unique_producer
      (cfg_dynamic (agentic_core new))
      (cfg_trace (agentic_core new));

  confinement_conservative_provenance :
    configuration_has_conservative_provenance g new;

  confinement_exact_proposal_approval_commitment :
    exact_proposal_approval_commitment_binding g new;

  confinement_capability_non_amplification :
    configuration_has_no_capability_amplification g new;

  confinement_source_closed_exposure :
    configuration_has_source_closed_exposure g o new;

  confinement_exact_boundary_fidelity :
    agentic_step_has_exact_boundary_fidelity
      g o invoke run internal old lab new
}.

(** [hard_klaim_one_step_confinement] gives the intuitive security meaning of
    one admitted Hard-KLAIM boundary transition.  It starts from the full
    configuration discipline of point 1, the accumulated origin invariant of
    point 4, the immutable-authority invariant of point 6, and the historical
    exposure invariant of point 7.  The transition is an
    [agentic_boundary_step], so its operational step, public label, boundary
    history, and active-context update are tied together.

    The conclusion says that protocol stages remain uniquely determined and
    cannot move backwards; dynamic names retain single assignment and one
    exact producer; model, tool, and runtime results retain conservative
    origins; proposals, verified approvals, commitments, and production
    actions retain one matching immutable tuple; no recorded event gains a
    capability absent from the delegate declaration; and every exposure is
    checked for its complete transitive source closure at the prefix where it
    occurs.  Finally, exact boundary fidelity connects the checked tool or
    runtime interface, the emitted public label, the appended trace effects,
    and the installed output bindings.  Thus the theorem constrains what the
    boundary records and authorises, without claiming correctness of an LLM's
    private reasoning or of an implementation outside the trusted adapters. *)
Theorem hard_klaim_one_step_confinement
        g o invoke run internal old lab new :
  well_formed_configuration g old ->
  configuration_has_conservative_provenance g old ->
  configuration_has_no_capability_amplification g old ->
  configuration_has_source_closed_exposure g o old ->
  agentic_boundary_step g o invoke run internal old lab new ->
  hard_klaim_one_step_guarantees
    g o invoke run internal old lab new.
Proof.
  intros Hwell_formed Hprovenance Hcapabilities Hexposure Hagentic.
  assert (Hstage : well_formed_exact_stage_extension g old new).
  { eapply agentic_boundary_step_is_well_formed_stage_extension; eassumption. }
  destruct (@every_well_formed_operational_step_preserves_point3
              g o invoke run internal old lab new
              Hwell_formed (agentic_step_core Hagentic))
    as [Hsingle_assignment Hunique_production].
  constructor.
  - exact Hstage.
  - intros q first second Hfirst Hsecond.
    eapply active_stage_deterministic; eassumption.
  - intros q before after Hbefore Hafter.
    eapply active_stage_monotone; eassumption.
  - exact Hsingle_assignment.
  - exact Hunique_production.
  - eapply agentic_boundary_step_preserves_conservative_provenance;
      eassumption.
  - eapply every_well_formed_agentic_boundary_step_preserves_point5;
      eassumption.
  - eapply agentic_boundary_step_preserves_capability_non_amplification;
      eassumption.
  - eapply agentic_boundary_step_preserves_source_closed_exposure;
      eassumption.
  - eapply every_agentic_boundary_step_has_exact_boundary_fidelity;
      eassumption.
Qed.
