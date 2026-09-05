(** * Trace safety by induction over confined boundary steps

    The one-step theorem proves all security-bearing preservation clauses, but
    the operational relation deliberately leaves several deployment facts to
    the trusted boundary: declarations must cover newly mentioned localities,
    emitted contexts must be active, and the finite wrapper history must remain
    structurally coherent.  This module names those residual obligations,
    reconstructs full well-formedness after each step, and performs the final
    induction.

    The proof is organised as follows.

    - [configuration_administrative_closure] isolates the structural facts
      that the security theorem cannot infer from an abstract adapter.
    - [reconstruct_well_formed_configuration] combines those facts with the
      one-step security conclusions to recover full configuration
      well-formedness.
    - [hard_klaim_trace_invariant] identifies the facts that must be available
      before every induction step.
    - [hard_klaim_certified_reaches] represents a finite sequence whose
      successor configurations discharge the structural boundary facts.
    - [hard_klaim_trace_invariant_by_induction] applies
      [hard_klaim_one_step_confinement] at each transition and reconstructs the
      invariant needed by the following transition.
    - [hard_klaim_final_trace_safety] exposes the security properties of the
      reached configuration, while its final corollary supplies the
      paper-shaped initial-state interface. *)

(** ** Correspondence with [GianluigiFerrari_tribute_2026.pdf]

    This module is the detailed mechanization of Section 7.4.2 (physical PDF
    pp. 26--27).  [configuration_administrative_closure] maps to Definition 28,
    Administrative closure.  [hard_klaim_trace_invariant] maps to Definition
    29, Persistent trace invariant.  [hard_klaim_certified_reaches] maps to
    Definition 30, Administratively closed finite reachability.

    [hard_klaim_trace_invariant_by_induction] maps to the induction described
    in the proof of Theorem 2 (PDF p. 27).  The records and theorems
    [hard_klaim_trace_safety_guarantees], [hard_klaim_final_trace_safety], and
    [hard_klaim_final_trace_safety_from_initial_configuration] together map to
    Theorem 2, Trace safety (PDF pp. 26--27).  Interface adequacy, Definition
    27, is represented forgetfully by the authoritative static environment,
    policy oracle, invocation relation, runtime relation, and adapter premises
    parameterizing the imported semantics rather than by a duplicated record.

    Reconstruction and base-case lemmas have no individual paper labels.  They
    are the Rocq-specific proof packaging needed to realize the induction
    described in the proof paragraph. *)

From Coq Require Import Lists.List.
From Janji Require Import Prelude Syntax Trace Policy Typing Semantics
  one_step_agentic_provenance_and_authority_confinement.
Import ListNotations.

Set Implicit Arguments.

(** ** Administrative closure of a target configuration *)

(** These are exactly the target clauses of [well_formed_configuration] not
    supplied by the security conclusions of
    [hard_klaim_one_step_confinement].  Keeping them in a separate record makes
    the trusted deployment boundary visible.  In a concrete implementation
    they are discharged by finite declaration lookup, context ownership, and
    the wrapper that records boundary labels. *)
Record configuration_administrative_closure
       (g : static_env) (c : agentic_configuration) : Prop := {
  (** A finite active-context list is a set representation.  Distinctness
      prevents one logical context from being counted as two activations. *)
  administrative_active_contexts_distinct :
    NoDup (active_contexts c);

  (** The running delegate must have an immutable capability declaration. *)
  administrative_delegate_declared :
    exists caps, delegate_caps g (cfg_delegate (agentic_core c)) = Some caps;

  (** Every protection domain mentioned by the accumulated effects must occur
      in the authoritative locality declaration. *)
  administrative_localities_declared :
    trace_uses_declared_localities g (cfg_trace (agentic_core c));

  (** A dynamic binding cannot inhabit a context absent from the finite active
      set. *)
  administrative_dynamic_contexts_active :
    forall q y t,
      cfg_dynamic (agentic_core c) q y = Some t -> active_context c q;

  (** The same coverage condition is required for context-labelled effects. *)
  administrative_trace_contexts_active :
    forall q eff,
      In (q, eff) (cfg_trace (agentic_core c)) -> active_context c q;

  (** Boundary labels and trace events must agree on which delegation contexts
      are live. *)
  administrative_history_contexts_active :
    forall lab q,
      In lab (boundary_history c) ->
      label_context lab = Some q -> active_context c q;

  (** A dynamically produced name may not alias a static or initially placed
      authoritative name. *)
  administrative_dynamic_names_fresh :
    dynamic_names_are_fresh_from_static
      g (cfg_dynamic (agentic_core c));

  (** Every installed name has one boundary origin, so a later event cannot
      retroactively reinterpret who produced it. *)
  administrative_dynamic_names_have_one_origin :
    forall q y t,
      cfg_dynamic (agentic_core c) q y = Some t ->
      has_unique_origin (boundary_history c) q y;

  (** Execution stage is reached through one recorded production call rather
      than through several competing call histories. *)
  administrative_execution_has_one_call :
    forall q,
      has_context_act (cfg_trace (agentic_core c)) q ->
      has_unique_production_call (boundary_history c) q
}.

(** Point 9 supplies the three non-administrative portions of the target
    well-formedness record: global single assignment, one producer for every
    installed name, and the exact proposal--approval--commitment discipline.
    Combining them with administrative closure recovers the complete record
    required as the source premise of the next induction step.  This bridge is
    necessary because [hard_klaim_one_step_confinement] proves the security
    effects of a transition but does not manufacture authoritative locality or
    context declarations that belong to the deployment. *)
Lemma reconstruct_well_formed_configuration
      g c :
  configuration_administrative_closure g c ->
  single_assignment (cfg_dynamic (agentic_core c)) ->
  every_dynamic_binding_has_unique_producer
    (cfg_dynamic (agentic_core c)) (cfg_trace (agentic_core c)) ->
  exact_proposal_approval_commitment_binding g c ->
  well_formed_configuration g c.
Proof.
  intros Hadministrative Hsingle Hproduction Hexact_authority.
  destruct Hadministrative.
  destruct Hexact_authority as [Hproposals [Hcommitments Hactions]].
  constructor; assumption.
Qed.

(** ** Persistent trace invariant and certified reachability *)

(** This is the induction invariant.  Full well-formedness supplies the source
    discipline required by the next one-step theorem.  Conservative provenance
    records a justified lower bound for model, tool, and runtime dependencies;
    capability non-amplification confines every recorded boundary operation to
    the delegate declaration; and source-closed exposure retains the exact
    prefix-sensitive flow checks.  These fields are stored together because
    all four are needed to invoke point 9 at the following transition. *)
Record hard_klaim_trace_invariant
       (g : static_env) (o : oracle)
       (c : agentic_configuration) : Prop := {
  trace_invariant_well_formed : well_formed_configuration g c;
  trace_invariant_conservative_provenance :
    configuration_has_conservative_provenance g c;
  trace_invariant_capability_non_amplification :
    configuration_has_no_capability_amplification g c;
  trace_invariant_source_closed_exposure :
    configuration_has_source_closed_exposure g o c
}.

(** With empty boundary history there is no origin whose provenance must be
    justified.  This is the point-4 base case used below. *)
Lemma initial_configuration_has_conservative_provenance
      g c :
  initial_agentic_configuration c ->
  configuration_has_conservative_provenance g c.
Proof.
  intros Hinitial q y origin Horigin.
  exfalso.
  eapply initial_configuration_has_no_origins; eassumption.
Qed.

(** A well-formed initial configuration automatically supplies the complete
    trace invariant.  The three historical security clauses are vacuous
    because both its trace and boundary history are empty. *)
Lemma well_formed_initial_configuration_has_trace_invariant
      g o c :
  well_formed_configuration g c ->
  initial_agentic_configuration c ->
  hard_klaim_trace_invariant g o c.
Proof.
  intros Hwell_formed Hinitial; constructor.
  - exact Hwell_formed.
  - now apply initial_configuration_has_conservative_provenance.
  - now apply initial_configuration_has_no_capability_amplification.
  - now apply initial_configuration_has_source_closed_exposure.
Qed.

(** A certified finite run records ordinary strengthened boundary steps and
    requires the administrative closure certificate for each successor.  The
    relation is the trace-level bridge between a single transition and a
    finite execution: its label list records order, its step premise provides
    the operational evidence, and its closure premise makes the successor
    eligible to become the source of the next step.  It does not assume the
    security conclusions; those are derived during induction. *)
Inductive hard_klaim_certified_reaches
          (g : static_env) (o : oracle)
          (invoke : invocation_semantics)
          (run : runtime_semantics)
          (internal : internal_semantics)
          (initial : agentic_configuration) :
          list boundary_label -> agentic_configuration -> Prop :=
| HardKlaimReachesRefl :
    hard_klaim_certified_reaches
      g o invoke run internal initial [] initial
| HardKlaimReachesStep : forall labels old lab new,
    hard_klaim_certified_reaches
      g o invoke run internal initial labels old ->
    agentic_boundary_step g o invoke run internal old lab new ->
    configuration_administrative_closure g new ->
    hard_klaim_certified_reaches
      g o invoke run internal initial (labels ++ [lab]) new.

(** This is the induction kernel of the final theorem.  At the successor
    case, [hard_klaim_one_step_confinement] produces every security component;
    [reconstruct_well_formed_configuration] joins its single-assignment,
    production, and authority conclusions with administrative closure so the
    induction hypothesis can be advanced again. *)
Theorem hard_klaim_trace_invariant_by_induction
        g o invoke run internal initial labels final :
  hard_klaim_trace_invariant g o initial ->
  hard_klaim_certified_reaches
    g o invoke run internal initial labels final ->
  hard_klaim_trace_invariant g o final.
Proof.
  intros Hinitial Hreaches; induction Hreaches.
  - exact Hinitial.
  - destruct IHHreaches as
      [Hold_well_formed Hold_provenance Hold_capabilities Hold_exposure].
    pose proof
      (@hard_klaim_one_step_confinement
         g o invoke run internal old lab new
         Hold_well_formed Hold_provenance Hold_capabilities Hold_exposure H)
      as Hone_step.
    assert (Hnew_well_formed : well_formed_configuration g new).
    { eapply reconstruct_well_formed_configuration.
      - exact H0.
      - exact (confinement_single_assignment Hone_step).
      - exact (confinement_unique_production Hone_step).
      - exact (confinement_exact_proposal_approval_commitment Hone_step). }
    constructor.
    + exact Hnew_well_formed.
    + exact (confinement_conservative_provenance Hone_step).
    + exact (confinement_capability_non_amplification Hone_step).
    + exact (confinement_source_closed_exposure Hone_step).
Qed.

(** ** Final trace-safety statement *)

(** The final record presents the safety consequences at the endpoint of a
    finite run.

    - The persistent invariant supplies well-formedness, conservative
      provenance, capability non-amplification, and source-closed exposure.
    - Stage determinism makes the protocol position of an active context
      unambiguous.
    - Single assignment prevents rebinding a dynamic name in any context.
    - Unique production gives every installed name exactly one producing
      computation in the trace.
    - Exact proposal authority binds proposal production, verified approval,
      commitment, and subsequent production action to the same workflow and
      patch. *)
Record hard_klaim_trace_safety_guarantees
       (g : static_env) (o : oracle)
       (c : agentic_configuration) : Prop := {
  trace_safety_persistent_invariant : hard_klaim_trace_invariant g o c;
  trace_safety_stage_deterministic :
    forall q first second,
      active_stage c q first -> active_stage c q second -> first = second;
  trace_safety_single_assignment :
    single_assignment (cfg_dynamic (agentic_core c));
  trace_safety_unique_production :
    every_dynamic_binding_has_unique_producer
      (cfg_dynamic (agentic_core c)) (cfg_trace (agentic_core c));
  trace_safety_exact_proposal_authority :
    exact_proposal_approval_commitment_binding g c
}.

(** [hard_klaim_final_trace_safety] is the finite-trace form of confinement.
    Starting from a configuration satisfying the complete invariant, every
    administratively certified sequence of strengthened Hard-KLAIM boundary
    steps ends in a well-formed configuration.  All model, tool, and runtime
    outputs retain conservative recorded origins; proposal use remains bound
    to the exact verified approval and prior commitment; no boundary event
    amplifies the delegate's immutable capabilities; and every exposure is
    authorised for the full reflexive-transitive source closure at its exact
    historical prefix.  Active stages are unambiguous, and every installed
    dynamic name has one type and one producing computation.  In summary, the
    reached configuration guarantees:

    - complete configuration well-formedness;
    - deterministic active protocol stages;
    - global single assignment and unique production;
    - conservative model, tool, and runtime provenance;
    - exact proposal--approval--commitment authority;
    - capability non-amplification; and
    - source-closed exposure.

    The theorem is conditional only on the explicit authoritative interfaces
    of the calculus and on [configuration_administrative_closure] at each
    successor.  It does not assume any of the security conclusions that it
    proves, and it does not assert correctness of behaviour omitted by a tool
    schema or trusted runtime adapter. *)
Theorem hard_klaim_final_trace_safety
        g o invoke run internal initial labels final :
  hard_klaim_trace_invariant g o initial ->
  hard_klaim_certified_reaches
    g o invoke run internal initial labels final ->
  hard_klaim_trace_safety_guarantees g o final.
Proof.
  intros Hinitial Hreaches.
  pose proof
    (@hard_klaim_trace_invariant_by_induction
       g o invoke run internal initial labels final Hinitial Hreaches)
    as Hfinal.
  destruct Hfinal as
    [Hwell_formed Hprovenance Hcapabilities Hexposure].
  constructor.
  - constructor; assumption.
  - intros q first second Hfirst Hsecond.
    eapply active_stage_deterministic; eassumption.
  - exact (wf_dynamic_names_global Hwell_formed).
  - exact (wf_dynamic_names_produced_once Hwell_formed).
  - now apply well_formed_configuration_has_exact_proposal_approval_commitment.
Qed.

(** This corollary has the shape used by the paper.  It replaces the abstract
    initial trace invariant in the main theorem with the two facts a reader
    normally supplies: the initial trace and dynamic contexts are empty, and
    the initial configuration is well formed.  The base-case lemmas derive the
    otherwise vacuous provenance, capability-history, and exposure-history
    fields before the same induction is applied. *)
Corollary hard_klaim_final_trace_safety_from_initial_configuration
          g o invoke run internal initial labels final :
  well_formed_configuration g initial ->
  initial_agentic_configuration initial ->
  hard_klaim_certified_reaches
    g o invoke run internal initial labels final ->
  hard_klaim_trace_safety_guarantees g o final.
Proof.
  intros Hwell_formed Hinitial Hreaches.
  eapply hard_klaim_final_trace_safety; [| exact Hreaches].
  now apply well_formed_initial_configuration_has_trace_invariant.
Qed.

Print Assumptions hard_klaim_final_trace_safety.
Print Assumptions hard_klaim_final_trace_safety_from_initial_configuration.
