(** * Core trace-safety consequences of reachable configurations

    This file states and proves the reusable core result feeding the final
    trace theorem in Section 7.4.
    The proof factors through reusable lemmas: reachability preserves closed
    admissibility; admissibility gives exact commitment order, fresh supported
    computations, and source-sensitive flow; well-formedness connects a
    historical commitment to the persistent proposal binding and verified
    proposal-specific evidence. *)

(** ** Correspondence with [GianluigiFerrari_tribute_2026.pdf]

    [state_consistent] is a compact core form of the proposal-binding and
    verified-evidence clauses later collected in Definitions 22 and 26
    (PDF pp. 24--25).  [compute_provenance_safety],
    [exact_typed_commitment_safety], and their admissibility lemmas map to the
    safety properties in Section 6.2 (PDF p. 21, equations (8)--(9)).

    [trace_safety] and [trace_safety_exact_order] establish these consequences
    for the unstrengthened reachability relation.  They are proof components of
    the final finite-run argument, not the whole of Theorem 2.
    The exact paper-level correspondence to Definitions 27--30 and Theorem 2
    is completed in [trace_safety.v] (PDF pp. 26--27).  The intermediate
    lemmas here are technical components of the full mechanized proof. *)

From Coq Require Import Lists.List.
From Janji Require Import Prelude Syntax Trace Policy Typing Semantics.
Import ListNotations.

Definition state_consistent (g : static_env) (c : configuration) : Prop :=
  forall q p w d alpha l,
    In (q, ECommit p w d alpha l) (cfg_trace c) ->
    cfg_dynamic c q p = Some (TyProposal w d) /\
    evidence_ok g alpha (cfg_delegate c) q p w d = true.

Definition well_formed_reachable g o invoke run internal c0 labels c : Prop :=
  reaches g o invoke run internal c0 labels c /\ state_consistent g c.

Definition compute_provenance_safety (g : static_env) (e : trace) : Prop :=
  forall prefix suffix q sources y l,
    e = prefix ++ (q, ECompute sources y l) :: suffix ->
    fresh g prefix y /\
    forall x, In x sources -> available g prefix x l.

Definition exact_typed_commitment_safety (g : static_env)
           (c : configuration) : Prop :=
  forall q p k w d y l,
    In (q, EAct p k w d y l) (cfg_trace c) ->
    exists alpha lc,
      occurs_before (q, ECommit p w d alpha lc)
                    (q, EAct p k w d y l) (cfg_trace c) /\
      cfg_dynamic c q p = Some (TyProposal w d) /\
      evidence_ok g alpha (cfg_delegate c) q p w d = true.

Lemma admissible_compute_provenance g o a e :
  admissible g o a e -> compute_provenance_safety g e.
Proof.
  intros Hadm prefix suffix q sources y l Heq.
  eapply compute_sources_available_from_admissibility; eauto.
Qed.

Lemma admissible_exact_typed_commitment g o c :
  admissible g o (cfg_delegate c) (cfg_trace c) ->
  state_consistent g c ->
  exact_typed_commitment_safety g c.
Proof.
  intros Hadm Hconsistent q p k w d y l Hact.
  destruct (@exact_commitment_from_admissibility
              g o (cfg_delegate c) (cfg_trace c) q p k w d y l Hadm Hact)
    as [alpha [lc [Hcommit Hbefore]]].
  specialize (Hconsistent q p w d alpha lc Hcommit) as [Hbinding Hevidence].
  exists alpha, lc; auto.
Qed.

(** Main theorem.  The assumptions correspond directly to the paper: the
    initial trace is empty, the boundary run is well formed, declarations and
    schemas are represented by [g], and the oracle/adapter are the parameters
    [o], [invoke], and [run]. *)
Theorem trace_safety g o invoke run internal c0 labels c :
  cfg_trace c0 = [] ->
  well_formed_reachable g o invoke run internal c0 labels c ->
  exact_typed_commitment_safety g c /\
  compute_provenance_safety g (cfg_trace c) /\
  source_sensitive_flow_safety g o (cfg_delegate c) (cfg_trace c).
Proof.
  intros Hinitial [Hreach Hconsistent].
  pose proof (@reachable_trace_admissible
    g o invoke run internal c0 labels c Hinitial Hreach) as Hadm.
  split.
  - eapply admissible_exact_typed_commitment; eauto.
  - split.
    + eapply admissible_compute_provenance; eauto.
    + apply (proj2 (@admissibility_implies_static_safety
        g o (cfg_delegate c) (cfg_trace c) Hadm)).
Qed.

Corollary trace_safety_exact_order g o invoke run internal c0 labels c :
  cfg_trace c0 = [] ->
  well_formed_reachable g o invoke run internal c0 labels c ->
  exact_commitment_safety (cfg_trace c).
Proof.
  intros Hinitial [Hreach _].
  pose proof (@reachable_trace_admissible
    g o invoke run internal c0 labels c Hinitial Hreach) as Hadm.
  apply (proj1 (@admissibility_implies_static_safety
    g o (cfg_delegate c) (cfg_trace c) Hadm)).
Qed.

Print Assumptions trace_safety.
