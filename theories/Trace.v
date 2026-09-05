(** * Trace projections, provenance, and protocol stage

    A context-labelled trace is the persistent security history.  Availability,
    proposal provenance, exact ordering, dependencies, source closure, and the
    four protocol stages are projections of this history; they are not mutable
    auxiliary stores. *)

(** ** Correspondence with [GianluigiFerrari_tribute_2026.pdf]

    [available], [produced], and [fresh] map to the availability and freshness
    notation following Definition 11 (PDF pp. 16--17).  [proposed] and
    [occurs_before] map to effect order and exact commitment binding,
    Definition 16 (PDF p. 18).  [direct_dependency] and its reflexive-
    transitive closure [source] map to Dependency relation and source closure,
    Definition 12 (PDF p. 17).  The dominance-ordered [stage_of] constructors
    map to the four-stage protocol of Definition 5 (PDF p. 13) and its derived
    trace formulation on PDF pp. 16--17.

    The closing lemmas establish list-level properties needed by later proofs.
    They are proof-engineering steps supporting the monotonicity and
    reflexivity observations surrounding Definitions 11--12. *)

From Coq Require Import Lists.List.
From Janji Require Import Prelude Syntax.
Import ListNotations.

Inductive available (g : static_env) (e : trace) : value -> locality -> Prop :=
| AvInitial : forall y l, initial_placement g y l = true -> available g e y l
| AvRead : forall y l q, In (q, ERead y l) e -> available g e y l
| AvCompute : forall s y l q, In (q, ECompute s y l) e -> available g e y l
| AvExpose : forall y l1 l2 q, In (q, EExpose y l1 l2) e -> available g e y l2.

Definition produced (e : trace) (y : value) : Prop :=
  exists q s l, In (q, ECompute s y l) e.

Definition fresh (g : static_env) (e : trace) (y : value) : Prop :=
  static_type g y = None /\
  (forall l, initial_placement g y l = false) /\
  ~ produced e y.

Definition proposed (e : trace) (q : context) (p : proposal)
                    (w : workflow) (d : patch) : Prop :=
  exists l, In (q, ECompute [w; d] p l) e.

Inductive direct_dependency (e : trace) : value -> value -> Prop :=
| DirectDependency : forall q l sources x y,
    In (q, ECompute sources y l) e ->
    In x sources ->
    direct_dependency e x y.

Inductive source (e : trace) : value -> value -> Prop :=
| SourceRefl : forall y, source e y y
| SourceStep : forall x y z,
    direct_dependency e x y -> source e y z -> source e x z.

Definition occurs_before (first second : event) (e : trace) : Prop :=
  exists prefix suffix,
    e = prefix ++ second :: suffix /\ In first prefix.

Definition effects_in (q : context) (e : trace) (eff : effect) : Prop :=
  In (q, eff) e.

Definition has_context_act (e : trace) (q : context) : Prop :=
  exists p k w d y l, effects_in q e (EAct p k w d y l).

Definition has_context_commit (e : trace) (q : context) : Prop :=
  exists p w d alpha l, effects_in q e (ECommit p w d alpha l).

Definition has_proposal_binding (dlt : dynamic_env) (q : context) : Prop :=
  exists p w d, dlt q p = Some (TyProposal w d).

Inductive stage_of (dlt : dynamic_env) (e : trace) (q : context) : stage -> Prop :=
| StageExecute : has_context_act e q -> stage_of dlt e q ExecuteStage
| StageCommit : ~ has_context_act e q -> has_context_commit e q ->
    stage_of dlt e q Commit
| StagePropose : ~ has_context_act e q -> ~ has_context_commit e q ->
    has_proposal_binding dlt q -> stage_of dlt e q Propose
| StageObserve : ~ has_context_act e q -> ~ has_context_commit e q ->
    ~ has_proposal_binding dlt q -> stage_of dlt e q Observe.

Lemma label_app q f1 f2 : label q (f1 ++ f2) = label q f1 ++ label q f2.
Proof.
  induction f1 as [|x xs IH]; simpl; [reflexivity | now rewrite IH].
Qed.

Lemma available_monotone g e1 e2 y l :
  available g e1 y l -> available g (e1 ++ e2) y l.
Proof.
  intros H; inversion H; subst.
  - apply AvInitial; assumption.
  - eapply AvRead. apply in_or_app; left; eassumption.
  - eapply AvCompute. apply in_or_app; left; eassumption.
  - eapply AvExpose. apply in_or_app; left; eassumption.
Qed.

Lemma source_reflexive e y : source e y y.
Proof. constructor. Qed.
