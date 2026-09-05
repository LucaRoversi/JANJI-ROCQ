(** * Prefix-sensitive policy admissibility

    A policy instance fixes a terminating oracle.  The model never answers an
    oracle query.  Each event is checked against its exact preceding prefix,
    which is the key definition needed by the trace-safety proof. *)

(** ** Correspondence with [GianluigiFerrari_tribute_2026.pdf]

    [query] and [oracle] implement the finite query family and terminating
    policy oracle preceding Prefix admissibility, Definition 15 (PDF p. 18).
    [event_obligation] is the Rocq inductive presentation of that definition's
    Read, Compute, Commit, Act, and Expose clauses (PDF pp. 18--19), while
    [admissible] is the closed, decomposition-based relation itself.

    [exact_commitment_safety] and [source_sensitive_flow_safety], together with
    the lemmas deriving them from admissibility, map to Definition 16 and to
    the two safety statements in Section 6.2 (PDF pp. 18 and 21, equations
    (8)--(9)).  Prefix-decomposition lemmas are technical support for the
    paper's statement that admissibility is prefix-closed by construction. *)

From Coq Require Import Lists.List.
From Janji Require Import Prelude Syntax Trace.
Import ListNotations.

Inductive query :=
| QObserve (a : delegate) (y : value) (l : locality)
| QPropose (a : delegate) (w : workflow) (d : patch) (l : locality)
| QCommit (a : delegate) (q : context) (p : proposal)
          (w : workflow) (d : patch) (alpha : approval) (l : locality)
| QCall (a : delegate) (t : tool) (delegate_loc tool_loc : locality)
        (eta : metadata)
| QAct (a : delegate) (k : action_kind) (w : workflow) (d : patch)
       (payload : value) (l : locality)
| QFlow (a : delegate) (y : value) (from to : locality).

Definition oracle := static_env -> trace -> query -> bool.

Inductive event_obligation (g : static_env) (o : oracle) (a : delegate)
                           (prefix : trace) (q : context) : effect -> Prop :=
| OblRead : forall y l,
    available g prefix y l ->
    o g prefix (QObserve a y l) = true ->
    event_obligation g o a prefix q (ERead y l)
| OblCompute : forall sources y l,
    fresh g prefix y ->
    (forall x, In x sources -> available g prefix x l) ->
    event_obligation g o a prefix q (ECompute sources y l)
| OblCommit : forall p w d alpha l,
    proposed prefix q p w d ->
    o g prefix (QCommit a q p w d alpha l) = true ->
    event_obligation g o a prefix q (ECommit p w d alpha l)
| OblAct : forall p k w d payload l,
    (exists alpha lc, In (q, ECommit p w d alpha lc) prefix) ->
    o g prefix (QAct a k w d payload l) = true ->
    event_obligation g o a prefix q (EAct p k w d payload l)
| OblExpose : forall y l1 l2,
    available g prefix y l1 ->
    (forall b, source prefix b y ->
       o g prefix (QFlow a b l1 l2) = true) ->
    event_obligation g o a prefix q (EExpose y l1 l2).

(** This closed, decomposition-based definition is Definition 15 of the final
    paper (PDF pp. 18--19).  Quantifying over every decomposition avoids a
    hidden cursor and makes prefix closure a theorem. *)
Definition admissible (g : static_env) (o : oracle) (a : delegate)
                      (e : trace) : Prop :=
  forall prefix q eff suffix,
    e = prefix ++ (q, eff) :: suffix ->
    event_obligation g o a prefix q eff.

Lemma admissible_nil g o a : admissible g o a [].
Proof.
  intros prefix q eff suffix H.
  destruct prefix; discriminate H.
Qed.

Lemma admissible_obligation g o a e prefix q eff suffix :
  admissible g o a e ->
  e = prefix ++ (q, eff) :: suffix ->
  event_obligation g o a prefix q eff.
Proof. intros Hadm Heq; eauto. Qed.

Lemma admissible_prefix g o a e1 e2 :
  admissible g o a (e1 ++ e2) -> admissible g o a e1.
Proof.
  intros H prefix q eff suffix Heq.
  apply (H prefix q eff (suffix ++ e2)).
  subst e1. rewrite <- app_assoc. reflexivity.
Qed.

Lemma exact_commitment_from_admissibility g o a e q p k w d y l :
  admissible g o a e ->
  In (q, EAct p k w d y l) e ->
  exists alpha lc,
    In (q, ECommit p w d alpha lc) e /\
    occurs_before (q, ECommit p w d alpha lc)
                  (q, EAct p k w d y l) e.
Proof.
  intros Hadm Hin.
  apply in_split in Hin as [prefix [suffix Heq]].
  pose proof (Hadm prefix q (EAct p k w d y l) suffix Heq) as Hobl.
  inversion Hobl as [| | | ? ? ? ? ? ? Hcommit Hallow |]; subst.
  destruct Hcommit as [alpha [lc Hprefix]].
  exists alpha, lc; split.
  - apply in_or_app. left. exact Hprefix.
  - exists prefix, suffix. split; [reflexivity | exact Hprefix].
Qed.

Lemma compute_sources_available_from_admissibility g o a e prefix suffix
      q sources y l :
  admissible g o a e ->
  e = prefix ++ (q, ECompute sources y l) :: suffix ->
  fresh g prefix y /\
  forall x, In x sources -> available g prefix x l.
Proof.
  intros Hadm Heq.
  pose proof (Hadm prefix q (ECompute sources y l) suffix Heq) as Hobl.
  inversion Hobl; subst; auto.
Qed.

Lemma flow_safety_from_admissibility g o a e prefix suffix q y l1 l2 :
  admissible g o a e ->
  e = prefix ++ (q, EExpose y l1 l2) :: suffix ->
  forall b, source prefix b y ->
    o g prefix (QFlow a b l1 l2) = true.
Proof.
  intros Hadm Heq.
  pose proof (Hadm prefix q (EExpose y l1 l2) suffix Heq) as Hobl.
  inversion Hobl; subst; auto.
Qed.

Definition exact_commitment_safety (e : trace) : Prop :=
  forall q p k w d y l,
    In (q, EAct p k w d y l) e ->
    exists alpha lc,
      In (q, ECommit p w d alpha lc) e /\
      occurs_before (q, ECommit p w d alpha lc)
                    (q, EAct p k w d y l) e.

Definition source_sensitive_flow_safety
           (g : static_env) (o : oracle) (a : delegate) (e : trace) : Prop :=
  forall prefix suffix q y l1 l2,
    e = prefix ++ (q, EExpose y l1 l2) :: suffix ->
    forall b, source prefix b y ->
      o g prefix (QFlow a b l1 l2) = true.

Theorem admissibility_implies_static_safety g o a e :
  admissible g o a e ->
  exact_commitment_safety e /\
  source_sensitive_flow_safety g o a e.
Proof.
  intros Hadm; split.
  - red; intros; eapply exact_commitment_from_admissibility; eauto.
  - red; intros; eapply flow_safety_from_admissibility; eauto.
Qed.
