(** * Executable micro-derivations of the motivating cases

    The paper's accepted trace has the shape observation/computation,
    proposal, exact commitment, and production action.  The following finite
    instance isolates the proof-critical suffix.  Two negative lemmas show
    that an action without a preceding exact commitment and an exposure denied
    for a reflexive source cannot be admitted. *)

(** ** Correspondence with [GianluigiFerrari_tribute_2026.pdf]

    [accepted_trace] and [accepted_trace_has_exact_commitment] map to the
    proof-critical proposal/commit/action suffix of OK-TRACE in Section 4
    (PDF p. 8) and its complete derivation in Appendix B.2 (PDF pp. 34--35).
    [uncommitted_trace_rejected] maps to the missing-commitment failure in
    NOT-OK-TRACE, Section 4 and Appendix B.3 (PDF pp. 9 and 36).
    [denied_source_flow_rejected] maps to the source-closure failure in
    NOT-OK-FLOW, Section 4 and Appendix B.4 (PDF pp. 10 and 36--37).

    These are deliberately small executable witnesses, not verbatim encodings
    of every displayed example step.  Their numeric names and permissive test
    oracle instantiate the corresponding symbolic participants and assumed
    oracle answers while omitting setup irrelevant to the isolated proof
    obligation. *)

From Coq Require Import Lists.List Arith.PeanoNat.
From Janji Require Import Prelude Syntax Trace Policy.
Import ListNotations.

Definition ex_q : context := 1.
Definition ex_a : delegate := 2.
Definition ex_l : locality := 3.
Definition ex_public : locality := 4.
Definition ex_w : workflow := 10.
Definition ex_d : patch := 11.
Definition ex_p : proposal := 12.
Definition ex_alpha : approval := 13.
Definition ex_payload : value := 14.

Definition ex_static_type (v : value) : option ty :=
  if Nat.eqb v ex_w then Some (TyBase 1)
  else if Nat.eqb v ex_d then Some (TyPatch ex_w)
  else None.

Definition ex_initial (v : value) (l : locality) : bool :=
  (Nat.eqb l ex_l && (Nat.eqb v ex_w || Nat.eqb v ex_d))%bool.

Definition ex_env : static_env :=
  {| locality_decl := fun _ => true;
     locality_metadata := fun _ => Some 0;
     static_type := ex_static_type;
     workflow_decl := fun _ => None;
     delegate_caps := fun _ => Some
       [CapRead; CapDerive; CapPropose; CapCommit; CapExpose; CapAct Execute];
     tool_decl := fun _ => None;
     schema_attested := fun _ => true;
     initial_placement := ex_initial;
     evidence_ok := fun _ _ _ _ _ _ => true;
     visible_values := fun _ _ => [ex_w; ex_d] |}.

Definition allow_all : oracle := fun _ _ _ => true.

Definition accepted_trace : trace :=
  [(ex_q, ECompute [ex_w; ex_d] ex_p ex_l);
   (ex_q, ECommit ex_p ex_w ex_d ex_alpha ex_l);
   (ex_q, EAct ex_p Execute ex_w ex_d ex_payload ex_l)].

Lemma accepted_trace_admissible :
  admissible ex_env allow_all ex_a accepted_trace.
Proof.
  unfold admissible; intros prefix q eff suffix Heq.
  destruct prefix as [|ev1 prefix].
  - simpl in Heq; inversion Heq; subst; clear Heq.
    apply OblCompute.
    + unfold fresh, ex_env, ex_static_type, ex_initial, produced,
        ex_p, ex_w, ex_d, ex_l; cbn.
      repeat split; try discriminate.
      * intros; now rewrite Bool.andb_false_r.
      * intros (? & ? & ? & H); inversion H.
    + intros x [Hx | [Hx | Hx]]; subst; try contradiction;
        apply AvInitial; reflexivity.
  - destruct prefix as [|ev2 prefix].
    + simpl in Heq; inversion Heq; subst; clear Heq.
      apply OblCommit.
      * exists ex_l; simpl; auto.
      * reflexivity.
    + destruct prefix as [|ev3 prefix].
      * simpl in Heq; inversion Heq; subst; clear Heq.
        apply OblAct.
        -- exists ex_alpha, ex_l; simpl; auto.
        -- reflexivity.
      * pose proof (f_equal (@length event) Heq).
        rewrite app_length in H; simpl in H.
        do 3 apply Nat.succ_inj in H.
        rewrite Nat.add_succ_r in H; discriminate.
Qed.

Example accepted_trace_has_exact_commitment :
  exact_commitment_safety accepted_trace.
Proof.
  apply (proj1 (@admissibility_implies_static_safety
    ex_env allow_all ex_a accepted_trace accepted_trace_admissible)).
Qed.

Definition uncommitted_trace : trace :=
  [(ex_q, EAct ex_p Execute ex_w ex_d ex_payload ex_l)].

Lemma uncommitted_trace_rejected :
  ~ admissible ex_env allow_all ex_a uncommitted_trace.
Proof.
  intro H.
  specialize (H [] ex_q (EAct ex_p Execute ex_w ex_d ex_payload ex_l) [] eq_refl).
  inversion H as [| | | ? ? ? ? ? ? Hexists |].
  destruct Hexists as [alpha [lc Hin]]. inversion Hin.
Qed.

Definition deny_flows : oracle :=
  fun _ _ query =>
    match query with QFlow _ _ _ _ => false | _ => true end.

Definition denied_exposure : trace :=
  [(ex_q, EExpose ex_w ex_l ex_public)].

Lemma denied_source_flow_rejected :
  ~ admissible ex_env deny_flows ex_a denied_exposure.
Proof.
  intro H.
  specialize (H [] ex_q (EExpose ex_w ex_l ex_public) [] eq_refl).
  inversion H as [| | | | ? ? ? Hav Hflows]; subst.
  specialize (Hflows ex_w (SourceRefl [] ex_w)).
  discriminate.
Qed.

Print Assumptions accepted_trace_has_exact_commitment.
Print Assumptions uncommitted_trace_rejected.
Print Assumptions denied_source_flow_rejected.
