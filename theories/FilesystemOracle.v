(** * Appendix A: filesystem-and-scheduler policy oracle

    This module gives the complete, deliberately narrow executable oracle
    interface described in Appendix A.  Principals and local identities are
    deployment metadata, not new core name classes.  Undefined resolution
    denies a query.  Every component is a terminating boolean or finite partial
    map, so the composite oracle is decidable by computation. *)

(** ** Correspondence with [GianluigiFerrari_tribute_2026.pdf]

    This module maps to Appendix A, Filesystem-and-Scheduler Policy Oracle
    (PDF pp. 31--32).  The fields of [filesystem_policy] implement principal
    and locality-specific identity resolution, path resolution, permission and
    quota checks, evidence verification, metadata-bound call authorization,
    concrete action resolution, and cross-locality flow authorization.

    The branches of [filesystem_oracle] map respectively to O-Read,
    O-Propose, O-Commit, O-Call, O-Act, and O-Flow.  The unresolved-principal
    denial lemmas and boolean case analysis are technical proofs making the
    appendix's totality, decidability, oracle equations, and deny-by-default
    policy executable. *)

From Coq Require Import Lists.List Bool.Bool.
From Janji Require Import Prelude Syntax Trace Policy.

Definition principal := nat.
Definition local_identity := nat.
Definition path := nat.

Record filesystem_policy := {
  principal_of : delegate -> option principal;
  identity_at : principal -> locality -> option local_identity;
  path_at : value -> locality -> option path;

  may_read : local_identity -> path -> bool;
  may_write : local_identity -> path -> bool;

  evolve_allowed : principal -> workflow -> patch -> locality -> bool;
  approval_valid : principal -> context -> proposal -> workflow ->
                   patch -> approval -> locality -> bool;
  approval_unused : approval -> trace -> bool;

  metadata_allowed : local_identity -> tool -> metadata -> bool;
  action_allowed : local_identity -> action_kind -> workflow -> patch ->
                   value -> locality -> bool
}.

Definition with_identity (pi : filesystem_policy) (a : delegate)
                         (l : locality)
                         (check : local_identity -> bool) : bool :=
  match principal_of pi a with
  | None => false
  | Some u =>
      match identity_at pi u l with
      | None => false
      | Some uid => check uid
      end
  end.

Definition readable_at (pi : filesystem_policy) (a : delegate)
                       (y : value) (l : locality) : bool :=
  with_identity pi a l (fun uid =>
    match path_at pi y l with
    | Some p => may_read pi uid p
    | None => false
    end).

Definition writable_at (pi : filesystem_policy) (a : delegate)
                       (y : value) (l : locality) : bool :=
  with_identity pi a l (fun uid =>
    match path_at pi y l with
    | Some p => may_write pi uid p
    | None => false
    end).

Definition filesystem_oracle (pi : filesystem_policy) : oracle :=
  fun g prefix question =>
    match question with
    | QObserve a y l => readable_at pi a y l
    | QPropose a w d l =>
        match principal_of pi a with
        | Some u => evolve_allowed pi u w d l
        | None => false
        end
    | QCommit a q p w d alpha l =>
        match principal_of pi a with
        | Some u =>
            (approval_valid pi u q p w d alpha l &&
             approval_unused pi alpha prefix)%bool
        | None => false
        end
    | QCall a t _ tool_loc eta =>
        (schema_attested g t &&
         with_identity pi a tool_loc
           (fun uid => metadata_allowed pi uid t eta))%bool
    | QAct a k w d payload l =>
        with_identity pi a l
          (fun uid => action_allowed pi uid k w d payload l)
    | QFlow a y l1 l2 =>
        (readable_at pi a y l1 && writable_at pi a y l2)%bool
    end.

Lemma filesystem_oracle_decides pi g prefix question :
  filesystem_oracle pi g prefix question = true \/
  filesystem_oracle pi g prefix question = false.
Proof.
  destruct (filesystem_oracle pi g prefix question); auto.
Qed.

Lemma observe_denied_when_principal_unresolved pi g prefix a y l :
  principal_of pi a = None ->
  filesystem_oracle pi g prefix (QObserve a y l) = false.
Proof.
  intro H; simpl; unfold readable_at, with_identity; rewrite H; reflexivity.
Qed.

Lemma flow_denied_when_principal_unresolved pi g prefix a y l1 l2 :
  principal_of pi a = None ->
  filesystem_oracle pi g prefix (QFlow a y l1 l2) = false.
Proof.
  intro H; simpl; unfold readable_at, writable_at, with_identity;
    rewrite H; reflexivity.
Qed.
