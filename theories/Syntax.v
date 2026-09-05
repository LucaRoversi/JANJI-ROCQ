(** * Hard-KLAIM syntax and authoritative interfaces

    The static environment classifies localities, immutable values, delegates,
    and tools.  Runtime progress is deliberately absent from delegate types:
    it is derived from the dynamic environment and accumulated trace. *)

(** ** Correspondence with [GianluigiFerrari_tribute_2026.pdf]

    The main paper correspondences are as follows (physical PDF pages are
    used).

    - [action_kind] and [capability] map to the delegate declaration and
      protocol of Definitions 4--5 (PDF p. 13), to [req] in Section 5.3
      (PDF p. 17), and to capability non-amplification, Definition 23
      (PDF p. 25).
    - [ty] and [data_type] map to Value types, Definition 13 (PDF p. 17),
      including the data-only restriction on tool results introduced with
      Definition 6 (PDF p. 14).
    - [effect], [event], [trace], [fragment], and [label] map to Primitive
      effects and Effect trace, Definitions 10--11 (PDF p. 16).
    - [tool_descriptor], [workflow_descriptor], and [static_env] implement the
      Level-1 declarations of Definitions 1--7 (PDF pp. 12--15).
    - [dynamic_env], value typing, and result shapes implement Definition 8
      and the exact result-binding convention (PDF pp. 15 and 20; Appendix B,
      PDF p. 34).
    - [atomic_action] and [program] map to Model-mediated actions,
      Definition 9 (PDF pp. 15--16); [has_act], [no_commit],
      [required_capabilities], [proposal_ids], [target_count], and [binds]
      make executable the side conditions summarized by Definition 17 and
      T-Call (PDF p. 20).

    Representation choices such as natural-number tags, records, boolean
    lookups, and recursive list scans are technical mechanization details.  The
    paper retains their mathematical interfaces, not their Rocq encodings. *)

From Coq Require Import Lists.List Bool.Bool.
From Janji Require Import Prelude.
Import ListNotations.

Inductive action_kind := Submit | Execute | Update | Allocate.

Inductive capability :=
| CapRead | CapDerive | CapPropose | CapCommit | CapExpose
| CapAct (k : action_kind).

Inductive ty :=
| TyBase (tag : nat)
| TyUnit
| TyProduct (left right : ty)
| TySet (element : ty)
| TyPatch (w : workflow)
| TyProposal (w : workflow) (d : patch)
| TyApproval (a : delegate) (q : context) (p : proposal)
             (w : workflow) (d : patch).

Fixpoint data_type (t : ty) : Prop :=
  match t with
  | TyProposal _ _ | TyApproval _ _ _ _ _ => False
  | TyProduct x y => data_type x /\ data_type y
  | TySet x => data_type x
  | _ => True
  end.

Inductive effect :=
| ERead (y : value) (l : locality)
| ECompute (sources : list value) (y : value) (l : locality)
| ECommit (p : proposal) (w : workflow) (d : patch)
          (alpha : approval) (l : locality)
| EAct (p : proposal) (k : action_kind) (w : workflow) (d : patch)
       (payload : value) (l : locality)
| EExpose (y : value) (from to : locality).

Definition event := (context * effect)%type.
Definition trace := list event.
Definition fragment := list effect.

Fixpoint label (q : context) (f : fragment) : trace :=
  match f with
  | [] => []
  | e :: rest => (q, e) :: label q rest
  end.

Inductive stage := Observe | Propose | Commit | ExecuteStage.

Record tool_descriptor := {
  tool_locality : locality;
  input_type : ty;
  output_type : ty;
  effect_schema : list value -> list value -> metadata -> list fragment;
  schema_output_data : data_type output_type
}.

Record workflow_descriptor := {
  workflow_input : ty;
  workflow_output : ty;
  workflow_policy_tag : nat;
  workflow_state_tag : nat;
  workflow_evolution_tag : nat
}.

(** The fields below make the declarations and trusted predicates that were
    prose-level in the paper explicit.  They are finite/decidable functions in
    an implementation; the metatheory uses only their specifications. *)
Record static_env := {
  locality_decl : locality -> bool;
  locality_metadata : locality -> option nat;
  static_type : value -> option ty;
  workflow_decl : workflow -> option workflow_descriptor;
  delegate_caps : delegate -> option (list capability);
  tool_decl : tool -> option tool_descriptor;
  schema_attested : tool -> bool;
  initial_placement : value -> locality -> bool;
  evidence_ok : approval -> delegate -> context -> proposal ->
                workflow -> patch -> bool;
  visible_values : context -> locality -> list value
}.

Definition dynamic_env := context -> value -> option ty.

Inductive value_has_type (g : static_env) (dlt : dynamic_env)
                         (q : context) : value -> ty -> Prop :=
| VTStatic : forall v t, static_type g v = Some t ->
    value_has_type g dlt q v t
| VTDynamic : forall v t, dlt q v = Some t ->
    value_has_type g dlt q v t
| VTApproval : forall alpha a p w d,
    evidence_ok g alpha a q p w d = true ->
    value_has_type g dlt q alpha (TyApproval a q p w d).

Inductive values_have_type (g : static_env) (dlt : dynamic_env)
                           (q : context) : list value -> ty -> Prop :=
| VHTUnit : values_have_type g dlt q [] TyUnit
| VHTSingle : forall v t,
    value_has_type g dlt q v t -> values_have_type g dlt q [v] t
| VHTProduct : forall xs ys tx ty,
    values_have_type g dlt q xs tx ->
    values_have_type g dlt q ys ty ->
    values_have_type g dlt q (xs ++ ys) (TyProduct tx ty)
| VHTSet : forall xs t,
    Forall (fun x => value_has_type g dlt q x t) xs ->
    values_have_type g dlt q xs (TySet t).

Inductive names_have_shape : list value -> ty -> Prop :=
| NHSUnit : names_have_shape [] TyUnit
| NHSSingle : forall v t,
    (match t with TyProduct _ _ | TyUnit => False | _ => True end) ->
    names_have_shape [v] t
| NHSProduct : forall xs ys tx ty,
    names_have_shape xs tx -> names_have_shape ys ty ->
    names_have_shape (xs ++ ys) (TyProduct tx ty).

Definition has_capability (g : static_env) (a : delegate)
                          (c : capability) : Prop :=
  exists caps, delegate_caps g a = Some caps /\ In c caps.

Inductive atomic_action :=
| AObserve (y : value) (source : locality)
| ADerive (y : value) (result_type : ty) (sources : list value)
| APropose (p : proposal) (w : workflow) (d : patch)
| ACommit (p : proposal) (w : workflow) (d : patch) (alpha : approval)
| ACall (results : list value) (t : tool) (inputs : list value)
        (eta : metadata) (reported : fragment).

Definition program := list atomic_action.

Fixpoint has_act (f : fragment) : Prop :=
  match f with
  | [] => False
  | EAct _ _ _ _ _ _ :: _ => True
  | _ :: rest => has_act rest
  end.

Fixpoint no_commit (f : fragment) : Prop :=
  match f with
  | [] => True
  | ECommit _ _ _ _ _ :: _ => False
  | _ :: rest => no_commit rest
  end.

(** [required_capabilities] is the paper's [req(F)].  It collects only the
    primitive authority exercised inside a fragment: reads, exposures, and
    production-action kinds.  Model derivation, proposal, and commitment are
    authorised by their dedicated typing rules; a tool fragment cannot contain
    a commitment. *)
Fixpoint required_capabilities (f : fragment) : list capability :=
  match f with
  | [] => []
  | ERead _ _ :: rest => CapRead :: required_capabilities rest
  | ECompute _ _ _ :: rest => required_capabilities rest
  | ECommit _ _ _ _ _ :: rest => required_capabilities rest
  | EAct _ k _ _ _ _ :: rest => CapAct k :: required_capabilities rest
  | EExpose _ _ _ :: rest => CapExpose :: required_capabilities rest
  end.

(** [pids(F)] is used by the call-fragment guard, Definition 17 of the final
    paper (PDF p. 20).  Only production effects carry a proposal identifier;
    commitments are forbidden from tool fragments separately. *)
Fixpoint proposal_ids (f : fragment) : list proposal :=
  match f with
  | [] => []
  | EAct p _ _ _ _ _ :: rest => p :: proposal_ids rest
  | _ :: rest => proposal_ids rest
  end.

Fixpoint target_count (y : value) (f : fragment) : nat :=
  match f with
  | [] => 0
  | ECompute _ z _ :: rest =>
      (if Nat.eqb y z then 1 else 0) + target_count y rest
  | _ :: rest => target_count y rest
  end.

Definition binds (f : fragment) (results : list value) : Prop :=
  forall y, In y results -> target_count y f = 1.
