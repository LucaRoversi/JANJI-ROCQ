(** * Prelude

    Hard-KLAIM is deliberately parameterised by deployment names.  The paper
    treats each syntactic name class as abstract and requires only decidable
    equality and finiteness.  Natural numbers give a small executable
    realisation without adding a dependency beyond Coq 8.17.1's standard
    library. *)

(** ** Correspondence with [GianluigiFerrari_tribute_2026.pdf]

    Page references below are physical PDF pages in the 39-page final file.
    The aliases [locality], [delegate], [tool], [value], [workflow], and
    [context] correspond to the core name classes listed in Section 5.2
    (PDF p. 12, around line 334) and to their notation summary in Appendix C,
    Table C.2 (PDF p. 38).  The role-specific aliases [proposal], [patch],
    [approval], and [metadata] correspond to the same table and to the prose
    introducing effects in Sections 3 and 5.3 (PDF pp. 7 and 15--16).

    [subset], [disjoint], and the list lemmas below have no separately named
    paper counterpart.  They are proof-assistant implementations of ordinary
    finite-set and sequence reasoning used implicitly throughout the displayed
    rules. *)

From Coq Require Import Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.

Set Implicit Arguments.

Definition name := nat.
Definition locality := name.
Definition delegate := name.
Definition tool := name.
Definition value := name.
Definition workflow := name.
Definition context := name.
Definition proposal := name.
Definition patch := name.
Definition approval := name.
Definition metadata := name.

Definition subset {A : Type} (xs ys : list A) : Prop :=
  forall x, In x xs -> In x ys.

Definition disjoint {A : Type} (xs ys : list A) : Prop :=
  forall x, In x xs -> ~ In x ys.

Lemma in_singleton_eq {A : Type} (x y : A) : In x [y] -> x = y.
Proof. simpl; intuition. Qed.

Lemma in_app_singleton {A : Type} (x y : A) (xs : list A) :
  In x (xs ++ [y]) <-> In x xs \/ x = y.
Proof. rewrite in_app_iff; simpl; intuition. Qed.

Lemma app_cons_assoc {A : Type} (xs ys : list A) (x : A) :
  xs ++ x :: ys = (xs ++ [x]) ++ ys.
Proof. induction xs; simpl; congruence. Qed.
