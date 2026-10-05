import SBILeanProject.Time.Reachability

set_option autoImplicit false

namespace SBI.Time

/-
Operational reconstruction of a preceding configuration.

Suppose an admissible interaction carries configuration X to a later
configuration Y.  To reconstruct X operationally from Y means that X is
operationally reachable from Y through admissible locally mediated
rearrangements.

This definition introduces no temporal direction.  It merely gives a
manuscript-facing name to reverse operational reachability:

    X is reconstructible from Y
        iff
    Y ⪯ X.

Persistent-record formation will later establish conditions under which
this reverse reachability fails even though the forward reachability
X ⪯ Y remains available.
-/
def OperationallyReconstructible
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    (X Y : Configuration K O) : Prop :=

  OperationalReachability D A O Y X

/-
Operational irreversibility of an admissible configuration change.

An interaction carrying X to Y is operationally irreversible when

  • Y is operationally reachable from X, while
  • X is not operationally reconstructible from Y.

Thus operational irreversibility is an asymmetry of operational
accessibility.  It does not assert that a formally admissible microscopic
reverse rearrangement is forbidden.

This is the manuscript-facing formulation of the asymmetric reachability
relation introduced earlier for the order-theoretic development.
-/
def OperationallyIrreversible
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    (X Y : Configuration K O) : Prop :=

  OperationalReachability D A O X Y ∧
  ¬ OperationallyReconstructible D A O X Y

/-
Operational irreversibility is exactly asymmetric operational reachability.

The earlier order-theoretic development used `AsymmetricReachability`.
The present manuscript-facing definition unpacks the same condition in
terms of failed operational reconstruction.

This theorem makes the correspondence explicit so that subsequent record
arguments can feed directly into the already established precedence theory.
-/
theorem operationallyIrreversible_iff_asymmetricReachability
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    (X Y : Configuration K O) :

    OperationallyIrreversible D A O X Y ↔
      AsymmetricReachability D A O X Y := by

  rfl

/-
Semantic interface for operational relational features of configurations.

The SBI network development already provides the type `C.Distinction`
for observer-resolvable relational distinctions.  What it does not yet
specify is how such a distinction is represented in a particular global
configuration.

The Time manuscript needs two configuration-level notions:

  • `PresentIn O Y R`:
      distinction R is realized in configuration Y;

  • `Distinguishes O X Y R`:
      R is a relational feature by which Y is operationally
      distinguished from X.

These predicates introduce representational semantics only.  They do not
assert that any particular distinction exists, persists, or produces
irreversibility.
-/
structure RecordFeatureSemantics
    {M : SBI}
    {C : NetworkRealizationContext M}
    (K : OperationalContext C) where

  PresentIn :
    (O : Observer M) →
    Configuration K O →
    C.Distinction →
    Prop

  Distinguishes :
    (O : Observer M) →
    Configuration K O →
    Configuration K O →
    C.Distinction →
    Prop
    /-
  Elimination of a record candidate together with its dependencies.

  `EliminatedWithDependencies O X Y R Z` means that, in configuration Z,
  the relational feature R and the interaction-induced relational
  dependencies by which R distinguishes the post-interaction
  configuration Y from the pre-interaction configuration X have been
  eliminated.

  This predicate only names that configuration-level condition.  It does
  not assert that Z is operationally reachable from Y, nor that X can be
  reconstructed from Z.  Those dynamical/reachability requirements are
  stated separately below.
  -/
  EliminatedWithDependencies :
    (O : Observer M) →
    Configuration K O →
    Configuration K O →
    C.Distinction →
    Configuration K O →
    Prop

/-
Persistent record produced by an interaction X → Y.

The fields follow the manuscript definition explicitly.

`forward_reachable` records that the post-interaction configuration Y is
operationally accessible from X.

`present_in_post` and `distinguishes_post_from_pre` state that R is an
operationally distinguishable relational feature of the post-interaction
organization.

`elimination_requires_reconstruction` formalizes the statement that
eliminating R together with the relational dependencies by which it
distinguishes Y from X requires recovery of the pre-interaction
organization.  Any configuration Z in which that elimination has been
completed must therefore admit operational reconstruction of X.

Finally, `reconstruction_inaccessible` states that such reconstruction
cannot be initiated operationally from Y.

The last two clauses together imply that no configuration in which the
record and all of its distinguishing dependencies have been eliminated is
operationally reachable from Y.
-/
structure PersistentRecord
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (F : RecordFeatureSemantics K)
    (O : Observer M)
    (X Y : Configuration K O)
    (R : C.Distinction) : Prop where

  forward_reachable :
    OperationalReachability D A O X Y

  present_in_post :
    F.PresentIn O Y R

  distinguishes_post_from_pre :
    F.Distinguishes O X Y R

  elimination_requires_reconstruction :
    ∀ Z : Configuration K O,
      F.EliminatedWithDependencies O X Y R Z →
      OperationalReachability D A O Z X

  reconstruction_inaccessible :
    ¬ OperationallyReconstructible D A O X Y

/-
A persistent record implies operational irreversibility.

If R is a persistent record produced in the transition from X to Y, then

  • Y is operationally reachable from X; and
  • X is not operationally reconstructible from Y.

These are exactly the two clauses of operational irreversibility.

The richer record structure above is important physically: it states what
kind of post-interaction relational feature supports the failure of
reconstruction.  Once that failure is available, however, this theorem is
an immediate logical consequence.
-/
theorem PersistentRecord.operationallyIrreversible
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (F : RecordFeatureSemantics K)
    (O : Observer M)
    (X Y : Configuration K O)
    (R : C.Distinction)
    (hRecord : PersistentRecord D A F O X Y R) :

    OperationallyIrreversible D A O X Y := by

  constructor

  · exact hRecord.forward_reachable

  · exact hRecord.reconstruction_inaccessible

/-
A persistent record cannot be operationally erased together with all of
its distinguishing dependencies.

Suppose Z were operationally reachable from the post-interaction
configuration Y and that, in Z, the record feature R together with all
dependencies by which it distinguishes Y from X had been eliminated.

By the defining property of a persistent record, such elimination would
make the pre-interaction configuration X operationally reconstructible
from Z.

Transitivity of operational reachability would then make X reachable
from Y, contradicting the record's reconstruction-inaccessibility clause.

Thus persistent record formation blocks operational erasure of the full
record-producing relational organization.
-/
theorem PersistentRecord.elimination_not_reachable
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (F : RecordFeatureSemantics K)
    (O : Observer M)
    (X Y : Configuration K O)
    (R : C.Distinction)
    (hRecord : PersistentRecord D A F O X Y R)
    {Z : Configuration K O}
    (hEliminated :
      F.EliminatedWithDependencies O X Y R Z) :

    ¬ OperationalReachability D A O Y Z := by

  intro hYZ

  have hZX :
      OperationalReachability D A O Z X :=
    hRecord.elimination_requires_reconstruction Z hEliminated

  have hYX :
      OperationalReachability D A O Y X :=
    operationalReachability_trans D A O hYZ hZX

  exact hRecord.reconstruction_inaccessible hYX

/-
Persistent record formation produces asymmetric operational reachability.

The earlier order-theoretic development defines irreversible precedence
from `AsymmetricReachability`.  The present theorem connects that abstract
relation directly to persistent-record formation.

Thus a transition carrying a persistent record supplies exactly the
reachability asymmetry required by the later temporal-order construction.
-/
theorem PersistentRecord.asymmetricReachability
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (F : RecordFeatureSemantics K)
    (O : Observer M)
    (X Y : Configuration K O)
    (R : C.Distinction)
    (hRecord : PersistentRecord D A F O X Y R) :

    AsymmetricReachability D A O X Y := by

  exact
    (operationallyIrreversible_iff_asymmetricReachability
      D A O X Y).mp
      (hRecord.operationallyIrreversible D A F O X Y R)

/-
Persistent record formation induces irreversible precedence.

A persistent record produced in the transition X → Y gives asymmetric
operational reachability from X to Y.  The quotient construction identifies
configurations that are mutually operationally reachable, so this asymmetry
descends to a strict precedence relation between their reversible classes:

    [X]R ≺ [Y]R.

This is the direct formal bridge from persistent record formation to the
irreversible precedence relation used in the temporal-order construction.
-/
theorem PersistentRecord.irreversiblePrecedence
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (F : RecordFeatureSemantics K)
    (O : Observer M)
    (X Y : Configuration K O)
    (R : C.Distinction)
    (hRecord : PersistentRecord D A F O X Y R) :

    IrreversiblePrecedence D A O
      (reversibleClassOf D A O X)
      (reversibleClassOf D A O Y) := by

  exact
    (irreversiblePrecedence_classOf_iff D A O X Y).2
      (hRecord.asymmetricReachability D A F O X Y R)
      
end SBI.Time
