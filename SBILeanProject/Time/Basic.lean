import SBILeanProject.SBI.Deformation

set_option autoImplicit false

namespace SBI.Time

/-
Operational accessibility of elementary rearrangements.

The SBI development already supplies

    D.AdmissibleStep O X Y

meaning that Y is obtainable from X by one admissible relational
rearrangement at observer O's operational resolution.

The Time manuscript requires a further distinction.  An admissible
rearrangement may exist formally without being operationally available
from the relational organization of the current configuration.

AccessibleStep O X Y means that the admissible rearrangement from
X to Y is operationally accessible from X.

This introduces no temporal parameter and no irreversible temporal
ordering.  It specifies only which admissible rearrangements are
operationally available from a given configuration.

In particular, no asymmetry is assumed here.  The later persistent-record
argument will establish conditions under which a forward accessible path
exists while no reverse accessible path exists.
-/
structure OperationalAccessibilitySemantics
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K) where

  /-
  One operationally accessible elementary rearrangement.

  Manuscript interpretation:

      X -> Y

  when this represented admissible locally mediated rearrangement is
  operationally available from the relational organization of X.
  -/
  AccessibleStep :
    (O : Observer M) →
    Configuration K O →
    Configuration K O →
    Prop

  /-
  Operational accessibility does not create a new class of physical
  rearrangements.

  Every operationally accessible step must already be an admissible
  relational rearrangement in the SBI sense.
  -/
  accessibleStep_admissible :
    ∀ {O : Observer M}
      {X Y : Configuration K O},
      AccessibleStep O X Y →
      D.AdmissibleStep O X Y

/-
Finite operational reachability.

The Time manuscript uses operational reachability between admissible
configurations.  The preceding structure supplied only one-step
operational accessibility:

    A.AccessibleStep O X Y.

We now take its finite reflexive-transitive closure.

OperationalReachability D A O X Y means that Y can be reached from X
through a finite sequence of operationally accessible admissible
rearrangements.

Manuscript notation:

    X ≼ Y

or, equivalently in prose,

    Y is operationally reachable from X.

There are two constructors:

  • refl:
      every configuration is operationally reachable from itself
      by a path containing zero rearrangements;

  • step:
      if X can make one operationally accessible step to Y, and
      Z is operationally reachable from Y, then Z is operationally
      reachable from X.

This relation still contains no temporal parameter and no temporal
ordering.  It is purely a statement about operational accessibility
within the relational configuration structure.

Its asymmetry, when such asymmetry occurs, will later provide the
basis for irreversible precedence.
-/
inductive OperationalReachability
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M) :
    Configuration K O →
    Configuration K O →
    Prop

  | refl
      (X : Configuration K O) :
      OperationalReachability D A O X X

  | step
      {X Y Z : Configuration K O}
      (hStep :
        A.AccessibleStep O X Y)
      (hRest :
        OperationalReachability D A O Y Z) :
      OperationalReachability D A O X Z


/-
Operational reachability is reflexive.

This follows directly from the zero-step path.
-/
theorem operationalReachability_refl
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    (X : Configuration K O) :

    OperationalReachability D A O X X := by

  exact OperationalReachability.refl X


/-
Operational reachability is transitive.

If Y is operationally reachable from X and Z is operationally
reachable from Y, concatenating the two finite accessible paths
makes Z operationally reachable from X.

This theorem will later be one of the two defining properties
needed to regard operational reachability as a preorder.
-/
theorem operationalReachability_trans
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    {X Y Z : Configuration K O}
    (hXY :
      OperationalReachability D A O X Y)
    (hYZ :
      OperationalReachability D A O Y Z) :

    OperationalReachability D A O X Z := by

  induction hXY with

  | refl X =>
      exact hYZ

  | step hStep hRest ih =>
      exact
        OperationalReachability.step
          hStep
          (ih hYZ)


/-
Every operationally reachable configuration is also admissibly
reachable in the SBI sense.

Operational accessibility therefore refines the admissible
configuration-change structure already established by SBI; it does
not introduce a second independent notion of physical rearrangement.

In manuscript terms:

    X ≼ Y

implies that there exists a finite admissible deformation

    X ↝ Y.

The converse is not asserted.  An admissible deformation may exist
without being operationally accessible from the configuration in
question.
-/
theorem operationalReachability_is_admissibleDeformation
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    {X Y : Configuration K O}
    (hReach :
      OperationalReachability D A O X Y) :

    AdmissibleDeformation D O X Y := by

  induction hReach with

  | refl X =>
      exact
        AdmissibleDeformation.refl X

  | step hStep hRest ih =>
      exact
        AdmissibleDeformation.step
          (A.accessibleStep_admissible hStep)
          ih
end SBI.Time
