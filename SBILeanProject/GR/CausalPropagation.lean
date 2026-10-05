import SBILeanProject.Time.Duration

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Causal propagation and reversible duration.

This file formalizes the bridge used in the GR manuscript between

  * relational propagation depth, and
  * the operational reversible duration constructed in the Time paper.

The Time formalization already proves that a represented reversible path
with positive resolved path length accumulates strictly positive duration
under a positive local calibration scale.

The genuinely new GR input is narrower: when a causal propagation process
crosses relational depth n, its represented duration-bearing traversal must
contain at least n resolved local advances.

We encode that bridge explicitly in `CausalPropagationProcess` by requiring

    relationalDepth <= path.pathLength.

This file therefore does NOT claim that A2 alone produces a positive
physical duration.  Positivity comes from the Time construction once the
causal process has been represented by a nontrivial reversible traversal.

No spacetime metric, spatial length, invariant speed, Lorentz
transformation, or coordinate system is introduced here.  The output is a
bound in relational depth per operational duration.  Conversion to an
effective spatial speed is a later coarse-grained step.
-/

/-
A duration-bearing representation of one causal propagation process.

`D` is the underlying configuration-change semantics and `A` is the
operational-accessibility semantics defined in the Time development.
They are explicit parameters of the process type because the endpoint
configurations alone do not determine them.  This also makes the formal
dependency on the chosen operational dynamics visible rather than asking
Lean to reconstruct it from a projection later.

`path` is the represented reversible traversal imported from the Time
formalization.

`relationalDepth` is the number of resolved relational stages crossed by
the causal process in the GR interpretation.

`depth_le_pathLength` is the explicit physical bridge:
traversing relational depth n requires at least n represented local
advances in the duration-bearing path.

The structure deliberately does not attempt to derive this identification
from A2.  It records the condition under which the Time duration theorem is
applicable to causal propagation.
-/
structure CausalPropagationProcess
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : Time.OperationalAccessibilitySemantics D)
    (O : Observer M)
    (X Y : Configuration K O) where

  path :
    Time.ReversibleRearrangementPath A O X Y

  relationalDepth :
    Nat

  depth_le_pathLength :
    relationalDepth <= path.pathLength

/-
A causal process of positive relational depth is represented by a
nontrivial reversible traversal.

If

    0 < n

and

    n <= L(gamma),

then

    0 < L(gamma).

This is the purely arithmetic part of the causal-duration bridge.
-/
theorem CausalPropagationProcess.pathLength_pos_of_depth_pos
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : Time.OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (p : CausalPropagationProcess D A O X Y)
    (hDepth : 0 < p.relationalDepth) :

    0 < p.path.pathLength := by

  exact lt_of_lt_of_le hDepth p.depth_le_pathLength

/-
Positive relational propagation depth implies positive accumulated
operational duration.

The logical chain is now explicit:

    positive relational depth
        ->
    positive represented path length
        ->
    positive accumulated reversible duration.

The second implication is imported directly from the Time formalization.
This theorem is therefore the formal counterpart of the corrected GR
manuscript statement that nonzero causal propagation is non-instantaneous
only after the causal mediation chain is represented as a nontrivial
physical-duration-bearing traversal.
-/
theorem CausalPropagationProcess.accumulatedDuration_pos_of_depth_pos
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : Time.OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (p : CausalPropagationProcess D A O X Y)
    (delta : Time.LocalDurationScale)
    (hDepth : 0 < p.relationalDepth) :

    0 < p.path.accumulatedDuration delta := by

  exact
    p.path.accumulatedDuration_pos_of_pathLength_pos
      delta
      (p.pathLength_pos_of_depth_pos hDepth)

/-
Lower bound on duration from relational propagation depth.

The Time construction defines

    Delta tau(gamma) = L(gamma) * delta tau_loc.

Since a causal propagation process of depth n is represented by a path with

    n <= L(gamma),

and the local duration scale is positive, multiplication preserves the
ordering:

    n * delta tau_loc <= Delta tau(gamma).

This is the quantitative core of the finite causal-rate argument.  It is
stated before introducing any effective spatial increment.
-/
theorem CausalPropagationProcess.depth_times_stepDuration_le_duration
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : Time.OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (p : CausalPropagationProcess D A O X Y)
    (delta : Time.LocalDurationScale) :

    (p.relationalDepth : Real) * delta.stepDuration
      <=
    p.path.accumulatedDuration delta := by

  rw [Time.ReversibleRearrangementPath.accumulatedDuration]

  simp only [nsmul_eq_mul]

  exact
    mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr p.depth_le_pathLength)
      (le_of_lt delta.stepDuration_positive)

/-
Finite relational-depth propagation bound.

Rather than divide by duration, we retain the mathematically stronger and
numerically safer inequality

    n * delta tau_loc <= Delta tau.

Because `delta.stepDuration` is strictly positive, the same positive finite
calibration applies to every resolved local advance represented by this
causal process.  Thus arbitrary relational depth cannot be traversed at
fixed finite duration without violating the bound.

The manuscript subsequently converts one resolved relational stage to an
effective spatial increment ell_loc.  That conversion is not formalized
here because it belongs to the coarse-grained spatial representation, not
to the relational-duration theorem itself.
-/
def HasFiniteRelationalDepthRateBound
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : Time.OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (p : CausalPropagationProcess D A O X Y)
    (delta : Time.LocalDurationScale) : Prop :=

  (p.relationalDepth : Real) * delta.stepDuration
    <=
  p.path.accumulatedDuration delta

/-
Every causal propagation process satisfying the explicit depth-to-path
bridge obeys the finite relational-depth propagation bound supplied by the
positive local duration calibration.
-/
theorem CausalPropagationProcess.hasFiniteRelationalDepthRateBound
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : Time.OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (p : CausalPropagationProcess D A O X Y)
    (delta : Time.LocalDurationScale) :

    HasFiniteRelationalDepthRateBound p delta := by

  exact p.depth_times_stepDuration_le_duration delta

end GR
end SBI
