import SBILeanProject.Time.Basic
import SBILeanProject.Time.Reachability

set_option autoImplicit false

namespace SBI.Time

/-
Represented operationally accessible rearrangement path.

The earlier relation `OperationalReachability` states only that one
configuration is reachable from another.  It is a proposition, so it does
not retain a physically represented path as data.

For reversible exploration we need the path itself, because the manuscript
defines

    L(γ)

from the number of elementary rearrangements in the represented sequence,
and distinct paths with the same endpoints may have different lengths.

We therefore define an accessible rearrangement path as an object in
`Type`, rather than as a proposition.

The constructors represent

    X

for a zero-step path, and

    X → Y → ... → Z

for a path whose first accessible elementary rearrangement is X → Y,
followed by a represented path from Y to Z.
-/
inductive AccessibleRearrangementPath
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M) :
    Configuration K O →
    Configuration K O →
    Type

  | refl
      (X : Configuration K O) :
      AccessibleRearrangementPath A O X X

  | step
      {X Y Z : Configuration K O}
      (hStep : A.AccessibleStep O X Y)
      (hRest : AccessibleRearrangementPath A O Y Z) :
      AccessibleRearrangementPath A O X Z

/-
Number of elementary rearrangements in a represented accessible path.

Because `AccessibleRearrangementPath` retains the actual rearrangement
sequence as data, we can count its elementary steps.

The zero-step path has length 0.

Adding one accessible elementary rearrangement to the front of a path
increases the count by one.

This is the discrete quantity from which the manuscript's path length
L(γ) can later be defined.  We keep the neutral name `stepCount` here so
that no physical scale or duration has yet been introduced.
-/
def AccessibleRearrangementPath.stepCount
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (γ : AccessibleRearrangementPath A O X Y) :
    Nat :=

  match γ with

  | .refl _ =>
      0

  | .step _ hRest =>
      Nat.succ hRest.stepCount

/-
Every represented accessible rearrangement path determines operational
reachability between the same endpoints.

`AccessibleRearrangementPath` contains more information than
`OperationalReachability`: it retains the actual finite sequence of
accessible rearrangements, whereas `OperationalReachability` records only
the existence of such a finite sequence.

This theorem forgets the path data and recovers the previously defined
endpoint reachability statement.

No new physical assumption enters here.
-/
theorem accessibleRearrangementPath_is_operationalReachability
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (γ : AccessibleRearrangementPath A O X Y) :
    OperationalReachability D A O X Y := by

  induction γ with

  | refl X =>
      exact OperationalReachability.refl X

  | step hStep hRest ih =>
      exact OperationalReachability.step hStep ih

/-
Concatenation of represented accessible rearrangement paths.

If γ₁ is a represented path from X to Y and γ₂ is a represented path
from Y to Z, their concatenation is a represented path from X to Z.

This operation preserves the actual step sequence rather than merely
proving endpoint reachability.  It will therefore support an additive
path-length construction downstream.
-/
def AccessibleRearrangementPath.append
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y Z : Configuration K O}
    (γ₁ : AccessibleRearrangementPath A O X Y)
    (γ₂ : AccessibleRearrangementPath A O Y Z) :
    AccessibleRearrangementPath A O X Z :=

  match γ₁ with

  | .refl _ =>
      γ₂

  | .step hStep hRest =>
      .step hStep (hRest.append γ₂)

/-
Step count is additive under path concatenation.

If γ₁ runs from X to Y and γ₂ runs from Y to Z, then the number of
elementary rearrangements in the concatenated path is the sum of the
numbers in the two component paths:

    stepCount (γ₁ ++ γ₂)
      =
    stepCount γ₁ + stepCount γ₂.

This is the discrete precursor of the manuscript's additivity property
for path length L(γ).
-/
theorem AccessibleRearrangementPath.stepCount_append
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y Z : Configuration K O}
    (γ₁ : AccessibleRearrangementPath A O X Y)
    (γ₂ : AccessibleRearrangementPath A O Y Z) :
    (γ₁.append γ₂).stepCount =
      γ₁.stepCount + γ₂.stepCount := by

  induction γ₁ with

  | refl X =>
      simp [AccessibleRearrangementPath.append,
            AccessibleRearrangementPath.stepCount]

    | step hStep hRest ih =>
      simp only [AccessibleRearrangementPath.append,
                 AccessibleRearrangementPath.stepCount]

      rw [ih]

      exact
        Nat.add_right_comm
          hRest.stepCount
          γ₂.stepCount
          1

/-
Represented reversible rearrangement path.

An accessible path need not be reversible.  For the reversible-exploration
construction used in the Time manuscript, every represented elementary
rearrangement along the specified path must also be traversable in the
opposite direction.

We therefore store, for every elementary step X → Y,

  • accessibility from X to Y, and
  • accessibility from Y back to X.

This is stronger than merely requiring the endpoints of the whole path to
belong to the same reversible equivalence class.  The stronger structure is
needed because the manuscript considers reversal of the specified path
itself, not merely the existence of some return path.
-/
inductive ReversibleRearrangementPath
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M) :
    Configuration K O →
    Configuration K O →
    Type

  | refl
      (X : Configuration K O) :
      ReversibleRearrangementPath A O X X

  | step
      {X Y Z : Configuration K O}
      (hForward : A.AccessibleStep O X Y)
      (hBackward : A.AccessibleStep O Y X)
      (hRest : ReversibleRearrangementPath A O Y Z) :
      ReversibleRearrangementPath A O X Z

/-
Number of elementary rearrangements in a represented reversible path.

As for an accessible path, the intrinsic discrete length is the number of
elementary rearrangement steps in the represented sequence.

The additional backward-accessibility certificate carried by each step does
not alter the count.  It records reversibility of the same represented
rearrangement.
-/
def ReversibleRearrangementPath.stepCount
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (γ : ReversibleRearrangementPath A O X Y) :
    Nat :=

  match γ with

  | .refl _ =>
      0

  | .step _ _ hRest =>
      Nat.succ hRest.stepCount

/-
Concatenation of represented reversible rearrangement paths.

If γ₁ is a reversible represented path from X to Y and γ₂ is a reversible
represented path from Y to Z, their concatenation is a reversible
represented path from X to Z.

Because each elementary step in both component paths carries accessibility
in both directions, the concatenated path does so as well.
-/
def ReversibleRearrangementPath.append
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y Z : Configuration K O}
    (γ₁ : ReversibleRearrangementPath A O X Y)
    (γ₂ : ReversibleRearrangementPath A O Y Z) :
    ReversibleRearrangementPath A O X Z :=

  match γ₁ with

  | .refl _ =>
      γ₂

  | .step hForward hBackward hRest =>
      .step hForward hBackward (hRest.append γ₂)

/-
Reversal of a represented reversible rearrangement path.

Because every elementary step stores accessibility in both directions, the
entire represented path can be traversed in reverse order.

For a path

    X → Y → ... → Z

the reversed path is constructed by first reversing the remainder

    Z → ... → Y

and then appending the reversed first step

    Y → X.

Thus `reverse` preserves the represented sequence of elementary
rearrangements, but traverses them in the opposite order and direction.
-/
def ReversibleRearrangementPath.reverse
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (γ : ReversibleRearrangementPath A O X Y) :
    ReversibleRearrangementPath A O Y X :=

  match γ with

  | .refl X =>
      .refl X

  | .step hForward hBackward hRest =>
      hRest.reverse.append
        (.step hBackward hForward (.refl _))

/-
Step count is additive under concatenation of reversible paths.

If γ₁ runs reversibly from X to Y and γ₂ runs reversibly from Y to Z,
then the number of elementary rearrangements in the concatenated path is

    stepCount (γ₁ ++ γ₂)
      =
    stepCount γ₁ + stepCount γ₂.

This is the reversible-path analogue of the corresponding result for
accessible paths.
-/
theorem ReversibleRearrangementPath.stepCount_append
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y Z : Configuration K O}
    (γ₁ : ReversibleRearrangementPath A O X Y)
    (γ₂ : ReversibleRearrangementPath A O Y Z) :
    (γ₁.append γ₂).stepCount =
      γ₁.stepCount + γ₂.stepCount := by

  induction γ₁ with

  | refl X =>
      simp [ReversibleRearrangementPath.append,
            ReversibleRearrangementPath.stepCount]

  | step hForward hBackward hRest ih =>
      simp only [ReversibleRearrangementPath.append,
                 ReversibleRearrangementPath.stepCount]

      rw [ih]

      exact
        Nat.add_right_comm
          hRest.stepCount
          γ₂.stepCount
          1

/-
Reversal preserves the number of elementary rearrangements.

A represented reversible path and its reverse contain exactly the same
elementary rearrangements, traversed in the opposite order and direction.

Therefore

    stepCount (reverse γ) = stepCount γ.

This is the discrete form of the manuscript statement that reversing a
specified reversible path leaves its path length unchanged.
-/
theorem ReversibleRearrangementPath.stepCount_reverse
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (γ : ReversibleRearrangementPath A O X Y) :
    γ.reverse.stepCount = γ.stepCount := by

  induction γ with

  | refl X =>
      rfl

  | step hForward hBackward hRest ih =>
      simp [ReversibleRearrangementPath.reverse,
            ReversibleRearrangementPath.stepCount_append,
            ReversibleRearrangementPath.stepCount,
            ih]

/-
Manuscript path length of reversible exploration.

For a represented reversible path

    γ : X₀ → X₁ → ... → Xₙ

the Time manuscript defines

    L(γ) = n,

the number of represented elementary rearrangements.

`stepCount` already computes exactly this quantity.  `pathLength` gives it
the manuscript-facing name while keeping the underlying representation
explicit.

The value depends on the resolution at which elementary rearrangements are
represented.  No identification with physical duration is made here.
-/
def ReversibleRearrangementPath.pathLength
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (γ : ReversibleRearrangementPath A O X Y) :
    Nat :=

  γ.stepCount

/-
Path length is additive under concatenation.

For reversible represented paths

    γ₁ : X → Y
    γ₂ : Y → Z,

the manuscript path length satisfies

    L(γ₁ ++ γ₂) = L(γ₁) + L(γ₂).

This follows directly from additivity of the underlying elementary-step
count.
-/
theorem ReversibleRearrangementPath.pathLength_append
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y Z : Configuration K O}
    (γ₁ : ReversibleRearrangementPath A O X Y)
    (γ₂ : ReversibleRearrangementPath A O Y Z) :
    (γ₁.append γ₂).pathLength =
      γ₁.pathLength + γ₂.pathLength := by

  simpa [ReversibleRearrangementPath.pathLength] using
    ReversibleRearrangementPath.stepCount_append γ₁ γ₂

/-
Path length is invariant under reversal.

A represented reversible path and its reverse contain the same elementary
rearrangements, traversed in the opposite order and direction.

Therefore the manuscript path length satisfies

    L(reverse γ) = L(γ).

This is the manuscript-facing version of the previously proved invariance
of `stepCount`.
-/
theorem ReversibleRearrangementPath.pathLength_reverse
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (γ : ReversibleRearrangementPath A O X Y) :
    γ.reverse.pathLength = γ.pathLength := by

  simpa [ReversibleRearrangementPath.pathLength] using
    ReversibleRearrangementPath.stepCount_reverse γ

/-
A represented reversible path determines operational reachability.

Every elementary step of a `ReversibleRearrangementPath` is accessible in
the forward direction.  Forgetting the additional backward-accessibility
certificates therefore gives an ordinary finite operational reachability
statement between the same endpoints.

This theorem discards path-specific information; it retains only the fact
that the endpoint is operationally reachable.
-/
theorem ReversibleRearrangementPath.is_operationalReachability
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (γ : ReversibleRearrangementPath A O X Y) :
    OperationalReachability D A O X Y := by

  induction γ with

  | refl X =>
      exact OperationalReachability.refl X

  | step hForward hBackward hRest ih =>
      exact OperationalReachability.step hForward ih

/-
Endpoints of a represented reversible path are reversibly equivalent.

A reversible represented path from X to Y gives

    X ≼ Y

by following the path forward.

Reversing that same represented path gives

    Y ≼ X.

Therefore the endpoint configurations satisfy the previously defined
reversible-equivalence relation

    X ~R Y.

This connects the path-level notion of reversible exploration to the
quotient construction used in the temporal-order formalization.
-/
theorem ReversibleRearrangementPath.endpoints_reversibleEquivalent
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (γ : ReversibleRearrangementPath A O X Y) :
    ReversibleEquivalent D A O X Y := by

  constructor

  · exact γ.is_operationalReachability

  · exact γ.reverse.is_operationalReachability

/-
A represented reversible path remains within one reversible class.

The preceding theorem established that the endpoint configurations of a
represented reversible path satisfy

    X ~R Y.

The quotient `ReversibleClass` identifies exactly configurations related by
`ReversibleEquivalent`.  Therefore X and Y determine the same quotient
element:

    [X]R = [Y]R.

This is the formal version of the manuscript statement that reversible
exploration takes place within a single operationally reversible
equivalence class.
-/
theorem ReversibleRearrangementPath.same_reversibleClass
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (γ : ReversibleRearrangementPath A O X Y) :
    reversibleClassOf D A O X =
      reversibleClassOf D A O Y := by

  exact Quotient.sound γ.endpoints_reversibleEquivalent

 
end SBI.Time
