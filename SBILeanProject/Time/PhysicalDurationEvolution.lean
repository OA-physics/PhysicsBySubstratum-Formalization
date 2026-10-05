import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic
import SBILeanProject.Time.Duration
set_option autoImplicit false

namespace SBI.Time
/--
Accumulated physical duration in the coarse-grained effective description.

Physical duration is represented by the nonnegative real numbers.  The
nonnegativity is structural: elapsed duration may vanish or increase, but
negative accumulated duration is not part of this parameter space.
-/
abbrev PhysicalDuration := NNReal

/-
Bridge from accumulated operational duration to physical duration.

`Duration.lean` constructs the calibrated duration of a represented
reversible path as a real number

    Δτ(γ) = L(γ) δτ_loc.

Because the local calibration is strictly positive and represented path
length is nonnegative, this accumulated duration can never be negative.
The present definition therefore packages that already constructed quantity
as an element of the nonnegative physical-duration domain

    PhysicalDuration = ℝ≥0.

This is the formal bridge between the discrete represented-path construction
and the duration parameter used by the later coarse-grained evolution.

Importantly, no continuous dynamics is derived here.  The definition only
states that the calibrated path duration belongs to the same nonnegative
duration domain used by the effective theory.  Autonomy, continuity,
differentiability, and generator structure remain additional properties of a
chosen coarse-grained dynamical description.
-/
def ReversibleRearrangementPath.physicalDuration
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (δ : LocalDurationScale)
    (γ : ReversibleRearrangementPath A O X Y) :
    PhysicalDuration :=

  ⟨γ.accumulatedDuration δ, by
    by_cases hLength : γ.pathLength = 0

    · have hZero :
          γ.accumulatedDuration δ = 0 :=
        γ.accumulatedDuration_eq_zero_of_pathLength_eq_zero
          δ
          hLength
      simp [hZero]

    · exact
        le_of_lt
          (γ.accumulatedDuration_pos_of_pathLength_pos
            δ
            (Nat.pos_of_ne_zero hLength))
  ⟩

/-
The nonnegative physical-duration value contains exactly the calibrated
operational duration already constructed from the represented path.

Thus the bridge changes only the codomain from a real number known to be
nonnegative to the explicit nonnegative-real type.  It does not alter the
duration value or introduce a second duration measure.
-/
@[simp] theorem ReversibleRearrangementPath.coe_physicalDuration
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (δ : LocalDurationScale)
    (γ : ReversibleRearrangementPath A O X Y) :

    (γ.physicalDuration δ : Real)
      =
    γ.accumulatedDuration δ := by

  rfl


/-
Bundle theorem — physical-duration characterization.

This theorem collects the manuscript-level conclusions connecting represented
reversible traversal, operational clocks, and the nonnegative physical-duration
parameter used by the effective theory.

For one positive local duration calibration and one represented reversible
clock:

  1. accumulated reversible duration has the path-level properties already
     established by `reversibleDuration_characterization`;

  2. the represented reversible clock determines an `OperationalClock`
     whose duration reading is exactly the duration accumulated after the
     corresponding number of represented cycles and is strictly increasing
     with completed cycle count;

  3. the path's `PhysicalDuration` value contains exactly the calibrated
     operational duration already constructed from that path.

Thus the passage from represented reversible traversal to physical duration
does not introduce an independent duration measure.  It packages the
nonnegative calibrated duration in the codomain used by the later effective
dynamics.

No autonomy, continuity, differentiability, or generator property is derived
here.  Those remain additional properties of a chosen coarse-grained
physical-duration evolution.
-/
theorem physicalDuration_characterization
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y Z : Configuration K O}
    (δ : LocalDurationScale)
    (γ₁ : ReversibleRearrangementPath A O X Y)
    (γ₂ : ReversibleRearrangementPath A O Y Z)
    (clock : ReversibleClock (A := A) X) :

    ((γ₁.accumulatedDuration δ = 0 ↔
        γ₁.pathLength = 0)
      ∧
      ((γ₁.append γ₂).accumulatedDuration δ
        =
        γ₁.accumulatedDuration δ
          +
        γ₂.accumulatedDuration δ)
      ∧
      (γ₁.reverse.accumulatedDuration δ
        =
        γ₁.accumulatedDuration δ))
    ∧
    (∃ τop : OperationalClock,
      τop.duration = clock.durationAfterCycles
      ∧
      StrictMono τop.duration)
    ∧
    ((γ₁.physicalDuration δ : Real)
      =
      γ₁.accumulatedDuration δ) := by

  constructor

  · exact
      reversibleDuration_characterization
        δ
        γ₁
        γ₂

  constructor

  · refine ⟨clock.toOperationalClock, ?_, ?_⟩

    · rfl

    · simp [ReversibleClock.toOperationalClock,
        clock.durationAfterCycles_strictMono]

  · exact
      ReversibleRearrangementPath.coe_physicalDuration
        δ
        γ₁


/-
Autonomous effective evolution parameterized by accumulated physical duration.

The preceding `Duration.lean` development constructs operational duration
from represented reversible rearrangement paths.  At that level duration is
discrete at the available operational resolution.

A further coarse-grained effective description may admit a duration
parameter that is treated as continuous.  The appropriate parameter space is
therefore the nonnegative real numbers

    h ∈ ℝ≥0,

not a signed copy of ℝ.

The state type used here represents a chosen effective dynamical domain.
Closure of the evolution within that domain is encoded by the fact that

    evolve h x

is again a value of the same state type.

The autonomous composition law is

    T(0) = id,

    T(h₁ + h₂) = T(h₁) ∘ T(h₂),

for nonnegative accumulated durations `h₁` and `h₂`.

This is a semigroup-style physical-duration evolution.  No negative duration
is introduced.  Reversibility, continuity, differentiability, and the
existence of a generator will be added as separate refinements rather than
being built into this basic structure.
-/
structure AutonomousPhysicalDurationEvolution
    (State : Type*) where

  evolve : PhysicalDuration → State → State

  evolve_zero :
    ∀ x : State,
      evolve 0 x = x

  evolve_add :
    ∀ h₁ h₂ : PhysicalDuration,
    ∀ x : State,
      evolve (h₁ + h₂) x =
        evolve h₁ (evolve h₂ x)


/-
Continuous coarse-grained evolution with respect to physical duration.

The underlying `AutonomousPhysicalDurationEvolution` supplies only the
nonnegative duration parameter and its autonomous composition law.  A
continuous effective description requires additional regularity.

We therefore assume that the effective state type carries a topology and
that, for every effective state `x`, the map

    h ↦ T(h) x

is continuous for

    h ∈ ℝ≥0.

This continuity is a property of the chosen coarse-grained effective
description.  It is not a claim that the underlying substratum or its
represented operational path structure is fundamentally continuous.

In particular, operational duration was constructed from discrete
represented rearrangement counts in `Duration.lean`.  Treating duration as
continuous here is an additional coarse-grained approximation appropriate
when those resolved increments are too fine to retain individually.
-/
structure ContinuousAutonomousPhysicalDurationEvolution
    (State : Type*)
    [TopologicalSpace State]
    extends AutonomousPhysicalDurationEvolution State where

  continuous_in_duration :
    ∀ x : State,
      Continuous
        (fun h : PhysicalDuration =>
          evolve h x)

/-
Right-differentiable coarse-grained evolution with respect to physical
duration.

Physical duration itself has type

    PhysicalDuration = ℝ≥0,

so there is no negative-duration branch.  Mathlib's derivative machinery is
formulated over normed fields such as ℝ.  To express the derivative at the
duration origin, we therefore view the nonnegative-duration evolution as the
real-parameterized map

    h ↦ T(Real.toNNReal h) x

and take its derivative within the set

    [0, ∞) = Set.Ici 0.

Within this set `Real.toNNReal h` is simply the nonnegative real `h`.
Consequently, differentiability within `Set.Ici 0` at zero is precisely the
one-sided regularity required for a right derivative with respect to physical
duration.

The use of a real variable here is only a technical device for Mathlib's
calculus.  No evolution at negative physical duration is introduced or
assumed.

As before, differentiability is an additional property of the chosen
coarse-grained effective description.  It is not derived from the discrete
operational duration construction or from the SBI admissibility axioms.
-/
structure RightDifferentiableAutonomousPhysicalDurationEvolution
    (State : Type*)
    [NormedAddCommGroup State]
    [NormedSpace Real State]
    extends ContinuousAutonomousPhysicalDurationEvolution State where

  differentiableWithinAt_zero :
    ∀ x : State,
      DifferentiableWithinAt Real
        (fun h : Real =>
          evolve (Real.toNNReal h) x)
        (Set.Ici 0)
        0

/-
Reversible physical-duration evolution.

A physical evolution through positive accumulated duration may itself be
reversible as a transformation of the effective state space.

This does not require negative physical duration.  It requires only that,
for each nonnegative duration `h`, the map

    x ↦ T(h) x

is bijective.

Thus reversibility belongs to the state transformation, while the duration
parameter remains in

    ℝ≥0.

The inverse transformation therefore exists as a map on effective states,
but it is not identified here with evolution at a parameter value `-h`,
since negative physical duration is not part of the duration domain.
-/
structure ReversibleAutonomousPhysicalDurationEvolution
    (State : Type*)
    extends AutonomousPhysicalDurationEvolution State where

  evolve_bijective :
    ∀ h : PhysicalDuration,
      Function.Bijective (evolve h)

/-
The reversible state transformation associated with a fixed positive
physical duration.

For each `h : PhysicalDuration`, bijectivity of

    x ↦ T(h) x

allows us to regard the evolution as an equivalence of the effective state
space with itself.

The inverse of this equivalence represents reversal of the state
transformation.  It is deliberately not labelled by `-h`: the physical
duration parameter remains nonnegative.
-/
noncomputable def
    ReversibleAutonomousPhysicalDurationEvolution.evolveEquiv
    {State : Type*}
    (T : ReversibleAutonomousPhysicalDurationEvolution State)
    (h : PhysicalDuration) :
    State ≃ State :=

  Equiv.ofBijective
    (T.evolve h)
    (T.evolve_bijective h)

/-
Reversing the state transformation after evolution recovers the initial
effective state.

The inverse here is the inverse of the bijective transformation `T(h)`.
It is not evolution through a negative duration.

Thus a process may be reversible at the level of effective states while
physical duration remains strictly nonnegative.
-/
theorem
    ReversibleAutonomousPhysicalDurationEvolution.inverse_after_evolve
    {State : Type*}
    (T : ReversibleAutonomousPhysicalDurationEvolution State)
    (h : PhysicalDuration)
    (x : State) :
    (T.evolveEquiv h).symm (T.evolve h x) = x := by

  exact (T.evolveEquiv h).symm_apply_apply x

/-
Evolving after applying the inverse state transformation also recovers the
original effective state.

Together with `inverse_after_evolve`, this shows that `T(h)` is reversible as
a transformation of the effective state space.

Again, the inverse transformation is not interpreted as evolution through
negative physical duration.  Both the physical duration parameter and the
forward evolution map remain defined only for `h ≥ 0`.
-/
theorem
    ReversibleAutonomousPhysicalDurationEvolution.evolve_after_inverse
    {State : Type*}
    (T : ReversibleAutonomousPhysicalDurationEvolution State)
    (h : PhysicalDuration)
    (x : State) :
    T.evolve h ((T.evolveEquiv h).symm x) = x := by

  exact (T.evolveEquiv h).apply_symm_apply x


/-
Bundle theorem — reversible physical-duration evolution.

This theorem collects the two inverse identities that characterize
reversibility of each fixed-duration state transformation.

For every nonnegative physical duration h:

  1. applying the inverse state transformation after evolution recovers the
     initial state;

  2. evolving after applying that inverse transformation also recovers the
     initial state.

The result expresses two-sided invertibility of the state map T(h) without
introducing a negative physical-duration parameter.  Reversal belongs to the
state transformation, while accumulated physical duration remains in ℝ≥0.
-/
theorem reversiblePhysicalDurationEvolution_characterization
    {State : Type*}
    (T : ReversibleAutonomousPhysicalDurationEvolution State) :

    (∀ (h : PhysicalDuration) (x : State),
      (T.evolveEquiv h).symm (T.evolve h x) = x)
    ∧
    (∀ (h : PhysicalDuration) (x : State),
      T.evolve h ((T.evolveEquiv h).symm x) = x) := by

  constructor

  · intro h x
    exact T.inverse_after_evolve h x

  · intro h x
    exact T.evolve_after_inverse h x


/-
Infinitesimal generator of coarse-grained physical-duration evolution.

For a right-differentiable effective evolution, define the generator at an
effective state `x` by differentiating the real-parameterized representation

    h ↦ T(Real.toNNReal h) x

at

    h = 0

within the nonnegative half-line

    Set.Ici 0.

Thus the derivative is taken only from physically admissible duration values

    h ≥ 0.

Formally,

    Gτ(x)
      =
    d/dh⁺ [T(h) x] |_{h = 0}.

The superscript `+` is conceptual notation for the right derivative.  In Lean
it is represented by `derivWithin` on `Set.Ici 0`.

The generator is defined directly with respect to nonnegative accumulated
physical duration.

No negative physical duration is introduced here.

At this stage the generator is simply a map from effective states to
effective states.  Linearity has not been assumed or proved, so this
definition alone does not identify the generator with energy or with a
Hamiltonian.
-/
noncomputable def
    RightDifferentiableAutonomousPhysicalDurationEvolution.generator
    {State : Type*}
    [NormedAddCommGroup State]
    [NormedSpace Real State]
    (T : RightDifferentiableAutonomousPhysicalDurationEvolution State)
    (x : State) :
    State :=

  derivWithin
    (fun h : Real =>
      T.evolve (Real.toNNReal h) x)
    (Set.Ici 0)
    0

/-
The physical-duration generator is the right derivative at duration zero.

By assumption, for every effective state `x`, the coarse-grained evolution

    h ↦ T(Real.toNNReal h) x

is differentiable at zero within the physically allowed duration domain

    Set.Ici 0.

The generator was defined to be precisely that `derivWithin`.  Therefore it
satisfies the corresponding `HasDerivWithinAt` statement:

    d/dh⁺ [T(h) x] |_{h = 0} = Gτ(x).

This theorem turns the generator definition into the derivative statement
that will be used in subsequent evolution equations.

Only the nonnegative-duration side participates in the derivative.  No
negative physical duration or signed extension of the physical evolution is
assumed.
-/
theorem
    RightDifferentiableAutonomousPhysicalDurationEvolution.hasDerivWithinAt_generator
    {State : Type*}
    [NormedAddCommGroup State]
    [NormedSpace Real State]
    (T : RightDifferentiableAutonomousPhysicalDurationEvolution State)
    (x : State) :
    HasDerivWithinAt
      (fun h : Real =>
        T.evolve (Real.toNNReal h) x)
      (T.generator x)
      (Set.Ici 0)
      0 := by

  simpa [RightDifferentiableAutonomousPhysicalDurationEvolution.generator] using
    (T.differentiableWithinAt_zero x).hasDerivWithinAt

/-
The same right-derivative law applies after any accumulated physical duration.

Let `τ` be a nonnegative physical duration and let

    T(τ) x

be the effective state reached after that duration.

Because the differentiability assumption applies to every effective state,
we may use `T(τ) x` as a new initial state.  The infinitesimal continuation

    h ↦ T(h) (T(τ) x),

for `h ≥ 0`, therefore has right derivative

    Gτ(T(τ) x)

at `h = 0`.

This theorem does not yet rewrite the continuation using the semigroup law.
It only establishes the generator at the already-reached state.  The next
step will identify this continuation with evolution through the combined
duration `τ + h`.
-/
theorem
    RightDifferentiableAutonomousPhysicalDurationEvolution.hasDerivWithinAt_from_reached_state
    {State : Type*}
    [NormedAddCommGroup State]
    [NormedSpace Real State]
    (T : RightDifferentiableAutonomousPhysicalDurationEvolution State)
    (x : State)
    (τ : PhysicalDuration) :
    HasDerivWithinAt
      (fun h : Real =>
        T.evolve (Real.toNNReal h) (T.evolve τ x))
      (T.generator (T.evolve τ x))
      (Set.Ici 0)
      0 := by

  exact T.hasDerivWithinAt_generator (T.evolve τ x)

/-
Continuing for an additional duration is equivalent to evolving for the
combined accumulated duration.

Suppose the effective state `x` has already evolved for physical duration

    τ,

and then evolves for a further duration

    h.

The autonomous composition law gives

    T(h) (T(τ) x)
      =
    T(h + τ) x.

Since physical duration is additive and addition on `ℝ≥0` is commutative,

    h + τ = τ + h,

so equivalently

    T(h) (T(τ) x)
      =
    T(τ + h) x.

This is the physical-duration analogue of time-translation autonomy.  It
uses only nonnegative durations and does not introduce a signed parameter or
negative duration.
-/
theorem
    AutonomousPhysicalDurationEvolution.evolve_from_reached_state
    {State : Type*}
    (T : AutonomousPhysicalDurationEvolution State)
    (x : State)
    (τ h : PhysicalDuration) :
    T.evolve h (T.evolve τ x) =
      T.evolve (τ + h) x := by

  calc
    T.evolve h (T.evolve τ x)
        = T.evolve (h + τ) x :=
          (T.evolve_add h τ x).symm
    _ = T.evolve (τ + h) x := by
          rw [add_comm]

/-
Right derivative of evolution after an already accumulated duration.

Suppose the effective state starts at `x` and has already evolved through
physical duration

    τ.

A further nonnegative duration increment `h` gives the state

    T(τ + h) x.

By the autonomous composition law this is the same physical evolution as

    T(h) (T(τ) x).

The preceding right-derivative theorem applies to the already-reached state
`T(τ) x`.  Therefore

    d/dh⁺ [T(τ + h) x] |_{h = 0}
      =
    Gτ(T(τ) x).

This is the local generator equation at arbitrary accumulated duration `τ`.
The derivative is with respect to an additional positive duration increment,
not with respect to a signed time coordinate.
-/
theorem
    RightDifferentiableAutonomousPhysicalDurationEvolution.hasDerivWithinAt_incremented_duration
    {State : Type*}
    [NormedAddCommGroup State]
    [NormedSpace Real State]
    (T : RightDifferentiableAutonomousPhysicalDurationEvolution State)
    (x : State)
    (τ : PhysicalDuration) :
    HasDerivWithinAt
      (fun h : Real =>
        T.evolve (τ + Real.toNNReal h) x)
      (T.generator (T.evolve τ x))
      (Set.Ici 0)
      0 := by

  have hderiv :=
    T.hasDerivWithinAt_from_reached_state x τ

  have hEq :
      ∀ h : Real,
        T.evolve (τ + Real.toNNReal h) x =
          T.evolve (Real.toNNReal h) (T.evolve τ x) := by
    intro h
    calc
      T.evolve (τ + Real.toNNReal h) x
          = T.evolve (Real.toNNReal h + τ) x := by
              rw [add_comm]
      _ = T.evolve (Real.toNNReal h) (T.evolve τ x) :=
            T.evolve_add (Real.toNNReal h) τ x

  exact hderiv.congr
    (fun h _ => hEq h)
    (hEq 0)

/-
Explicit right-derivative evolution equation at arbitrary accumulated
physical duration.

The preceding theorem states the local evolution equation in Mathlib's
`HasDerivWithinAt` form.  Since the nonnegative half-line

    Set.Ici 0

has a unique derivative direction at its endpoint zero, we can extract the
corresponding equality for `derivWithin`:

    d/dh⁺ [T(τ + h) x] |_{h = 0}
      =
    Gτ(T(τ) x).

This is the manuscript-facing form of the coarse-grained
physical-duration generator equation.

The derivative is one-sided because physical duration is nonnegative.  No
negative duration or signed extension of the physical-duration evolution is
required.
-/
theorem
    RightDifferentiableAutonomousPhysicalDurationEvolution.derivWithin_incremented_duration
    {State : Type*}
    [NormedAddCommGroup State]
    [NormedSpace Real State]
    (T : RightDifferentiableAutonomousPhysicalDurationEvolution State)
    (x : State)
    (τ : PhysicalDuration) :
    derivWithin
      (fun h : Real =>
        T.evolve (τ + Real.toNNReal h) x)
      (Set.Ici 0)
      0
      =
      T.generator (T.evolve τ x) := by

  exact
    (T.hasDerivWithinAt_incremented_duration x τ).derivWithin
      (uniqueDiffWithinAt_Ici 0)


/-
Bundle theorem — physical-duration generator characterization.

This theorem collects the manuscript-level conclusions of the effective
physical-duration generator branch.

For a right-differentiable autonomous coarse-grained evolution:

  1. continuing for an additional nonnegative duration depends only on the
     accumulated duration interval and composes by duration addition;

  2. the generator at any effective state is the right derivative at
     physical duration zero;

  3. after any already accumulated duration τ, the right derivative with
     respect to a further nonnegative duration increment is the generator
     evaluated at the reached state.

The first statement is the nonnegative-duration form of translation
autonomy.  The second and third statements identify the infinitesimal
generator and its local evolution equation without introducing negative
physical duration.

No additional physical assumption is introduced by this theorem.  It only
packages the autonomy and generator results already proved above so that the
manuscript dependency map has one recognizable endpoint for this branch.

The theorem does not identify the generator with energy or with a
Hamiltonian.  That identification belongs to the effective physical
interpretation once the state space and its dynamical structure have been
specified.
-/
theorem physicalDurationGenerator_characterization
    {State : Type*}
    [NormedAddCommGroup State]
    [NormedSpace Real State]
    (T : RightDifferentiableAutonomousPhysicalDurationEvolution State) :

    (∀ (x : State) (τ h : PhysicalDuration),
      T.evolve h (T.evolve τ x) =
        T.evolve (τ + h) x)
    ∧
    (∀ x : State,
      HasDerivWithinAt
        (fun h : Real =>
          T.evolve (Real.toNNReal h) x)
        (T.generator x)
        (Set.Ici 0)
        0)
    ∧
    (∀ (x : State) (τ : PhysicalDuration),
      derivWithin
        (fun h : Real =>
          T.evolve (τ + Real.toNNReal h) x)
        (Set.Ici 0)
        0
        =
        T.generator (T.evolve τ x)) := by

  constructor

  · intro x τ h
    exact
      AutonomousPhysicalDurationEvolution.evolve_from_reached_state
        T.toContinuousAutonomousPhysicalDurationEvolution.toAutonomousPhysicalDurationEvolution
        x
        τ
        h

  constructor

  · intro x
    exact T.hasDerivWithinAt_generator x

  · intro x τ
    exact T.derivWithin_incremented_duration x τ


end SBI.Time
