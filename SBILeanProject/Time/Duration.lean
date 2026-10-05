import SBILeanProject.Time.ReversibleExploration
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace SBI.Time

/-
Abstract operational measure of reversible duration.

This structure records only the algebraic properties required of a
repeatable duration parameter.  It deliberately does not yet specify the
physical mechanism by which duration is generated.

For N equivalent repetitions, `duration N` is the accumulated operational
reversible duration.  The defining structural requirements are

    duration 0 = 0

and

    duration (m + n)
      =
    duration m + duration n.

Thus successive equivalent repetitions compose as successive increments
of one operational duration parameter.

Later in this file this abstract structure is physically realized from
represented reversible rearrangement paths at an available operational
resolution.  There the dimensionless duration count is identified with
represented path length and dimensional duration is obtained by local
calibration:

    Δτ(γ) = L(γ) δτ_loc.

The represented path length counts resolved rearrangement steps at that
resolution.  It is not asserted to count fundamental substratum events;
finer relational rearrangement may remain unresolved.

The present structure is therefore an abstract interface for operational
duration, not an assumption that duration exists independently of physical
change.

No continuity of duration is assumed here.
-/

structure OperationalDurationParameter where

  duration :
    Nat → Real

  duration_zero :
    duration 0 = 0

  duration_add :
    ∀ m n : Nat,
      duration (m + n) =
        duration m + duration n

/-
Equivalent repetitions accumulate equal increments of reversible duration.

For a reproducible reversible process, let

    duration 1

be the operational duration assigned to one cycle or one equivalent
repetition.

Additivity then implies that N equivalent repetitions accumulate

    duration N = N • duration 1,

where `N • x` denotes N-fold addition of x.

This is the formal counterpart of the manuscript relation

    Δτ = N Δτ₀.

No continuity of duration is assumed here, and no relation to microscopic
path length is part of this abstract theorem.  The later physical
realization supplies such a relation by deriving accumulated duration from
the elementary rearrangements actually executed along a reversible path.
-/
theorem OperationalDurationParameter.duration_eq_nsmul
    (τ : OperationalDurationParameter)
    (N : Nat) :
    τ.duration N = N • τ.duration 1 := by

  induction N with

  | zero =>
      simpa using τ.duration_zero

  | succ N ih =>
      calc
        τ.duration (N + 1)
            = τ.duration N + τ.duration 1 := τ.duration_add N 1
        _ = N • τ.duration 1 + τ.duration 1 := by
              rw [ih]
        _ = (N + 1) • τ.duration 1 := by
              rw [add_nsmul, one_nsmul]

/-
Abstract operational clock.

An `OperationalDurationParameter` supplies the additive structure

    duration (m + n) = duration m + duration n.

To represent an operational clock reading we additionally require one
nominal tick to have strictly positive duration:

    duration 1 > 0.

At this level a tick is still an abstract repetition count.  No physical
mechanism producing the tick is specified by this structure itself.

Later in this file a `ReversibleClock` supplies that mechanism: one tick is
an actually executed nontrivial reversible cycle, and its duration is
derived from the elementary rearrangements contained in that cycle.

Thus `OperationalClock` is retained as a useful abstract interface, while
the physical clock construction establishes why its positive increments
arise.

No irreversible precedence is introduced by this structure.
-/

structure OperationalClock extends OperationalDurationParameter where

  tick_positive :
    0 < duration 1

/-
Each additional clock tick strictly increases accumulated reversible
duration.

The clock remains free to return to the same physical configuration after
each reversible cycle.  What increases here is not configuration
displacement but accumulated traversal count expressed as duration.

Thus the intrinsic sequence of repeated reversible histories

    0, 1, 2, ...

carries a strictly increasing duration assignment.
-/
theorem OperationalClock.duration_succ_gt
    (τ : OperationalClock)
    (N : Nat) :

    τ.duration N < τ.duration (N + 1) := by

  calc
    τ.duration N
        = 0 + τ.duration N := by simp

    _ < τ.duration 1 + τ.duration N :=
      add_lt_add_left
        τ.tick_positive
        (τ.duration N)

    _ = τ.duration N + τ.duration 1 := by
      rw [add_comm]

    _ = τ.duration (N + 1) := by
      symm
      exact τ.duration_add N 1

/-
Accumulated reversible clock duration is strictly increasing with the
intrinsic tick count.

If fewer repetitions of the reversible clock process have occurred, then
the accumulated duration is strictly smaller:

    m < n  →  duration m < duration n.

This is the formal expression of the fact that reversible return of the
clock mechanism to an earlier configuration does not undo accumulated
duration.  The configuration may recur; the traversed repetition count
does not.
-/
theorem OperationalClock.duration_strictMono
    (τ : OperationalClock) :

    StrictMono τ.duration := by

  exact strictMono_nat_of_lt_succ τ.duration_succ_gt

/-
Any positive number of clock ticks corresponds to positive accumulated
reversible duration.

This follows from two facts already built into the clock structure:

  • zero ticks have zero duration;
  • duration is strictly increasing with tick count.

Thus a nontrivial reversible traversal cannot have zero accumulated
duration even if the clock mechanism returns to its initial configuration.
-/
theorem OperationalClock.duration_pos
    (τ : OperationalClock)
    {N : Nat}
    (hN : 0 < N) :

    0 < τ.duration N := by

  have h :
      τ.duration 0 < τ.duration N :=
    τ.duration_strictMono hN

  simpa [τ.duration_zero] using h

/-
The intrinsic clock tick count is faithfully represented by accumulated
reversible duration.

Because clock duration is strictly increasing, two different repetition
counts cannot receive the same duration value.  Thus returning repeatedly
to the same clock configuration does not erase how much reversible
traversal has accumulated.

In particular,

    duration m = duration n  →  m = n.

The duration parameter therefore retains the intrinsic ordering and
distinction of the repeated clock histories.
-/
theorem OperationalClock.duration_injective
    (τ : OperationalClock) :

    Function.Injective τ.duration := by

  exact τ.duration_strictMono.injective

/-
Local calibration scale for operational reversible duration.

The preceding development represents reversible exploration at a fixed
available operational resolution.  The path length

    L(γ)

therefore counts represented elementary rearrangements at that resolution.
Such a represented step is not asserted to be a fundamentally indivisible
event of the substratum.  It may contain finer relational rearrangement
that is unresolved at the available operational resolution.

At the represented level, however, each resolved step contributes one unit
to path length.  `LocalDurationScale` supplies the positive metrical
calibration

    δτ_loc > 0

that converts one unit of this dimensionless operational path count into
duration units.

Thus `stepDuration` should be interpreted as a calibration factor for one
resolved unit of operational traversal, not as an assertion that all
unresolved substratum rearrangements possess an identical fundamental
duration.

The qualification "local" means that the calibration applies to the local
clock process under consideration.  When identically constituted clocks
are compared at the same operational resolution using the same calibration,
differences in accumulated operational duration arise from differences in
the number of resolved rearrangements represented as having occurred.

This introduces metrical calibration data, not a fourth SBI admissibility
axiom.
-/
structure LocalDurationScale where

  stepDuration :
    Real

  stepDuration_positive :
    0 < stepDuration


/-
Accumulated operational duration of a represented reversible path.

At the available operational resolution, a represented reversible path γ
contains

    L(γ)

resolved rearrangement steps.  The dimensionless operational duration count
is therefore identified with this represented path length.

Given a local calibration scale δτ_loc, define

    Δτ(γ) = L(γ) δτ_loc.

In Lean, `N • x` denotes N-fold addition of x, so this definition requires
no explicit conversion of the natural-valued path length into a real number.

The construction is explicitly resolution dependent.  A represented step
may contain finer relational rearrangement that remains unresolved at the
available operational resolution.  Such finer structure still belongs to
the substratum insofar as it participates in the admissible relational
organization, but it is not counted separately in `L(γ)`.

Thus the formal statement is

    no resolved represented step  →  no accumulated operational duration

at the resolution under consideration.  It does not assert that the
substratum is literally static whenever the represented path has zero
length.

The accumulated duration depends on the traversed represented path, not
merely on its endpoint configurations.  A reversible path may therefore
return to its starting configuration while still accumulating positive
operational duration.
-/
def ReversibleRearrangementPath.accumulatedDuration
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (δ : LocalDurationScale)
    (γ : ReversibleRearrangementPath A O X Y) :
    Real :=

  γ.pathLength • δ.stepDuration

/-
A represented reversible path with zero resolved path length accumulates no
operational duration at the available resolution.

If

    L(γ) = 0,

then by definition

    Δτ(γ) = 0.

Here `L(γ) = 0` means that no rearrangement step is separately resolved and
represented in this path.  It does not imply that the complete substratum
undergoes no finer relational rearrangement.  Such finer change may remain
unresolved at the available operational resolution.

Thus this theorem concerns the operational duration represented at the
chosen resolution:

    no resolved represented step
        →
    no accumulated operational duration.

In particular, a zero-step represented path does not advance the
operational reading of a local clock at that resolution.
-/
theorem ReversibleRearrangementPath.accumulatedDuration_eq_zero_of_pathLength_eq_zero
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (δ : LocalDurationScale)
    (γ : ReversibleRearrangementPath A O X Y)
    (h : γ.pathLength = 0) :

    γ.accumulatedDuration δ = 0 := by

  simp [ReversibleRearrangementPath.accumulatedDuration, h]

/-
Any represented reversible traversal with positive resolved path length
accumulates strictly positive operational duration.

If

    0 < L(γ),

then at least one rearrangement step is separately resolved and represented
at the available operational resolution.  Since each resolved path unit is
converted by the strictly positive calibration `δ.stepDuration`, the
accumulated operational duration must also be strictly positive:

    0 < Δτ(γ).

Together with the preceding zero-length theorem, this gives the operational
statement

    no resolved represented step  →  zero operational duration,
    resolved represented change  →  positive operational duration.

This does not exclude finer relational rearrangement within the substratum
that remains unresolved at the available operational resolution.

The orientation of the represented rearrangement is irrelevant here.
Traversing a reversible step in either direction still contributes one
resolved unit of operational traversal and therefore a positive calibrated
duration.
-/
theorem ReversibleRearrangementPath.accumulatedDuration_pos_of_pathLength_pos
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (δ : LocalDurationScale)
    (γ : ReversibleRearrangementPath A O X Y)
    (h : 0 < γ.pathLength) :

    0 < γ.accumulatedDuration δ := by

  rw [ReversibleRearrangementPath.accumulatedDuration]

  simpa [nsmul_eq_mul] using
    mul_pos
      (Nat.cast_pos.mpr h : (0 : Real) < (γ.pathLength : Real))
      δ.stepDuration_positive

/-
Zero accumulated operational duration is equivalent to zero represented
path length at the available operational resolution.

For a positive local calibration scale,

    Δτ(γ) = 0  ↔  L(γ) = 0.

The reverse implication follows directly from the definition.  For the
forward implication, any positive represented path length gives strictly
positive accumulated operational duration.

The equivalence therefore concerns the resolved operational description:

    zero accumulated operational duration
        ↔
    no resolved represented rearrangement.

It does not imply that the complete substratum undergoes no finer
relational rearrangement when `L(γ) = 0`.  Such finer structure may remain
unresolved at the available operational resolution.

This distinction is essential: the theorem identifies zero duration with
zero represented traversal, not with ontological stasis of the substratum.
-/
theorem ReversibleRearrangementPath.accumulatedDuration_eq_zero_iff_pathLength_eq_zero
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (δ : LocalDurationScale)
    (γ : ReversibleRearrangementPath A O X Y) :

    γ.accumulatedDuration δ = 0 ↔
      γ.pathLength = 0 := by

  constructor

  · intro hDuration

    by_contra hLength

    have hPositiveLength :
        0 < γ.pathLength :=
      Nat.pos_of_ne_zero hLength

    have hPositiveDuration :
        0 < γ.accumulatedDuration δ :=
      γ.accumulatedDuration_pos_of_pathLength_pos
        δ
        hPositiveLength

    exact
      (ne_of_gt hPositiveDuration)
        hDuration

  · intro hLength

    exact
      γ.accumulatedDuration_eq_zero_of_pathLength_eq_zero
        δ
        hLength

/-
Accumulated operational duration is additive under concatenation of
represented reversible paths.

If a represented reversible path γ₁ from X to Y is followed by a represented
reversible path γ₂ from Y to Z, then

    Δτ(γ₁ ++ γ₂)
      =
    Δτ(γ₁) + Δτ(γ₂).

At the available operational resolution, represented path length is
additive:

    L(γ₁ ++ γ₂)
      =
    L(γ₁) + L(γ₂).

Applying the same local calibration to the combined resolved path therefore
gives additive operational duration.

No claim is made here that unresolved substratum rearrangements occurring
within different represented steps have identical microscopic durations.
The theorem concerns the additive count of resolved represented traversal
and its common metrical calibration at the chosen operational resolution.

The accumulated duration depends on the represented path actually traversed,
not merely on the net relation between its endpoint configurations.
-/
theorem ReversibleRearrangementPath.accumulatedDuration_append
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y Z : Configuration K O}
    (δ : LocalDurationScale)
    (γ₁ : ReversibleRearrangementPath A O X Y)
    (γ₂ : ReversibleRearrangementPath A O Y Z) :

    (γ₁.append γ₂).accumulatedDuration δ
      =
    γ₁.accumulatedDuration δ
      +
    γ₂.accumulatedDuration δ := by

  simp [ReversibleRearrangementPath.accumulatedDuration,
        ReversibleRearrangementPath.pathLength_append,
        add_mul]

/-
Reversing a represented reversible traversal preserves accumulated
operational duration.

A represented reversible path and its reverse contain exactly the same
resolved rearrangement steps at the available operational resolution,
traversed in the opposite order and direction.  Since accumulated
operational duration is obtained from represented path length rather than
from signed configuration displacement,

    Δτ(reverse γ) = Δτ(γ).

Thus reversal changes the orientation of the represented traversal but not
the amount of resolved change accumulated along it.

Executing the inverse represented path therefore does not undo previously
accumulated duration and does not contribute negative duration.  It
constitutes an additional traversal with its own positive operational
duration whenever the represented path length is nonzero.

This statement concerns the represented path structure.  It does not imply
that the unresolved relational organization followed during a physical
return must be unique; other return paths may exist and may have different
represented path lengths and therefore different accumulated durations.
-/
theorem ReversibleRearrangementPath.accumulatedDuration_reverse
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (δ : LocalDurationScale)
    (γ : ReversibleRearrangementPath A O X Y) :

    γ.reverse.accumulatedDuration δ
      =
    γ.accumulatedDuration δ := by

  simp [ReversibleRearrangementPath.accumulatedDuration,
        ReversibleRearrangementPath.pathLength_reverse]

/-
More resolved represented change gives more accumulated operational duration.

Consider two represented reversible traversals evaluated at the same
available operational resolution and using the same local calibration.
If

    L(γ₁) < L(γ₂),

then

    Δτ(γ₁) < Δτ(γ₂).

The comparison concerns resolved operational path length.  It does not
assert that the two traversals contain identical unresolved substratum
structure, nor that finer rearrangements below the available operational
resolution contribute equally.

What matters at this level is that the second represented traversal contains
more resolved path units than the first, and the same positive calibration
is applied to both.

This is the formal comparison principle relevant to identically constituted
local clocks described at the same operational resolution: if one clock
executes fewer resolved rearrangements than the other, it accumulates less
operational duration.

Thus the duration difference is attributed to a difference in represented
executed change, not to an independently varying rate of an external time
parameter.
-/
theorem ReversibleRearrangementPath.accumulatedDuration_lt_of_pathLength_lt
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X₁ Y₁ X₂ Y₂ : Configuration K O}
    (δ : LocalDurationScale)
    (γ₁ : ReversibleRearrangementPath A O X₁ Y₁)
    (γ₂ : ReversibleRearrangementPath A O X₂ Y₂)
    (h : γ₁.pathLength < γ₂.pathLength) :

    γ₁.accumulatedDuration δ <
      γ₂.accumulatedDuration δ := by

  have hLength :
      (γ₁.pathLength : Real) <
        (γ₂.pathLength : Real) := by

    exact_mod_cast h

  simpa [ReversibleRearrangementPath.accumulatedDuration,
         nsmul_eq_mul] using
    mul_lt_mul_of_pos_right
      hLength
      δ.stepDuration_positive

/-
One missing resolved rearrangement produces exactly one calibrated duration
difference.

Suppose two represented reversible traversals are evaluated at the same
available operational resolution and using the same local calibration, with

    L(γ₂) = L(γ₁) + 1.

Then

    Δτ(γ₂) = Δτ(γ₁) + δτ_loc.

Thus one additional resolved unit of represented traversal contributes
exactly one additional unit of the local duration calibration.

The statement is operational.  It does not assert that the corresponding
physical processes differ by exactly one fundamental substratum event.
Either represented step may contain finer relational rearrangement that is
unresolved at the available operational resolution.

This theorem gives the simplest formal model of two identically constituted
local clocks diverging at a common resolution because one executes one more
resolved rearrangement than the other.

No independently varying background time or separate change of clock rate is
introduced.  The duration difference follows directly from the difference
in represented path count.
-/
theorem ReversibleRearrangementPath.accumulatedDuration_eq_add_step_of_pathLength_succ
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X₁ Y₁ X₂ Y₂ : Configuration K O}
    (δ : LocalDurationScale)
    (γ₁ : ReversibleRearrangementPath A O X₁ Y₁)
    (γ₂ : ReversibleRearrangementPath A O X₂ Y₂)
    (h :
      γ₂.pathLength =
        γ₁.pathLength + 1) :

    γ₂.accumulatedDuration δ
      =
    γ₁.accumulatedDuration δ
      +
    δ.stepDuration := by

  rw [ReversibleRearrangementPath.accumulatedDuration]
  rw [ReversibleRearrangementPath.accumulatedDuration]
  rw [h]
  rw [add_nsmul, one_nsmul]



/-
A represented reversible cycle.

A reversible cycle is a represented reversible rearrangement path whose
final configuration is the same as its initial configuration.

Such a path may nevertheless have nonzero path length.  This is the
structural reason that accumulated reversible exploration cannot be reduced
to a displacement between endpoint configurations.
-/
abbrev ReversibleCycle
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    (X : Configuration K O) :=

  ReversibleRearrangementPath A O X X


/-
A reversible physical clock at the available operational resolution.

A clock consists of

  • a specified represented reversible cycle γ based at configuration X,
  • a proof that the cycle contains at least one resolved represented
    rearrangement, and
  • a positive local calibration converting represented path length into
    operational duration.

The nontriviality condition

    0 < L(γ)

excludes the zero-step reflexive path from being treated as a physical
clock tick at the represented level.

Clock duration is not supplied independently of the represented dynamics.
It is obtained from the reversible path resolved as having been traversed:

    Δτ(γ) = L(γ) δτ_loc.

Consequently, the operational reading of the clock advances only when its
represented mechanism executes resolved rearrangement steps.  If no such
step is resolved and represented, no operational duration increment occurs
at that resolution.

This does not assert that the substratum is static between represented clock
steps.  Finer relational rearrangement may occur while remaining unresolved
at the available operational resolution.

The represented cycle may nevertheless return to exactly the same
configuration after every tick.  Recurrence of represented configuration
does not erase the operational duration accumulated by the traversal.
-/
structure ReversibleClock
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    (X : Configuration K O) where

  cycle :
    ReversibleCycle (A := A) (O := O) X

  cycle_nontrivial :
    0 < cycle.pathLength

  durationScale :
    LocalDurationScale

/-
Operational duration accumulated by one represented clock cycle.

Because clock duration is derived from the represented reversible traversal,

    tickDuration = Δτ(cycle),

it is determined, at the available operational resolution, by

  • the number of resolved rearrangement steps represented in the cycle,
    and
  • the positive local duration calibration.

It is therefore not an independently assigned clock parameter.

This statement does not imply that one represented clock cycle contains a
fixed number of fundamental substratum rearrangements.  Finer relational
structure may remain unresolved at the available operational resolution.
`tickDuration` measures the calibrated duration of the represented cycle.
-/
def ReversibleClock.tickDuration
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X : Configuration K O}
    (clock : ReversibleClock (A := A) X) :
    Real :=

  clock.cycle.accumulatedDuration clock.durationScale


/-
One complete represented clock cycle accumulates strictly positive
operational duration.

A reversible physical clock is required to have positive represented path
length,

    0 < L(cycle),

at the available operational resolution.  Since each resolved path unit is
converted by the strictly positive local calibration, one complete
represented cycle has positive operational duration:

    0 < tickDuration.

This statement concerns the represented clock process.  It does not require
the cycle to contain any specified number of fundamental substratum
rearrangements; finer relational structure may remain unresolved at the
available operational resolution.
-/
theorem ReversibleClock.tickDuration_pos
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X : Configuration K O}
    (clock : ReversibleClock (A := A) X) :

    0 < clock.tickDuration := by

  exact
    clock.cycle.accumulatedDuration_pos_of_pathLength_pos
      clock.durationScale
      clock.cycle_nontrivial



/-
Repeated execution of a represented reversible cycle accumulates repeated
operational duration.

For a represented reversible cycle γ and local duration calibration δ,

    Δτ(iterate γ N)
      =
    N • Δτ(γ).

Thus the duration associated with repeated clock operation is not an
independent counter placed alongside the represented dynamics.  It is
obtained from the resolved path traversal represented as having occurred at
the available operational resolution.

If one represented cycle is not executed, its resolved path contribution is
absent and so is its contribution to accumulated operational duration.

This statement does not require successive cycles to contain identical
unresolved substratum rearrangements.  It requires only that they are
represented as repetitions of the same reversible cycle at the operational
resolution under consideration and are evaluated using the same local
calibration.
-/
def ReversibleCycle.iterate
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X : Configuration K O}
    (γ : ReversibleCycle (A := A) (O := O) X) :
    Nat →
    ReversibleCycle (A := A) (O := O) X

  | 0 =>
      .refl X

  | Nat.succ N =>
      (iterate γ N).append γ

/-
Path length accumulates under repeated reversible cycles.

If γ is a reversible cycle based at X, then N successive executions of
that same cycle have path length

    L(iterate γ N) = N * L(γ).

Thus a process can return repeatedly to the same configuration while
accumulating nonzero reversible traversal.

This is precisely why reversible duration cannot be identified with
endpoint displacement.
-/
theorem ReversibleCycle.pathLength_iterate
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X : Configuration K O}
    (γ : ReversibleCycle (A := A) (O := O) X)
    (N : Nat) :
    (ReversibleCycle.iterate γ N).pathLength =
      N * γ.pathLength := by

  induction N with

  | zero =>
      simp [ReversibleCycle.iterate,
            ReversibleRearrangementPath.pathLength,
            ReversibleRearrangementPath.stepCount]

  | succ N ih =>
      rw [ReversibleCycle.iterate]
      rw [ReversibleRearrangementPath.pathLength_append]
      rw [ih]
      rw [Nat.succ_mul]

/-
Repeated execution of a reversible cycle accumulates repeated duration.

For a reversible cycle γ and local duration scale δ,

    Δτ(iterate γ N)
      =
    N • Δτ(γ).

Thus the duration associated with repeated clock operation is not an
independent counter placed alongside the dynamics.  It is obtained from the
actual reversible traversal that has occurred.

If one execution of the cycle fails to occur, its contribution to the
accumulated duration is absent.
-/
theorem ReversibleCycle.accumulatedDuration_iterate
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X : Configuration K O}
    (δ : LocalDurationScale)
    (γ : ReversibleCycle (A := A) (O := O) X)
    (N : Nat) :

    (ReversibleCycle.iterate γ N).accumulatedDuration δ
      =
    N • γ.accumulatedDuration δ := by

  induction N with

  | zero =>
      simp [ReversibleCycle.iterate,
            ReversibleRearrangementPath.accumulatedDuration,
            ReversibleRearrangementPath.pathLength,
            ReversibleRearrangementPath.stepCount]

  | succ N ih =>
      rw [ReversibleCycle.iterate]
      rw [ReversibleRearrangementPath.accumulatedDuration_append]
      rw [ih]
      rw [succ_nsmul]

/-
Accumulated operational duration after repeated represented clock cycles.

For a reversible clock, `durationAfterCycles N` is the duration associated
with the represented path obtained from N executions of the clock cycle:

    durationAfterCycles N
      =
    Δτ(iterate cycle N).

The reading is therefore derived from the resolved traversal represented as
having occurred at the available operational resolution; it is not an
independent counter attached to the clock.

If a represented cycle is not executed, its path contribution is absent and
so is its contribution to accumulated operational duration.

Finer relational rearrangement may occur within or between represented clock
steps without being separately resolved.  `durationAfterCycles` records only
the calibrated traversal represented at the operational resolution under
consideration.
-/
def ReversibleClock.durationAfterCycles
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X : Configuration K O}
    (clock : ReversibleClock (A := A) X)
    (N : Nat) :
    Real :=

  (ReversibleCycle.iterate clock.cycle N).accumulatedDuration
    clock.durationScale

/-
Repeated represented clock cycles accumulate equal calibrated duration
increments.

Because `durationAfterCycles N` is defined from the represented repeated
reversible path, and because

    Δτ(iterate cycle N)
      =
    N • Δτ(cycle),

we obtain

    durationAfterCycles N
      =
    N • tickDuration.

This has the same algebraic form as the earlier abstract operational-clock
relation, but its meaning is now stronger: the count N refers to represented
cycle executions at the available operational resolution.

A represented cycle that is not executed contributes neither a represented
path increment nor an operational duration increment.

No claim is made that different executions contain identical unresolved
substratum rearrangements.  Equality of the increments refers to repetition
of the same represented clock cycle evaluated with the same local
calibration.
-/
theorem ReversibleClock.durationAfterCycles_eq_nsmul
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X : Configuration K O}
    (clock : ReversibleClock (A := A) X)
    (N : Nat) :

    clock.durationAfterCycles N
      =
    N • clock.tickDuration := by

  simp [ReversibleClock.durationAfterCycles,
        ReversibleClock.tickDuration,
        ReversibleCycle.accumulatedDuration_iterate]

/-
Every additional represented clock cycle strictly increases accumulated
operational duration.

After N represented cycles, executing one further nontrivial represented
cycle changes the reading from

    durationAfterCycles N

to

    durationAfterCycles (N + 1).

Because one represented clock cycle has strictly positive operational
duration,

    tickDuration > 0,

the latter reading is strictly larger.

This is the clock-level expression of the operational duration structure:
additional resolved traversal gives additional calibrated duration.  If the
additional represented cycle does not occur, this increment is absent.

The statement concerns the clock description at the available operational
resolution.  It does not assert that no unresolved substratum rearrangement
occurs when the represented clock reading remains unchanged.
-/
theorem ReversibleClock.durationAfterCycles_succ_gt
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X : Configuration K O}
    (clock : ReversibleClock (A := A) X)
    (N : Nat) :

    clock.durationAfterCycles N <
      clock.durationAfterCycles (N + 1) := by

  rw [clock.durationAfterCycles_eq_nsmul N]
  rw [clock.durationAfterCycles_eq_nsmul (N + 1)]
  rw [add_nsmul, one_nsmul]

  exact
    lt_add_of_pos_right
      (N • clock.tickDuration)
      clock.tickDuration_pos

/-
Accumulated operational clock duration is strictly increasing with the
number of represented cycles executed.

If

    m < n,

then

    durationAfterCycles m
      <
    durationAfterCycles n.

The ordering is derived from the represented reversible paths themselves.
At the available operational resolution, more completed represented cycles
contain more resolved path units and therefore correspond to greater
accumulated operational duration under the same positive calibration.

For two identically constituted clocks described at the same operational
resolution and using the same cycle and calibration, a clock that has
completed fewer represented cycles necessarily records less operational
duration.

This theorem makes no claim about the amount or detailed structure of finer
substratum rearrangement that may remain unresolved within those cycles.
-/
theorem ReversibleClock.durationAfterCycles_strictMono
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X : Configuration K O}
    (clock : ReversibleClock (A := A) X) :

    StrictMono clock.durationAfterCycles := by

  exact strictMono_nat_of_lt_succ
    clock.durationAfterCycles_succ_gt

/-
Every reversible physical clock determines an abstract operational clock.

The earlier `OperationalClock` abstraction requires

  • zero duration at zero ticks,
  • additive accumulation over successive tick counts, and
  • a strictly positive duration for one tick.

For a `ReversibleClock` these properties no longer need to be supplied as
independent duration assumptions.  They follow from the calibrated duration
of the represented reversible cycle at the available operational
resolution.

Thus the operational duration function is

    N ↦ durationAfterCycles N.

This establishes the logical direction

    represented reversible clock dynamics
        →
    calibrated operational clock parameter,

rather than treating the clock parameter as an independently flowing
temporal variable.

The construction remains resolution dependent.  A represented clock cycle
may contain finer relational rearrangement that is unresolved at the
available operational resolution.  `OperationalClock` records the
coarse-grained duration structure generated by the represented clock
process, not a count of fundamental substratum events.
-/
def ReversibleClock.toOperationalClock
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X : Configuration K O}
    (clock : ReversibleClock (A := A) X) :
    OperationalClock where

  duration :=
    clock.durationAfterCycles

  duration_zero := by
    rw [clock.durationAfterCycles_eq_nsmul 0]
    simp

  duration_add := by
    intro m n

    rw [clock.durationAfterCycles_eq_nsmul (m + n)]
    rw [clock.durationAfterCycles_eq_nsmul m]
    rw [clock.durationAfterCycles_eq_nsmul n]
    rw [add_nsmul]

  tick_positive := by
    rw [clock.durationAfterCycles_eq_nsmul 1]
    simpa using clock.tickDuration_pos


/-
Bundle theorem — reversible-duration characterization.

This theorem collects the central manuscript-level properties of accumulated
duration along represented reversible rearrangement paths.

For one positive local duration calibration:

  1. zero accumulated duration is equivalent to zero represented path length;

  2. accumulated duration is additive under concatenation of represented
     reversible paths;

  3. reversing a represented reversible path preserves its accumulated
     duration.

Together these statements express the key conceptual distinction used in the
Time manuscript: duration measures accumulated resolved change along the
executed path and is not a signed displacement that is undone by reversal.

No additional physical assumption is introduced here. The theorem only
packages results already proved separately.
-/
theorem reversibleDuration_characterization
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y Z : Configuration K O}
    (δ : LocalDurationScale)
    (γ₁ : ReversibleRearrangementPath A O X Y)
    (γ₂ : ReversibleRearrangementPath A O Y Z) :

    (γ₁.accumulatedDuration δ = 0 ↔
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
      γ₁.accumulatedDuration δ) := by

  constructor

  · exact
      γ₁.accumulatedDuration_eq_zero_iff_pathLength_eq_zero δ

  constructor

  · exact
      γ₁.accumulatedDuration_append δ γ₂

  · exact
      γ₁.accumulatedDuration_reverse δ

end SBI.Time
