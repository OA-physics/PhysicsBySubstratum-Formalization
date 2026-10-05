import SBILeanProject.GR.ReachabilityBoundary

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Closed local metric state and second-order closure.

This file formalizes the logical core of the manuscript lemma
"Second-order closure of metric dynamics".

The manuscript argument contains two distinct ingredients and they must
remain distinct in Lean:

  1. a closed local metric state contains all physically relevant local
     information required for continued geometric evolution;

  2. irreducible higher-than-second-order metric dynamics would require
     additional independent local continuation data beyond the metric and
     its first directed-time derivative.

The second statement is the standard initial-data bridge for genuinely
higher-order dynamics.  It is NOT derived from A1--A3 by Lean here.  It is
represented explicitly by the field

    higherOrder_requires_independent

below.

Once that bridge is stated, the incompatibility with a closed metric-only
state is purely logical.

Why A1 and A3 do not appear directly in the theorem statement
--------------------------------------------------------------
In the manuscript, A1 supplies the physical reason that information capable
of affecting subsequent evolution cannot reside in an external historical
variable absent from the current relational state.  A3 supplies the reason
that information retained from earlier evolution can affect the present
only through persistent relational organization that is present now.

The current SBI Lean axioms encode relational invariance/support and
persistence, but they do not already contain a theorem saying that every
possible continuation datum of an effective metric PDE is represented by a
particular local state variable.  Pretending otherwise would hide a physical
coarse-graining/closure bridge inside the formalization.

Accordingly this file formalizes only the implication actually needed:

    closed metric state
      +
    irreducible higher order requires independent continuation data
      ->
    no irreducible higher-order metric dynamics.

No tensor calculus, manifold theory, Einstein equation, Lovelock theorem,
or Ostrogradsky argument is assumed here.
-/

/-
Abstract semantics for local metric closure.

`MetricData` represents the instantaneous coarse-grained metric data.
`RateData` represents its admissible first directed-time derivative.
Together they form the manuscript's local metric state

    (g, dg/dt).

`ContinuationData` represents any additional local datum that would be
required to select continued geometric evolution once the present metric
state is fixed.

`AdmissibleContinuation s d` means that d is an admissible continuation
datum for the same present state s.

`IrreduciblyHigherOrder` is intentionally left abstract.  The formalization
does not identify a specific differential operator or derivative order.
Instead, the physical/mathematical bridge is stated explicitly:

    if the metric dynamics are irreducibly higher order,
    then one present metric state admits at least two distinct independent
    continuation data.

This captures precisely the part of the higher-order initial-value argument
used in the manuscript.
-/
structure MetricClosureSemantics where

  MetricData : Type

  RateData : Type

  ContinuationData : Type

  AdmissibleContinuation :
    (MetricData × RateData) →
    ContinuationData →
    Prop

  IrreduciblyHigherOrder : Prop

  higherOrder_requires_independent :
    IrreduciblyHigherOrder →
    ∃ (s : MetricData × RateData)
      (d₁ d₂ : ContinuationData),
      AdmissibleContinuation s d₁ ∧
      AdmissibleContinuation s d₂ ∧
      d₁ ≠ d₂

/-
Closed local metric state.

A metric description is closed when fixing the present metric and its first
instantaneous rate leaves no additional independent continuation datum.

Formally, for any fixed present state s = (g, dg/dt), any two admissible
continuation data must coincide.

This is an "at most one" statement.  It does not assert that a continuation
exists for every conceivable state, only that no further independent local
state variable is required when continuation is admissible.
-/
def ClosedLocalMetricState
    (S : MetricClosureSemantics) : Prop :=

  ∀ (s : S.MetricData × S.RateData)
    {d₁ d₂ : S.ContinuationData},
    S.AdmissibleContinuation s d₁ →
    S.AdmissibleContinuation s d₂ →
    d₁ = d₂

/-
Independent continuation data.

Such data exist when the same present metric state admits two distinct
continuation data.  This is exactly what a metric-only closed state excludes.
-/
def HasIndependentContinuationData
    (S : MetricClosureSemantics) : Prop :=

  ∃ (s : S.MetricData × S.RateData)
    (d₁ d₂ : S.ContinuationData),
    S.AdmissibleContinuation s d₁ ∧
    S.AdmissibleContinuation s d₂ ∧
    d₁ ≠ d₂

/-
A closed local metric state excludes independent continuation data.

This is the basic logical closure theorem.  If the same present state had
two distinct admissible continuation data, closure would identify them,
contradicting their independence.
-/
theorem closedLocalMetricState_no_independentContinuation
    (S : MetricClosureSemantics)
    (hClosed : ClosedLocalMetricState S) :

    ¬ HasIndependentContinuationData S := by

  intro hIndependent

  rcases hIndependent with
    ⟨s, d₁, d₂, h₁, h₂, hDistinct⟩

  have hEq : d₁ = d₂ :=
    hClosed s h₁ h₂

  exact hDistinct hEq

/-
Second-order closure theorem in manuscript-facing logical form.

If

  * the metric and its first directed-time derivative constitute a closed
    local effective state, and

  * irreducibly higher-order metric dynamics would require additional
    independent continuation data,

then the metric dynamics cannot be irreducibly higher order.

The second bullet is carried by `MetricClosureSemantics` itself through
`higherOrder_requires_independent`.  The theorem therefore exposes rather
than hides the physical/mathematical bridge on which the manuscript's
second-order conclusion depends.
-/
theorem closedMetricState_excludes_irreducibleHigherOrder
    (S : MetricClosureSemantics)
    (hClosed : ClosedLocalMetricState S) :

    ¬ S.IrreduciblyHigherOrder := by

  intro hHigher

  have hIndependent :
      HasIndependentContinuationData S :=
    S.higherOrder_requires_independent hHigher

  exact
    (closedLocalMetricState_no_independentContinuation
      S hClosed)
      hIndependent

/-
Contrapositive form useful for dependency auditing.

If irreducibly higher-order metric dynamics are present, then the metric and
its first rate cannot by themselves form a closed local effective state.
This corresponds to the manuscript statement that physically encoded
additional continuation information would have to be promoted to additional
local state variables.
-/
theorem irreducibleHigherOrder_not_metricOnlyClosed
    (S : MetricClosureSemantics)
    (hHigher : S.IrreduciblyHigherOrder) :

    ¬ ClosedLocalMetricState S := by

  intro hClosed

  exact
    (closedMetricState_excludes_irreducibleHigherOrder
      S hClosed)
      hHigher

/-
Scope clarification.

The theorem above excludes only `IrreduciblyHigherOrder` dynamics in the
sense encoded by the explicit bridge

    higher order -> independent continuation data.

It does NOT exclude a higher-derivative equation obtained after eliminating
additional local degrees of freedom from a larger closed system.  In such a
representation the omitted variables can encode the apparent additional
continuation data, so the reduced metric description is not metric-only
closed in the sense defined here.

This comment mirrors the manuscript qualification and is intentionally not
turned into a theorem without first formalizing a concrete elimination
procedure.
-/

end GR
end SBI
