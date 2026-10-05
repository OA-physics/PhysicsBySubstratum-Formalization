import SBILeanProject.GR.ConstraintCapacity

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Constraint-dependent reachability and limiting configurations.

This file formalizes the next step of the GR domain-of-validity argument.
ConstraintCapacity.lean established that strengthening persistence
requirements cannot enlarge the family of locally compatible
configurations.  The manuscript then argues that sufficiently restrictive
constraint loading can also restrict the admissible rearrangements and
therefore the reachability domain built from them.

There is one genuine physical bridge here.  The existing SBI formalization
does not say that every strengthening of persistence requirements must
remove dynamical transitions.  What is needed, and what is stated explicitly
below as semantics of the constrained transition relation, is only the
monotonicity condition

    Γ₁ ⊆ Γ₂
        and
    X ->_{Γ₂} Y
        imply
    X ->_{Γ₁} Y.

In words: imposing additional persistence requirements may remove an
otherwise admissible local rearrangement, but cannot create a rearrangement
that was forbidden before the additional requirements were imposed.

Once that bridge is stated, the rest of the reachability argument is purely
logical.  In particular we prove:

  * strengthening constraints cannot enlarge finite reachability;
  * a terminal configuration has no nontrivial reachable continuation;
  * once a configuration is terminal under a weaker requirement family,
    strengthening the constraints cannot restore continuation.

The manuscript later interprets a physically realized limiting
configuration of this kind as a reachability horizon.  That physical
identification is deliberately NOT built into the definitions here.
No geometry, metric, energy, curvature, black-hole interior, or temporal
coordinate is assumed in this file.
-/

/-
Constraint-dependent local transition semantics.

For a fixed observer O and local relational conjunction v,

    AdmissibleStep Γ X Y

means that Y can be obtained from X by one locally represented admissible
rearrangement while the finite persistence-requirement family Γ is in
force.

The field `step_antitone` is the physical monotonicity bridge described
above.  `RequirementFamilyIncluded S O v Γ₁ Γ₂` means that Γ₂ is at least
as restrictive in the sense that it contains every physical persistence
requirement represented in Γ₁.

Thus a transition surviving Γ₂ must already have been available under Γ₁.
The converse is not required: additional constraints may eliminate steps.
-/
structure ConstraintReachabilitySemantics
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O) where

  AdmissibleStep :
    List (LocalPersistenceRequirement S O v) →
    LocalConfigurationSpace K O v →
    LocalConfigurationSpace K O v →
    Prop

  step_antitone :
    ∀
      (Γ₁ Γ₂ : List (LocalPersistenceRequirement S O v))
      {X Y : LocalConfigurationSpace K O v},
      RequirementFamilyIncluded S O v Γ₁ Γ₂ →
      AdmissibleStep Γ₂ X Y →
      AdmissibleStep Γ₁ X Y

/-
Finite reachability under one fixed persistence-requirement family.

`ConstrainedReachability R Γ X Y` means that Y is reachable from X by a
finite sequence of `R.AdmissibleStep Γ` rearrangements.

The relation is reflexive because zero-step continuation is always allowed
as a reachability statement.  This does not mean that a physical
rearrangement occurs in the reflexive case.

This is structurally the same reflexive-transitive closure pattern used
elsewhere in the SBI/Time development, but it is stated here on local
configurations because the GR capacity argument is local to one resolved
relational neighborhood.
-/
inductive ConstrainedReachability
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    {S : LocalPersistenceSemantics P}
    {O : Observer M}
    {v : LocalRelationalConjunction C O}
    (R : ConstraintReachabilitySemantics S O v)
    (Γ : List (LocalPersistenceRequirement S O v)) :
    LocalConfigurationSpace K O v →
    LocalConfigurationSpace K O v →
    Prop

  | refl
      (X : LocalConfigurationSpace K O v) :
      ConstrainedReachability R Γ X X

  | step
      {X Y Z : LocalConfigurationSpace K O v}
      (hStep : R.AdmissibleStep Γ X Y)
      (hRest : ConstrainedReachability R Γ Y Z) :
      ConstrainedReachability R Γ X Z

/-
Strengthening persistence requirements cannot enlarge finite reachability.

If Γ₂ contains all physical requirements represented in Γ₁, every step
available under Γ₂ is also available under Γ₁ by `step_antitone`.
Induction over the finite rearrangement chain therefore gives

    Reach_{Γ₂}(X) ⊆ Reach_{Γ₁}(X).

This is the reachability counterpart of the compatible-configuration
antitonicity theorem in ConstraintCapacity.lean.
-/
theorem constrainedReachability_of_includedRequirements
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (R : ConstraintReachabilitySemantics S O v)
    (Γ₁ Γ₂ : List (LocalPersistenceRequirement S O v))
    (hIncluded : RequirementFamilyIncluded S O v Γ₁ Γ₂)
    {X Y : LocalConfigurationSpace K O v}
    (hReach₂ : ConstrainedReachability R Γ₂ X Y) :

    ConstrainedReachability R Γ₁ X Y := by

  induction hReach₂ with

  | refl X =>
      exact ConstrainedReachability.refl X

  | step hStep hRest ih =>
      exact
        ConstrainedReachability.step
          (R.step_antitone Γ₁ Γ₂ hIncluded hStep)
          ih

/-
Reachability-domain inclusion in manuscript form.

Instead of constructing a Set-valued Ω(X,Γ), we state inclusion
extensionally: every configuration reachable under the stronger family Γ₂
is also reachable under Γ₁.
-/
def NoGreaterReachabilityDomain
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    {S : LocalPersistenceSemantics P}
    {O : Observer M}
    {v : LocalRelationalConjunction C O}
    (R : ConstraintReachabilitySemantics S O v)
    (Γ₂ Γ₁ : List (LocalPersistenceRequirement S O v))
    (X : LocalConfigurationSpace K O v) : Prop :=

  ∀ Y : LocalConfigurationSpace K O v,
    ConstrainedReachability R Γ₂ X Y →
    ConstrainedReachability R Γ₁ X Y

/-
Constraint strengthening cannot enlarge the reachability domain.
-/
theorem includedRequirements_noGreaterReachabilityDomain
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (R : ConstraintReachabilitySemantics S O v)
    (Γ₁ Γ₂ : List (LocalPersistenceRequirement S O v))
    (hIncluded : RequirementFamilyIncluded S O v Γ₁ Γ₂)
    (X : LocalConfigurationSpace K O v) :

    NoGreaterReachabilityDomain R Γ₂ Γ₁ X := by

  intro Y hReach₂

  exact
    constrainedReachability_of_includedRequirements
      S O v R Γ₁ Γ₂ hIncluded hReach₂

/-
Terminal configuration under a fixed requirement family.

A local configuration X is terminal when there is no admissible one-step
rearrangement beginning at X while Γ is in force.

This is deliberately stronger and cleaner than saying that outward
reachability becomes one-way.  It formalizes the manuscript claim that at a
limiting configuration nothing further happens in the represented local
relational evolution: there is no next admissible rearrangement.

Because finite reachability is reflexive, X remains reachable from itself by
the zero-step path.  Terminality excludes every positive-step continuation.
-/
def TerminalUnderConstraints
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    {S : LocalPersistenceSemantics P}
    {O : Observer M}
    {v : LocalRelationalConjunction C O}
    (R : ConstraintReachabilitySemantics S O v)
    (Γ : List (LocalPersistenceRequirement S O v))
    (X : LocalConfigurationSpace K O v) : Prop :=

  ¬ ∃ Y : LocalConfigurationSpace K O v,
      R.AdmissibleStep Γ X Y

/-
A terminal configuration has no reachable state other than itself.

Any non-reflexive constrained reachability proof begins with one admissible
step.  Terminality excludes exactly such a first step.  Therefore the only
configuration reachable from a terminal X is X itself.

This theorem is the formal core of the manuscript statement that there is
no physical sequence of local states "beyond" the limiting reachability
configuration.
-/
theorem terminal_reachability_eq_self
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    {S : LocalPersistenceSemantics P}
    {O : Observer M}
    {v : LocalRelationalConjunction C O}
    (R : ConstraintReachabilitySemantics S O v)
    (Γ : List (LocalPersistenceRequirement S O v))
    (X : LocalConfigurationSpace K O v)
    (hTerminal : TerminalUnderConstraints R Γ X)
    {Y : LocalConfigurationSpace K O v}
    (hReach : ConstrainedReachability R Γ X Y) :

    Y = X := by

  cases hReach with

  | refl _ =>
      rfl

  | step hXY hRest =>
      exact False.elim (hTerminal ⟨_, hXY⟩)

/-
Equivalent negative formulation: a distinct configuration cannot be
reached from a terminal configuration.
-/
theorem terminal_no_distinct_reachable
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    {S : LocalPersistenceSemantics P}
    {O : Observer M}
    {v : LocalRelationalConjunction C O}
    (R : ConstraintReachabilitySemantics S O v)
    (Γ : List (LocalPersistenceRequirement S O v))
    (X : LocalConfigurationSpace K O v)
    (hTerminal : TerminalUnderConstraints R Γ X)
    {Y : LocalConfigurationSpace K O v}
    (hDistinct : Y ≠ X) :

    ¬ ConstrainedReachability R Γ X Y := by

  intro hReach

  have hEq : Y = X :=
    terminal_reachability_eq_self
      R Γ X hTerminal hReach

  exact hDistinct hEq

/-
Strengthening constraints cannot restore continuation once terminality has
already been reached.

If Γ₁ ⊆ Γ₂ and X has no admissible outgoing step under Γ₁, then X also has
no outgoing step under the stronger family Γ₂.  Otherwise `step_antitone`
would turn such a Γ₂-step into a forbidden Γ₁-step.
-/
theorem terminal_preserved_by_constraintStrengthening
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (R : ConstraintReachabilitySemantics S O v)
    (Γ₁ Γ₂ : List (LocalPersistenceRequirement S O v))
    (hIncluded : RequirementFamilyIncluded S O v Γ₁ Γ₂)
    (X : LocalConfigurationSpace K O v)
    (hTerminal₁ : TerminalUnderConstraints R Γ₁ X) :

    TerminalUnderConstraints R Γ₂ X := by

  intro hStep₂

  rcases hStep₂ with ⟨Y, hXY₂⟩

  have hXY₁ : R.AdmissibleStep Γ₁ X Y :=
    R.step_antitone Γ₁ Γ₂ hIncluded hXY₂

  exact hTerminal₁ ⟨Y, hXY₁⟩

/-
Limiting reachability configuration.

For the later manuscript interpretation we need both:

  * the configuration still satisfies the operative persistence
    requirements, so the persistent structure is well defined there;
  * no further locally admissible rearrangement leaves that configuration.

This is the structural object that may later be interpreted physically as
a reachability boundary.  The definition itself contains no horizon or GR
terminology.
-/
def LimitingReachabilityConfiguration
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (R : ConstraintReachabilitySemantics S O v)
    (Γ : List (LocalPersistenceRequirement S O v))
    (X : LocalConfigurationSpace K O v) : Prop :=

  CompatibleConfiguration S O v Γ X
  ∧
  TerminalUnderConstraints R Γ X

/-
A limiting reachability configuration has no physically represented
continuation to a distinct local configuration.

This is a direct corollary of terminality, but it is stated in the exact
form needed by the GR manuscript: the persistent configuration remains
compatible at the limiting state while no further admissible local state is
reachable from it.
-/
theorem limitingConfiguration_no_distinct_continuation
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (R : ConstraintReachabilitySemantics S O v)
    (Γ : List (LocalPersistenceRequirement S O v))
    (X : LocalConfigurationSpace K O v)
    (hLimiting : LimitingReachabilityConfiguration S O v R Γ X)
    {Y : LocalConfigurationSpace K O v}
    (hDistinct : Y ≠ X) :

    ¬ ConstrainedReachability R Γ X Y := by

  exact
    terminal_no_distinct_reachable
      R Γ X hLimiting.2 hDistinct

end GR
end SBI
