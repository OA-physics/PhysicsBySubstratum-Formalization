import SBILeanProject.SBI.Frustration

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Constraint loading and local reconfiguration capacity.

This file begins the Lean formalization of the GR companion manuscript.
It deliberately starts with the part of the GR argument that can be stated
most directly in terms of already formalized SBI objects.

Manuscript role
---------------
The GR manuscript introduces the local compatible-configuration set

    C(Γ)

for a finite family Γ of persistence requirements, and observes that
strengthening the requirement family cannot enlarge that set:

    Γ₁ ⊆ Γ₂
        ->
    C(Γ₂) ⊆ C(Γ₁).

The manuscript calls the remaining compatible configurational freedom
"reconfiguration capacity".  At this stage we intentionally do NOT assign
that capacity a scalar value.  Only the inclusion ordering is needed.

Relation to the existing SBI formalization
------------------------------------------
Frustration.lean already contains the essential logical machinery:

  * LocalPersistenceRequirement;
  * SatisfiesAllRequirements;
  * semantic equality of persistence requirements;
  * satisfaction passing to a semantic subfamily;
  * FiniteLocalStructuralFrustration;
  * frustration_requires_reorganization.

This file therefore does not re-prove the SBI physics.  It packages those
results in the terminology used by the GR domain-of-validity argument.

Nothing in this file introduces geometry, energy, gravity, a horizon, or a
temporal ordering.  Those interpretations come later.  The purpose here is
to isolate the exact structural statement on which those later arguments
will depend.
-/

/-
A local configuration compatible with a finite family of persistence
requirements.

For a fixed observer O and local relational conjunction v, Γ is a finite
list of persistence requirements.  A local configuration Z belongs to the
manuscript set C(Γ) exactly when it satisfies every requirement in Γ.

We keep this as a predicate rather than constructing a separate Set object.
That matches the representation already used in Frustration.lean and keeps
the dependency on the SBI development transparent.
-/
def CompatibleConfiguration
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Γ : List (LocalPersistenceRequirement S O v))
    (Z : LocalConfigurationSpace K O v) : Prop :=

  SatisfiesAllRequirements S O v Γ Z

/-
Semantic inclusion of persistence-requirement families.

RequirementFamilyIncluded S O v Γ₁ Γ₂ means that every physical
persistence requirement represented in Γ₁ is also represented in Γ₂.

This is intentionally stronger than literal List membership and weaker than
syntactic equality.  A persistence requirement in Γ₁ may be represented in
Γ₂ by a different representative of the same persistence class.  The
existing SBI predicate SamePersistenceRequirement identifies those cases.

Thus this definition is the formal counterpart of the manuscript relation

    Γ₁ ⊆ Γ₂

where Γ denotes physical persistence requirements rather than Lean syntax.
-/
def RequirementFamilyIncluded
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Γ₁ Γ₂ : List (LocalPersistenceRequirement S O v)) : Prop :=

  ∀ Q₁ : LocalPersistenceRequirement S O v,
    Q₁ ∈ Γ₁ →
    ∃ Q₂ : LocalPersistenceRequirement S O v,
      Q₂ ∈ Γ₂ ∧
      SamePersistenceRequirement S O v Q₂ Q₁

/-
The compatible-configuration set is antitone in the persistence
requirements.

If Γ₂ contains every persistence requirement represented in Γ₁, then any
configuration satisfying Γ₂ necessarily satisfies Γ₁:

    Γ₁ ⊆ Γ₂
        ->
    C(Γ₂) ⊆ C(Γ₁).

This is the exact formal content of the GR manuscript statement that adding
persistence constraints cannot increase the remaining compatible local
configurational freedom.

No claim is made that the inclusion must be strict.  A newly added
requirement may be redundant.
-/
theorem compatibleConfiguration_of_includedRequirements
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Γ₁ Γ₂ : List (LocalPersistenceRequirement S O v))
    (hIncluded :
      RequirementFamilyIncluded S O v Γ₁ Γ₂)
    (Z : LocalConfigurationSpace K O v)
    (hCompatible₂ :
      CompatibleConfiguration S O v Γ₂ Z) :

    CompatibleConfiguration S O v Γ₁ Z := by

  unfold CompatibleConfiguration at hCompatible₂ ⊢

  exact
    satisfiesAllRequirements_of_semanticSubfamily
      S O v
      Γ₂
      Z
      hCompatible₂
      Γ₁
      hIncluded

/-
Ordering statement for reconfiguration capacity.

The GR manuscript does not yet possess a scalar microscopic measure of
reconfiguration capacity.  What is already meaningful is an ordering:
Γ₂ has no greater reconfiguration capacity than Γ₁ when every local
configuration compatible with Γ₂ is also compatible with Γ₁.

In set language:

    C(Γ₂) ⊆ C(Γ₁).

This definition therefore captures exactly the amount of structure needed
for the later reachability argument without pretending that a numerical
capacity has already been derived.
-/
def NoGreaterReconfigurationCapacity
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Γ₂ Γ₁ : List (LocalPersistenceRequirement S O v)) : Prop :=

  ∀ Z : LocalConfigurationSpace K O v,
    CompatibleConfiguration S O v Γ₂ Z →
    CompatibleConfiguration S O v Γ₁ Z

/-
Constraint strengthening cannot increase reconfiguration capacity.

This is the manuscript implication

    Γ₁ ⊆ Γ₂
        ->
    C(Γ₂) ⊆ C(Γ₁).

The proof is only a GR-facing repackaging of the already formalized SBI
subfamily theorem above.
-/
theorem includedRequirements_noGreaterReconfigurationCapacity
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Γ₁ Γ₂ : List (LocalPersistenceRequirement S O v))
    (hIncluded :
      RequirementFamilyIncluded S O v Γ₁ Γ₂) :

    NoGreaterReconfigurationCapacity S O v Γ₂ Γ₁ := by

  intro Z hCompatible₂

  exact
    compatibleConfiguration_of_includedRequirements
      S O v Γ₁ Γ₂ hIncluded Z hCompatible₂

/-
Strict reduction of reconfiguration capacity.

The compatible family is strictly reduced when two things hold:

  1. every configuration compatible with Γ₂ is compatible with Γ₁;
  2. at least one configuration compatible with Γ₁ is excluded by Γ₂.

This separates the always-valid monotonicity statement from the additional
physical fact that a particular added persistence requirement is genuinely
restrictive rather than redundant.
-/
def StrictlyLowerReconfigurationCapacity
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Γ₂ Γ₁ : List (LocalPersistenceRequirement S O v)) : Prop :=

  NoGreaterReconfigurationCapacity S O v Γ₂ Γ₁
  ∧
  ∃ Z : LocalConfigurationSpace K O v,
    CompatibleConfiguration S O v Γ₁ Z
    ∧
    ¬ CompatibleConfiguration S O v Γ₂ Z

/-
If the stronger family really excludes a configuration that was compatible
with the weaker family, then the reduction of reconfiguration capacity is
strict.
-/
theorem includedRequirements_strictlyLower_of_exclusion
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Γ₁ Γ₂ : List (LocalPersistenceRequirement S O v))
    (hIncluded :
      RequirementFamilyIncluded S O v Γ₁ Γ₂)
    (hExclusion :
      ∃ Z : LocalConfigurationSpace K O v,
        CompatibleConfiguration S O v Γ₁ Z
        ∧
        ¬ CompatibleConfiguration S O v Γ₂ Z) :

    StrictlyLowerReconfigurationCapacity S O v Γ₂ Γ₁ := by

  constructor

  · exact
      includedRequirements_noGreaterReconfigurationCapacity
        S O v Γ₁ Γ₂ hIncluded

  · exact hExclusion

/-
Exhaustion of local reconfiguration capacity.

At the purely structural level used here, capacity is exhausted when there
is no local configuration satisfying the complete finite requirement
family Γ:

    C(Γ) = ∅.

This is exactly the compatibility failure appearing in finite local
structural frustration.  The definition does not yet say what physical
process produced the requirement family, nor does it identify exhaustion
with energy density, curvature, or a horizon.
-/
def ReconfigurationCapacityExhausted
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Γ : List (LocalPersistenceRequirement S O v)) : Prop :=

  ¬ ∃ Z : LocalConfigurationSpace K O v,
      CompatibleConfiguration S O v Γ Z

/-
Finite local structural frustration exhausts the compatible local
configuration family.

This is not a new physical result: FiniteLocalStructuralFrustration was
already defined upstream as a nonempty finite requirement family with no
simultaneously compatible local configuration.  The theorem records its
GR interpretation as exhaustion of local reconfiguration capacity.
-/
theorem structuralFrustration_exhaustsReconfigurationCapacity
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Γ : List (LocalPersistenceRequirement S O v))
    (hFrustrated :
      FiniteLocalStructuralFrustration S O v Γ) :

    ReconfigurationCapacityExhausted S O v Γ := by

  simpa [ReconfigurationCapacityExhausted,
         CompatibleConfiguration]
    using hFrustrated.2

/-
Bundle theorem: saturation plus continued persistence requires relational
reorganization.

The first conclusion says that the original persistence-requirement family
has exhausted its compatible local realization set.

The second conclusion imports the existing SBI theorem
frustration_requires_reorganization: if another local situation succeeds in
preserving its persistence requirements, it cannot simply retain the same
frustrated relational organization.  Some relational reorganization must
have occurred.

This theorem is useful for the GR dependency graph because it gives one
explicit endpoint for the upstream saturation mechanism:

    local persistence constraints
        -> structural frustration / exhausted capacity
        -> continued persistence requires reorganization.

Again, no temporal direction is asserted between Situation₁ and Situation₂
by this theorem itself; that distinction belongs to the Time development.
-/
theorem structuralFrustration_capacityExhausted_and_reorganizationRequired
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Situation₁ Situation₂ :
      LocalPersistenceSituation S O v)
    (hFrustrated :
      FiniteLocalStructuralFrustration
        S O v Situation₁.requirements)
    (hPreserves₂ :
      SituationPreservesRequirements S O v Situation₂) :

    ReconfigurationCapacityExhausted
        S O v Situation₁.requirements
    ∧
    RelationalReorganization
        S O v Situation₁ Situation₂ := by

  constructor

  · exact
      structuralFrustration_exhaustsReconfigurationCapacity
        S O v Situation₁.requirements hFrustrated

  · exact
      frustration_requires_reorganization
        S O v
        Situation₁ Situation₂
        hFrustrated
        hPreserves₂

end GR
end SBI
