import SBILeanProject.SBI.Axioms

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Inertial persistence and the structural content of Newton I.

This file formalizes the logical core of the GR manuscript's argument for
unconstrained inertial propagation.

The manuscript claim is deliberately weaker than a microscopic equation of
motion.  It says that a persistent structure cannot acquire a physically
meaningful change in its propagation character without relational structure
supporting that change.

The existing SBI axiom A1 already contains exactly the abstract principle
needed for this step:

    physically meaningful relation
        ->
    relational support.

A3 supplies the notion of persistent identity across distinct relational
realizations.  A2 constrains how an actual influence is locally mediated,
but it is not needed for the purely negative statement proved here:

    no relational support
        ->
    no physically meaningful propagation-character change.

Keeping that dependency separation explicit is important.  The later
coarse-grained identification

    unchanged propagation character
        ->
    d v / d tau = 0

is a physical representation step and is not encoded in this module.
No coordinates, velocity, differentiability, or spacetime geometry are
assumed below.
-/

/-
Semantics of a physically meaningful change in propagation character.

`ChangesPropagationCharacter R₁ R₂` means that the passage from relational
realization R₁ to relational realization R₂ contains a physically meaningful
change in the coarse-grained propagation character of the structure being
tracked.

The exact microscopic content of "propagation character" is intentionally
left abstract.  The GR manuscript uses the notion before introducing a
metric or a coordinate velocity, so the formalization should not smuggle in
those later structures.

The only requirement imposed here is that the binary change relation itself
is physically meaningful in the sense already represented by A1.
-/
structure PropagationChangeSemantics (M : SBI) where

  ChangesPropagationCharacter :
    M.Org → M.Org → Prop

  physicallyMeaningful :
    M.PhysMeaningful ChangesPropagationCharacter

/-
A physically meaningful change in propagation character requires relational
support.

This is a direct specialization of the relational-support clause of A1.
If the propagation-character change relation holds between R₁ and R₂, A1
requires a relational witness connecting those realizations.

The theorem does not yet say that the witness is a force, field, or local
interaction.  It states only the exact conclusion supplied by A1:
physically meaningful change cannot be unsupported by relational structure.
-/
theorem propagationChange_requires_relationalSupport
    {M : SBI}
    (D : PropagationChangeSemantics M)
    {R₁ R₂ : M.Org}
    (hChange :
      D.ChangesPropagationCharacter R₁ R₂) :

    M.RelWitness R₁ R₂ := by

  exact
    M.A1_relational_support
      D.physicallyMeaningful
      hChange

/-
Contrapositive form of the preceding theorem.

If there is no relational witness capable of supporting a physically
meaningful propagation-character change between R₁ and R₂, then such a
change cannot occur in the physical description.

This is the formal core of the manuscript phrase "no admissible relational
source of change".  We retain the more precise term `RelWitness` here because
A1 itself establishes relational support, not yet a dynamical force law.
-/
theorem noRelationalSupport_noPropagationChange
    {M : SBI}
    (D : PropagationChangeSemantics M)
    {R₁ R₂ : M.Org}
    (hNoSupport :
      ¬ M.RelWitness R₁ R₂) :

    ¬ D.ChangesPropagationCharacter R₁ R₂ := by

  intro hChange

  exact
    hNoSupport
      (propagationChange_requires_relationalSupport
        D hChange)

/-
Unconstrained persistent continuation.

R₁ and R₂ represent two realizations of the same persistent identity, while
no relational witness exists for a physically meaningful change in its
propagation character.

The two clauses have distinct logical roles:

  * `M.Persist R₁ R₂` identifies the subject across the two realizations;
  * `¬ M.RelWitness R₁ R₂` expresses the absence of relational support for
    the relevant change.

Persistence does not require R₁ and R₂ to be relationally equivalent.  This
is essential: A3 explicitly permits one persistent identity to possess
relationally distinct realizations.
-/
def UnconstrainedPersistentContinuation
    (M : SBI)
    (R₁ R₂ : M.Org) : Prop :=

  M.Persist R₁ R₂
  ∧
  ¬ M.RelWitness R₁ R₂

/-
Persistence of propagation character under unconstrained continuation.

If R₁ and R₂ are realizations of the same persistent identity and no
relational support exists for a physically meaningful change in propagation
character, then

  * persistent identity is retained; and
  * propagation character does not change.

This theorem is intentionally stated without coordinates.  It captures the
structural content that will later be represented, in a sufficiently smooth
localized coarse-grained regime, by constant velocity.
-/
theorem unconstrainedPersistentContinuation_preservesPropagationCharacter
    {M : SBI}
    (D : PropagationChangeSemantics M)
    {R₁ R₂ : M.Org}
    (hUnconstrained :
      UnconstrainedPersistentContinuation M R₁ R₂) :

    M.Persist R₁ R₂
    ∧
    ¬ D.ChangesPropagationCharacter R₁ R₂ := by

  constructor

  · exact hUnconstrained.1

  · exact
      noRelationalSupport_noPropagationChange
        D hUnconstrained.2

/-
Manuscript-facing structural form of Newton's first law.

At the pre-geometric level, the content of Newton I is not yet the equation

    d v / d tau = 0.

It is the statement that one and the same persistent structure retains its
propagation character when no relationally supported cause of change is
present.

This definition packages exactly those two conditions and no more.
-/
def NewtonFirstLawStructural
    {M : SBI}
    (D : PropagationChangeSemantics M)
    (R₁ R₂ : M.Org) : Prop :=

  M.Persist R₁ R₂
  ∧
  ¬ D.ChangesPropagationCharacter R₁ R₂

/-
Unconstrained persistent continuation implies the structural Newton-I
condition.

The proof makes the dependency split explicit:

  * persistence is carried by A3's persistence relation;
  * exclusion of unexplained propagation change is supplied by A1;
  * A2 is not needed until one asks how a physically present source of
    change is mediated.

This is useful for the manuscript dependency audit because it shows that
Newton I's "no change without a source" content is already fixed before the
local structure of the source is analyzed.
-/
theorem unconstrainedPersistentContinuation_implies_NewtonFirstLawStructural
    {M : SBI}
    (D : PropagationChangeSemantics M)
    {R₁ R₂ : M.Org}
    (hUnconstrained :
      UnconstrainedPersistentContinuation M R₁ R₂) :

    NewtonFirstLawStructural D R₁ R₂ := by

  exact
    unconstrainedPersistentContinuation_preservesPropagationCharacter
      D hUnconstrained

end GR
end SBI
