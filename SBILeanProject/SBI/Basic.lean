set_option autoImplicit false

/-
Primitive formal vocabulary for the SBI framework.

This structure contains only the domains and relations needed before
the physical admissibility axioms are stated.

In particular:

* RelEq, PhysMeaningful, and RelWitness provide the vocabulary used
  to formulate A1.

* MediationStep and Sigma provide the vocabulary used to formulate A2.

* The persistence relation is intentionally NOT introduced here.
  It is introduced as part of A3 itself in Axioms.lean.

This separation is important: later formal use of persistence should
therefore depend on A3 rather than on pre-axiomatic vocabulary.
-/

structure SBIBase where

  /-
  Admissible relational organizations.

  Manuscript notation:
      ℛ
  -/
  Org : Type

  /-
  Elementary admissible interactions.

  Interaction itself is primitive.
  -/
  Interaction : Type

  /-
  Relational participations involved in interactions.
  -/
  Participation : Type

  /-
  Sigma a p means that relational participation p
  participates in elementary interaction a.

  Manuscript notation:
      p ∈ Σ(a)
  -/
  Sigma : Interaction → Participation → Prop

  /-
  MediationStep a b means that mediation passes directly
  between elementary interactions a and b.

  This is formal vocabulary used to state A2.
  It does not yet impose the A2 locality condition.
  -/
  MediationStep : Interaction → Interaction → Prop

  /-
  Relational equivalence.

  Manuscript notation:
      R₁ ≃rel R₂

  The relation is part of the formal vocabulary.
  Its equivalence properties and its physical significance are
  imposed in the axiomatic structure rather than here.
  -/
  RelEq : Org → Org → Prop

  /-
  Physically meaningful descriptors.

  A descriptor F may take values in any type α.

  PhysMeaningful F states that F represents a physically
  meaningful quantity, predicate, or relation.

  Examples include:
      Org → ℝ
      Org → Bool
      Org → Org → Prop

  The final example is represented by taking
      α = Org → Prop.
  -/
  PhysMeaningful :
    {α : Type} → (Org → α) → Prop

  /-
  RelWitness R₁ R₂ means that relational organization
  accessible through admissible interaction witnesses a
  physical relation involving both R₁ and R₂.

  This is formal vocabulary used by the relational-support
  clause of A1.

  It does not impose locality, finiteness, geometry, network
  structure, or persistence.
  -/
  RelWitness : Org → Org → Prop
