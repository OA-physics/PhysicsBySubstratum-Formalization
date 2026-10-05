import SBILeanProject.SBI.Deformation

set_option autoImplicit false

namespace SBI

/-
Structural characterization of a persistent relational defect.

This theorem is deliberately stated in the same three-part form as the
manuscript theorem rather than returning an intermediate packaging structure.

For a persistent relational defect associated with identity [R]ₚ at X:

  1. operational re-identification from X has finite operational/network
     support;

  2. the identifying property Q is invariant under every
     persistence-preserving admissible deformation from X;

  3. the identifying property-value q cannot be eliminated by any
     context-preserving local deformation within Ω.

Finite Operational Accessibility is not taken here as an additional theorem
hypothesis.  It is derived from A2 together with operational accessibility by
`finite_operational_accessibility` and used internally for the finite-support
clause.

Thus the public Lean theorem mirrors the three conclusions of the manuscript
directly.  No intermediate `PersistentDefectCharacterization` object is part of
the conceptual proof.
-/
theorem persistentRelationalDefect_characterization
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (L : LocalDeformationSemantics D)
    (P : PersistenceContext K)
    (O : Observer M)
    (R : M.Org)
    (Ω : Domain M)
    {α : Type}
    (Q : Configuration K O → α)
    (q : α)
    (X : Configuration K O)
    (hDefect :
      PersistentRelationalDefect
        D L P O R Ω Q q X) :

    (∃ Y : Configuration K O,
      ∃ S : OperationalSupport P O X Y R,
        ∃ Efin : List (DirectRelation C O),

          (∀ a : M.Interaction,
            a ∈ S.interactions →
            InteractionConjunction C O a
              ∈ supportConjunctions S)

          ∧

          (∀ e : DirectRelation C O,
            IsSupportDirectRelation S e →
            e ∈ Efin))

    ∧

    (∀ {Y : Configuration K O},
      PersistencePreservingDeformation
        D P O R X Y →
      Q X = Q Y)

    ∧

    (∀ {Y : Configuration K O},
      ContextPreservingLocalDeformation
        D L O Ω X Y →
      Q Y = q) := by

  /-
  FOA is a derived proposition, not an additional physical input to this
  theorem.  It is reconstructed here from the operational accessibility
  semantics and A2 finite operational resolution.
  -/
  have hFOA : FOA C.toNetworkContext :=
    finite_operational_accessibility C.toNetworkContext

  constructor

  · exact
      persistentRelationalDefect_has_finiteOperationalSupport
        D L P hFOA O R Ω Q q X hDefect

  constructor

  · intro Y hPreserving

    exact
      persistentRelationalDefect_identifyingProperty_invariant
        D L P O R Ω Q q X
        hDefect
        hPreserving

  · intro Y hLocal

    exact
      persistentRelationalDefect_is_locallyNonEliminable
        D L P O R Ω Q q X
        hDefect
        hLocal

end SBI
