import SBILeanProject.GR.LorentzClassification

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Coarse-grained geometric representation and coordinate equivalence.

This module formalizes the beginning of the manuscript section
"Manifold Structure and General Relativity".

Three logically different steps are kept separate.

1. Smooth coarse-grained representation.

   In a regime where the relational organization varies smoothly and admits
   compatible overlapping local descriptions, it may be represented by an
   effective differentiable manifold.  This is a physical coarse-graining
   bridge, not a theorem of A1--A3 alone.

2. Lorentzian character of the effective causal geometry.

   The preceding kinematical analysis establishes a Lorentz result for the
   selected inertial regime.  Passing from that local causal/inertial result,
   together with smooth manifold representability, to a Lorentzian causal
   structure on the effective manifold is an explicit physical
   representation bridge.

   Importantly, this step does not depend on every other Section-2 conclusion.
   In particular, structural Newton I is a parallel kinematical result rather
   than a premise of the Lorentzian-manifold construction.

3. Coordinate equivalence.

   Once two smooth coordinate descriptions are identified as descriptions of
   the same relational physical state, A1 implies that no physically
   meaningful descriptor can distinguish them.

No differential geometry library is introduced here.  The purpose of this
Lean layer is to expose the logical interfaces between the relational,
kinematical and effective-geometric parts of the manuscript.
-/

/-
An abstract coarse-grained geometric representation.

`Description` is the type of effective local geometric descriptions used in
some coarse-grained regime.  `relationalState` associates each such
representation with the relational physical state that it describes.

`SmoothlyEquivalent d₁ d₂` means that the two descriptions differ only by an
admissible smooth change of coordinates.  The bridge
`smoothlyEquivalent_relEq` identifies that redundancy with relational
equivalence of the represented physical states.

The manifold condition is stated and supplied here because smooth manifold
representability is the coarse-graining assumption made at the start of this
section.

By contrast, `HasLorentzianCausalStructure` is only the proposition naming the
Lorentzian character of the effective causal geometry.  Evidence for that
proposition is deliberately NOT a field of this structure.  It is obtained
below from the checked Lorentz result through `LorentzianGeometryBridge`.
-/
structure EffectiveGeometricRepresentation (M : SBI) where

  Description : Type

  relationalState :
    Description → M.Org

  SmoothlyEquivalent :
    Description → Description → Prop

  smoothlyEquivalent_relEq :
    ∀ {d₁ d₂ : Description},
      SmoothlyEquivalent d₁ d₂ →
      M.RelEq (relationalState d₁) (relationalState d₂)

  HasEffectiveDifferentiableManifold : Prop

  hasEffectiveDifferentiableManifold :
    HasEffectiveDifferentiableManifold

  HasLorentzianCausalStructure : Prop

/-
Bridge from a local Lorentz result to Lorentzian effective geometry.

A curved Lorentzian manifold is a local geometric representation of a
smoothly varying regime.  Identifying the Lorentz classification of the
selected inertial transformation with the causal character of that smooth
representation is therefore not merely a logical rewrite.

No field equation, curvature law or Lovelock assumption enters here.
-/
structure LorentzianGeometryBridge
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    (L : StandardLorentzClassification)
    (T : L.InertialTransformation) where

  lorentz_to_lorentzian :
    L.IsLorentz T →
    G.HasEffectiveDifferentiableManifold →
    G.HasLorentzianCausalStructure

/-
Lower-level form: the selected smooth effective geometry is Lorentzian once
one Lorentz transformation result and the local-geometry bridge are supplied.
-/
theorem lorentzianCausalStructure_of_lorentzResult
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    (L : StandardLorentzClassification)
    (T : L.InertialTransformation)
    (hLorentz : L.IsLorentz T)
    (B : LorentzianGeometryBridge G L T) :

    G.HasLorentzianCausalStructure := by

  exact
    B.lorentz_to_lorentzian
      hLorentz
      G.hasEffectiveDifferentiableManifold

/-
Manuscript-facing connection from the standard Lorentz classification to the
smooth effective geometry.

This theorem deliberately uses only the Lorentz-classification result needed
for the Section-3 geometric step.  The broader Section-2 synthesis also
contains structural Newton I and the finite-rate statement, but those are not
premises of the manifold representation itself.
-/
theorem lorentzianCausalStructure_of_standardClassification
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    (L : StandardLorentzClassification)
    (H : LorentzClassificationInput L)
    (T : L.InertialTransformation)
    (hT : L.AdmissibleInertial T)
    (B : LorentzianGeometryBridge G L T) :

    G.HasLorentzianCausalStructure := by

  have hLorentz :
      L.IsLorentz T :=
    lorentz_of_standardClassification L H T hT

  exact
    lorentzianCausalStructure_of_lorentzResult
      G L T hLorentz B

/-
A physically meaningful relational descriptor lifted to the effective
geometric description.
-/
def EffectiveGeometricRepresentation.liftDescriptor
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    {α : Type}
    (F : M.Org → α) :
    G.Description → α :=

  fun d => F (G.relationalState d)

/-
Coordinate-equivalent descriptions cannot be distinguished by a physically
meaningful relational descriptor.
-/
theorem coordinateEquivalent_descriptors_agree
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    {α : Type}
    (F : M.Org → α)
    (hPhys : M.PhysMeaningful F)
    {d₁ d₂ : G.Description}
    (hCoord : G.SmoothlyEquivalent d₁ d₂) :

    G.liftDescriptor F d₁ =
      G.liftDescriptor F d₂ := by

  exact
    M.A1_invariance
      hPhys
      (G.smoothlyEquivalent_relEq hCoord)

/-
Predicate form of coordinate invariance.
-/
def EffectiveGeometricRepresentation.CoordinateInvariant
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    {α : Type}
    (f : G.Description → α) : Prop :=

  ∀ {d₁ d₂ : G.Description},
    G.SmoothlyEquivalent d₁ d₂ →
    f d₁ = f d₂

/-
Every physically meaningful relational descriptor becomes coordinate
invariant when evaluated through the effective geometric representation.
-/
theorem physicallyMeaningful_descriptor_is_coordinateInvariant
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    {α : Type}
    (F : M.Org → α)
    (hPhys : M.PhysMeaningful F) :

    G.CoordinateInvariant (G.liftDescriptor F) := by

  intro d₁ d₂ hCoord

  exact
    coordinateEquivalent_descriptors_agree
      G F hPhys hCoord

/-
Manuscript-facing bundle for the effective geometric regime.

The first component is the explicit smooth-manifold coarse-graining bridge.
The second follows from the Lorentz classification through
`LorentzianGeometryBridge`.  The third is the A1-derived coordinate-invariance
result.
-/
theorem effectiveGeometry_bridge_and_coordinateInvariance
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    (L : StandardLorentzClassification)
    (H : LorentzClassificationInput L)
    (T : L.InertialTransformation)
    (hT : L.AdmissibleInertial T)
    (B : LorentzianGeometryBridge G L T)
    {α : Type}
    (F : M.Org → α)
    (hPhys : M.PhysMeaningful F) :

    G.HasEffectiveDifferentiableManifold
    ∧ G.HasLorentzianCausalStructure
    ∧ G.CoordinateInvariant (G.liftDescriptor F) := by

  exact
    ⟨ G.hasEffectiveDifferentiableManifold,
      lorentzianCausalStructure_of_standardClassification
        G L H T hT B,
      physicallyMeaningful_descriptor_is_coordinateInvariant
        G F hPhys ⟩

end GR
end SBI
