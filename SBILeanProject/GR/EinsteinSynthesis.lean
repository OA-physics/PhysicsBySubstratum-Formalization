import SBILeanProject.GR.LovelockClassification
import SBILeanProject.GR.GeometricRepresentation
import SBILeanProject.GR.MetricClosure
import SBILeanProject.GR.StressEnergyBridge

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Final Einstein-form synthesis.

This module separates three logically different stages that were previously
compressed into one bridge:

  1. the GR construction supplies physical/effective structural premises
     relevant to a Lovelock-type classification;
  2. those physical premises are identified with the formal predicates used
     by the imported standard Lovelock theorem;
  3. the classified geometric tensor is coupled to the admissible effective
     source tensor.

Keeping these stages separate prevents the dependency graph from visually
suggesting that the external Lovelock theorem somehow establishes its own
physical premises.

The empirical value kappa = 8 pi G / c^4 remains outside the structural
argument.
-/

/-
Physical/effective bridge defining the GR-side structural conditions that
will later be identified with the hypotheses of the external Lovelock
classification.

These propositions are intentionally independent of
`StandardLovelockClassification`.  They belong to the selected effective GR
regime, not to the external mathematical theorem.
-/
structure EffectiveLovelockRegimeBridge
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    (S : MetricClosureSemantics) where

  FourDimensionalRegime : Prop
  LocalMetricConstruction : Prop
  DiffeomorphismCovariantField : Prop
  SymmetricGeometricField : Prop
  DivergenceFreeGeometricField : Prop
  AtMostSecondOrderField : Prop

  fourDimensional :
    FourDimensionalRegime

  localMetricConstruction :
    LocalMetricConstruction

  geometricRepresentation_to_covariance :
    G.HasEffectiveDifferentiableManifold →
    G.HasLorentzianCausalStructure →
    DiffeomorphismCovariantField

  symmetric :
    SymmetricGeometricField

  divergenceFree :
    DivergenceFreeGeometricField

  closedMetric_to_atMostSecondOrder :
    (¬ S.IrreduciblyHigherOrder) →
    AtMostSecondOrderField

/-
Established GR-side Lovelock premises in one selected closed effective regime.

This record is the physical conclusion before the imported Lovelock theorem
is mentioned.  It says only that the chosen regime satisfies the structural
properties which will subsequently be identified with the theorem's formal
hypotheses.
-/
structure EffectiveLovelockPremises
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    (S : MetricClosureSemantics)
    (R : EffectiveLovelockRegimeBridge G S) where

  fourDimensional :
    R.FourDimensionalRegime

  localMetricConstruction :
    R.LocalMetricConstruction

  diffeomorphismCovariant :
    R.DiffeomorphismCovariantField

  symmetric :
    R.SymmetricGeometricField

  divergenceFree :
    R.DivergenceFreeGeometricField

  atMostSecondOrder :
    R.AtMostSecondOrderField

/-
The effective geometry plus closed metric state establish the GR-side
structural premises needed before the external Lovelock classification is
applied.
-/
theorem effectiveLovelockPremises_of_closedEffectiveRegime
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    (hLorentzian : G.HasLorentzianCausalStructure)
    (S : MetricClosureSemantics)
    (hClosed : ClosedLocalMetricState S)
    (R : EffectiveLovelockRegimeBridge G S) :

    EffectiveLovelockPremises G S R := by

  have hNoHigher :
      ¬ S.IrreduciblyHigherOrder :=
    closedMetricState_excludes_irreducibleHigherOrder
      S hClosed

  exact
    { fourDimensional :=
        R.fourDimensional
      localMetricConstruction :=
        R.localMetricConstruction
      diffeomorphismCovariant :=
        R.geometricRepresentation_to_covariance
          G.hasEffectiveDifferentiableManifold
          hLorentzian
      symmetric :=
        R.symmetric
      divergenceFree :=
        R.divergenceFree
      atMostSecondOrder :=
        R.closedMetric_to_atMostSecondOrder hNoHigher }

/-
Identification bridge between the GR-side structural predicates and the
formal predicates occurring in one selected external Lovelock classification.

This is deliberately distinct from both the physical premise theorem above
and the imported Lovelock theorem itself.
-/
structure LovelockRegimeBridge
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    (S : MetricClosureSemantics)
    (R : EffectiveLovelockRegimeBridge G S)
    (L : StandardLovelockClassification)
    (H : L.GeometricTensor) where

  identifyFourDimensional :
    R.FourDimensionalRegime →
    L.FourDimensional

  identifyLocalMetricConstruction :
    R.LocalMetricConstruction →
    L.LocalMetricConstruction H

  identifyCovariance :
    R.DiffeomorphismCovariantField →
    L.DiffeomorphismCovariant H

  identifySymmetry :
    R.SymmetricGeometricField →
    L.Symmetric H

  identifyDivergenceFree :
    R.DivergenceFreeGeometricField →
    L.DivergenceFree H

  identifySecondOrder :
    R.AtMostSecondOrderField →
    L.AtMostSecondOrder H

/-
Translate the already established GR-side premises into the input record
required by the external Lovelock theorem.
-/
theorem lovelockInput_of_effectivePremises
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    (S : MetricClosureSemantics)
    (R : EffectiveLovelockRegimeBridge G S)
    (E : EffectiveLovelockPremises G S R)
    (L : StandardLovelockClassification)
    (H : L.GeometricTensor)
    (I : LovelockRegimeBridge G S R L H) :

    LovelockClassificationInput L H := by

  exact
    { fourDimensional :=
        I.identifyFourDimensional E.fourDimensional
      localMetricConstruction :=
        I.identifyLocalMetricConstruction E.localMetricConstruction
      diffeomorphismCovariant :=
        I.identifyCovariance E.diffeomorphismCovariant
      symmetric :=
        I.identifySymmetry E.symmetric
      divergenceFree :=
        I.identifyDivergenceFree E.divergenceFree
      atMostSecondOrder :=
        I.identifySecondOrder E.atMostSecondOrder }

/-
Explicit bridge from classified geometry and an admissible effective source
to the Einstein-form field equation.

`kappa` is intentionally supplied as part of the effective coupling rather
than derived.
-/
structure EffectiveEinsteinCoupling
    (L : StandardLovelockClassification)
    (B : CoarseGrainedLocalBalance)
    (P : PreservedQuantityBridge B)
    (T : EffectiveSourceTensorBridge B P) where

  kappa : Real

  EinsteinFormEquation :
    L.GeometricTensor →
    T.SourceTensor →
    Real →
    Prop

  classifiedGeometry_couplesToAdmissibleSource :
    ∀ {H : L.GeometricTensor}
      {source : T.SourceTensor},
      L.EinsteinPlusCosmological H →
      T.IsTensorial source →
      T.IsSymmetric source →
      T.IsCovariantlyConserved source →
      EinsteinFormEquation H source kappa

/-
Final manuscript-facing synthesis theorem.

The proof order is now explicit:

  effective geometry + metric closure
    -> GR-side Lovelock premises
    -> identification with external Lovelock predicates
    -> imported Lovelock classification
    -> coupling to the admissible effective source.
-/
theorem admissibleCoarseGrainedGeometry_has_EinsteinForm
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    (hLorentzian : G.HasLorentzianCausalStructure)
    (S : MetricClosureSemantics)
    (hClosed : ClosedLocalMetricState S)
    (R₀ : EffectiveLovelockRegimeBridge G S)
    (L : StandardLovelockClassification)
    (H : L.GeometricTensor)
    (R : LovelockRegimeBridge G S R₀ L H)
    (B : CoarseGrainedLocalBalance)
    (P : PreservedQuantityBridge B)
    (T : EffectiveSourceTensorBridge B P)
    (C : EffectiveEinsteinCoupling L B P T)
    (q : B.Quantity)
    (hPreserved : P.IsPreserved q) :

    C.EinsteinFormEquation
      H
      (T.sourceTensor q)
      C.kappa := by

  have hPremises :
      EffectiveLovelockPremises G S R₀ :=
    effectiveLovelockPremises_of_closedEffectiveRegime
      G hLorentzian S hClosed R₀

  have hInput :
      LovelockClassificationInput L H :=
    lovelockInput_of_effectivePremises
      G S R₀ hPremises L H R

  have hGeometry :
      L.EinsteinPlusCosmological H :=
    einsteinPlusCosmological_of_standardLovelock
      L H hInput

  have hSource :
      HasAdmissibleEffectiveSource B P T q :=
    preservedQuantity_has_admissibleEffectiveSource
      B P T q hPreserved

  exact
    C.classifiedGeometry_couplesToAdmissibleSource
      hGeometry
      hSource.1
      hSource.2.1
      hSource.2.2

end GR
end SBI
