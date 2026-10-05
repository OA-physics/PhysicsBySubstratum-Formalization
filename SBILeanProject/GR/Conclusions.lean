import SBILeanProject.GR.EinsteinSynthesis
import SBILeanProject.GR.KinematicsSynthesis
import SBILeanProject.GR.ReachabilityBoundary

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Manuscript-facing conclusion bundles.

The Section-2 spacetime-kinematics conclusion lives in
`KinematicsSynthesis.lean`.  It summarizes the kinematical results, including
structural Newton I, but the later manifold construction depends only on the
Lorentz causal/inertial result actually used there.

This file retains the later manuscript-facing destinations:

  * constraint strengthening and limiting reachability;
  * the final effective-GR characterization.

No new physical assumptions are introduced here.
-/

/-
Constraint-loading conclusion bundle.
-/
theorem constraintStrengthening_characterization
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

    NoGreaterReachabilityDomain R Γ₂ Γ₁ X
    ∧ TerminalUnderConstraints R Γ₂ X := by

  exact
    ⟨ includedRequirements_noGreaterReachabilityDomain
        S O v R Γ₁ Γ₂ hIncluded X,
      terminal_preserved_by_constraintStrengthening
        S O v R Γ₁ Γ₂ hIncluded X hTerminal₁ ⟩

/-
Limiting-reachability conclusion bundle.
-/
theorem limitingReachability_characterization
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
    (hLimiting : LimitingReachabilityConfiguration S O v R Γ X) :

    CompatibleConfiguration S O v Γ X
    ∧ ∀ Y : LocalConfigurationSpace K O v,
        Y ≠ X →
        ¬ ConstrainedReachability R Γ X Y := by

  constructor

  · exact hLimiting.1

  · intro Y hDistinct

    exact
      limitingConfiguration_no_distinct_continuation
        S O v R Γ X hLimiting hDistinct

/-
Effective-GR conclusion bundle.

The manifold branch uses the precise Section-2 result needed by the
manuscript: the Lorentz classification of the selected inertial regime.
Structural Newton I remains part of the Section-2 kinematics summary but is
not treated as a premise of the Lorentzian-manifold construction.

The later synthesis is likewise staged explicitly:

    Lorentz result + smooth effective representation
      -> Lorentzian effective geometry,

    effective geometry + closed metric state
      -> GR-side structural Lovelock premises,

    identification bridge + imported Lovelock theorem
      -> Einstein-plus-cosmological geometric form,

    admissible effective source + coupling bridge
      -> Einstein-form field equation.

The empirical numerical value of kappa remains outside the structural theorem.
-/
theorem effectiveGR_characterization
    {M : SBI}
    (G : EffectiveGeometricRepresentation M)
    (LKin : StandardLorentzClassification)
    (HKin : LorentzClassificationInput LKin)
    (TKin : LKin.InertialTransformation)
    (hTKin : LKin.AdmissibleInertial TKin)
    (BGeom : LorentzianGeometryBridge G LKin TKin)
    {α : Type}
    (F : M.Org → α)
    (hPhys : M.PhysMeaningful F)
    (S : MetricClosureSemantics)
    (hClosed : ClosedLocalMetricState S)
    (R₀ : EffectiveLovelockRegimeBridge G S)
    (LL : StandardLovelockClassification)
    (H : LL.GeometricTensor)
    (R : LovelockRegimeBridge G S R₀ LL H)
    (B : CoarseGrainedLocalBalance)
    (P : PreservedQuantityBridge B)
    (T : EffectiveSourceTensorBridge B P)
    (Cpl : EffectiveEinsteinCoupling LL B P T)
    (q : B.Quantity)
    (hPreserved : P.IsPreserved q) :

    G.HasLorentzianCausalStructure
    ∧ G.CoordinateInvariant (G.liftDescriptor F)
    ∧ (¬ S.IrreduciblyHigherOrder)
    ∧ HasAdmissibleEffectiveSource B P T q
    ∧ Cpl.EinsteinFormEquation
        H
        (T.sourceTensor q)
        Cpl.kappa := by

  have hLorentzian :
      G.HasLorentzianCausalStructure :=
    lorentzianCausalStructure_of_standardClassification
      G LKin HKin TKin hTKin BGeom

  have hCoordinateInvariant :
      G.CoordinateInvariant (G.liftDescriptor F) :=
    physicallyMeaningful_descriptor_is_coordinateInvariant
      G F hPhys

  have hNoHigher :
      ¬ S.IrreduciblyHigherOrder :=
    closedMetricState_excludes_irreducibleHigherOrder
      S hClosed

  have hSource :
      HasAdmissibleEffectiveSource B P T q :=
    preservedQuantity_has_admissibleEffectiveSource
      B P T q hPreserved

  have hEinstein :
      Cpl.EinsteinFormEquation
        H
        (T.sourceTensor q)
        Cpl.kappa :=
    admissibleCoarseGrainedGeometry_has_EinsteinForm
      G hLorentzian S hClosed R₀ LL H R B P T Cpl q hPreserved

  exact
    ⟨ hLorentzian,
      hCoordinateInvariant,
      hNoHigher,
      hSource,
      hEinstein ⟩

end GR
end SBI
