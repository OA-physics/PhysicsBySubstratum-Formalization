import SBILeanProject.GR.LorentzClassification

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Manuscript-facing synthesis of the Section 2 kinematics.

The preceding modules deliberately keep four logically distinct ingredients
separate:

  * persistent propagation without a relationally supported change
    (the pre-geometric content of Newton I);
  * finite causal propagation once relational depth is calibrated by the
    reversible duration construction from the Time paper;
  * operational inertial equivalence and preservation of causal structure;
  * the externally imported Lorentz classification.

For the manuscript architecture these ingredients are not four independent
endpoints.  Together they constitute the effective kinematical regime that is
carried into the later spacetime-geometric argument.

This file therefore introduces one explicit result object collecting those
conclusions.  No new physical assumption is added here: every field is proved
by a theorem from the preceding modules.
-/

/--
The checked output of the pre-geometric spacetime-kinematics argument.

The fields are intentionally heterogeneous.  They record the distinct claims
that have to coexist before the manuscript passes to an effective Lorentzian
spacetime description:

  * structural Newton I for one persistent continuation;
  * absence of an absolute inertial marker;
  * a finite relational-depth / duration rate bound;
  * causal invariance under the same operational inertial equivalence;
  * Lorentz classification of the selected inertial transformation.

The object is a conclusion bundle, not an additional axiom.
-/
structure SpacetimeKinematicsResult
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : Time.OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (PChange : PropagationChangeSemantics M)
    (R₁ R₂ : M.Org)
    (p : CausalPropagationProcess D A O X Y)
    (delta : Time.LocalDurationScale)
    (I : InertialEquivalenceSemantics M)
    (Caus : CausalAccessibilitySemantics M)
    (Rdesc : OperationalInertialRedescription I)
    (L : StandardLorentzClassification)
    (T : L.InertialTransformation) where

  newtonFirstLaw :
    NewtonFirstLawStructural PChange R₁ R₂

  noAbsoluteInertialMarker :
    NoAbsoluteInertialMarker I

  finiteCausalRate :
    HasFiniteRelationalDepthRateBound p delta

  preLorentzSymmetry :
    PreLorentzInertialSymmetry
      Caus
      Rdesc.toInertialRedescription

  lorentz :
    L.IsLorentz T

/-
Section-2 spacetime-kinematics characterization.

Each component comes from an already established result:

  * unconstrained persistence -> structural Newton I;
  * operational inertial equivalence -> no absolute inertial marker;
  * calibrated causal propagation -> finite depth-rate bound;
  * operational inertial redescription -> causal symmetry;
  * the explicit standard classification interface -> Lorentz.

The theorem is deliberately placed before the effective-geometric module so
that the later Lorentzian-geometry bridge can depend on the complete checked
kinematical result rather than bypassing it and using the Lorentz theorem in
isolation.
-/
theorem spacetimeKinematics_characterization
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : Time.OperationalAccessibilitySemantics D}
    {O : Observer M}
    {X Y : Configuration K O}
    (PChange : PropagationChangeSemantics M)
    (R₁ R₂ : M.Org)
    (hUnconstrained :
      UnconstrainedPersistentContinuation M R₁ R₂)
    (p : CausalPropagationProcess D A O X Y)
    (delta : Time.LocalDurationScale)
    (I : InertialEquivalenceSemantics M)
    (Caus : CausalAccessibilitySemantics M)
    (Rdesc : OperationalInertialRedescription I)
    (L : StandardLorentzClassification)
    (H : LorentzClassificationInput L)
    (T : L.InertialTransformation)
    (hT : L.AdmissibleInertial T) :

    SpacetimeKinematicsResult
      PChange R₁ R₂ p delta I Caus Rdesc L T := by

  exact
    { newtonFirstLaw :=
        unconstrainedPersistentContinuation_implies_NewtonFirstLawStructural
          PChange hUnconstrained
      noAbsoluteInertialMarker :=
        inertialEquivalence_excludes_absoluteMarker I
      finiteCausalRate :=
        CausalPropagationProcess.hasFiniteRelationalDepthRateBound
          p delta
      preLorentzSymmetry :=
        operationalInertialRedescription_has_preLorentzSymmetry
          I Caus Rdesc
      lorentz :=
        lorentz_of_standardClassification L H T hT }

end GR
end SBI
