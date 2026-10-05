import SBILeanProject.GR.InertialSymmetry
import SBILeanProject.GR.CausalPropagation

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Explicit interface to the standard Lorentz-classification theorem.

The preceding GR modules establish the ingredients that belong to the
present axiomatic programme:

  * inertial descriptions related only by relationally redundant
    redescription preserve physically meaningful observables and causal
    accessibility;
  * causal propagation has a finite operational depth-per-duration bound
    once the explicit bridge to the Time duration construction is supplied.

The remaining step from those ingredients, together with the usual
homogeneity, isotropy and relativity assumptions of inertial kinematics, to
Lorentz transformations is standard external mathematics.  It is not a new
consequence proved from A1--A3 inside this repository.

This file therefore does not attempt to re-prove that classification.
Instead it represents it as an explicit imported interface.  Doing so keeps
the formal dependency graph honest: the Lean development can show exactly
where the external theorem is used rather than allowing it to disappear
inside prose.
-/

/-
Abstract statement of the external inertial-kinematics classification.

`InertialTransformation` is intentionally left abstract.  A future, more
mathematical formalization could instantiate it with affine transformations
of a real spacetime vector space and prove the classification from the
standard hypotheses.  That is not needed for the logical audit performed
here.

The four propositions record the assumptions entering the standard result:

  * homogeneity of the inertial regime;
  * isotropy;
  * the relativity principle;
  * existence of a finite invariant causal speed.

`AdmissibleInertial` marks the transformations belonging to the inertial
class being classified, and `IsLorentz` records the conclusion.

The field `classify` is therefore explicitly imported mathematics, not a
field derived from SBI axioms.
-/
structure StandardLorentzClassification where

  InertialTransformation : Type

  HomogeneousRegime : Prop

  IsotropicRegime : Prop

  RelativityPrinciple : Prop

  FiniteInvariantCausalSpeed : Prop

  AdmissibleInertial :
    InertialTransformation → Prop

  IsLorentz :
    InertialTransformation → Prop

  classify :
    HomogeneousRegime →
    IsotropicRegime →
    RelativityPrinciple →
    FiniteInvariantCausalSpeed →
    ∀ T : InertialTransformation,
      AdmissibleInertial T →
      IsLorentz T

/-
The assumptions actually supplied to one use of the external
classification theorem.

This bundle is separate from `StandardLorentzClassification` because the
classification theorem states an implication, whereas the GR manuscript
must establish or explicitly assume that its coarse-grained regime satisfies
the theorem's hypotheses.

In particular, `finiteInvariantCausalSpeed` is deliberately stronger than
the single-process finite depth-rate result in CausalPropagation.lean.
The latter establishes finiteness after duration calibration; invariance of
the resulting causal boundary across inertial descriptions also requires the
symmetry input formalized in InertialSymmetry.lean and the homogeneous
coarse-grained identification used in the manuscript.
-/
structure LorentzClassificationInput
    (L : StandardLorentzClassification) where

  homogeneous :
    L.HomogeneousRegime

  isotropic :
    L.IsotropicRegime

  relativity :
    L.RelativityPrinciple

  finiteInvariantCausalSpeed :
    L.FiniteInvariantCausalSpeed

/-
Application of the explicitly imported Lorentz-classification theorem.

No physics is hidden in this proof: Lean merely verifies that once all four
classification hypotheses are supplied, and T belongs to the admissible
inertial class, the imported theorem yields the Lorentz conclusion.

This is exactly the desired formal separation between

  1. results derived within the SBI/Time/GR development, and
  2. standard external mathematics invoked at the final classification
     step.
-/
theorem lorentz_of_standardClassification
    (L : StandardLorentzClassification)
    (H : LorentzClassificationInput L)
    (T : L.InertialTransformation)
    (hT : L.AdmissibleInertial T) :

    L.IsLorentz T := by

  exact
    L.classify
      H.homogeneous
      H.isotropic
      H.relativity
      H.finiteInvariantCausalSpeed
      T
      hT

end GR
end SBI
