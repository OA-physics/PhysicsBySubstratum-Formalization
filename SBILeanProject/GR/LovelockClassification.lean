import SBILeanProject.GR.StressEnergyBridge
import SBILeanProject.GR.MetricClosure

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Explicit interface to the four-dimensional Lovelock classification.

The GR manuscript reaches the Einstein form only after several ingredients
have been separated and audited:

  * an effective Lorentzian metric description exists in the selected
    coarse-grained regime;
  * coordinate redundancy is physical redundancy rather than additional
    structure;
  * a closed metric-only description excludes irreducible derivatives above
    second order;
  * the effective source is represented tensorially and is locally conserved.

The remaining statement that, in four dimensions, a local symmetric
covariantly conserved rank-two tensor constructed from the metric through
second derivatives is restricted to Einstein-tensor plus metric form is
standard external mathematics: the Lovelock classification.

This file does NOT re-prove Lovelock's theorem.  As with the Lorentz
classification module, it introduces an explicit theorem interface so the
dependency graph cannot silently turn imported mathematics into a consequence
of A1--A3.
-/

/-
Abstract statement of the external Lovelock classification.

`GeometricTensor` denotes the candidate geometric left-hand side of the
effective field equation.  We deliberately avoid implementing tensor
calculus here; the present goal is logical dependency auditing.

The predicates expose the hypotheses used in the manuscript:

  * `FourDimensional` — the effective manifold is four-dimensional;
  * `LocalMetricConstruction H` — H is constructed locally from the metric;
  * `DiffeomorphismCovariant H` — H is a geometric/covariant rank-two object;
  * `Symmetric H` — H is symmetric;
  * `DivergenceFree H` — H is covariantly divergence-free;
  * `AtMostSecondOrder H` — metric derivatives enter irreducibly through at
    most second order.

`EinsteinPlusCosmological H` is the classification conclusion: H belongs to
the two-term Einstein-plus-metric family, corresponding schematically to

    G_{mu nu} + Lambda g_{mu nu}.

The field `classify` is imported standard mathematics, not a derivation from
the substratum axioms.
-/
structure StandardLovelockClassification where

  GeometricTensor : Type

  FourDimensional : Prop

  LocalMetricConstruction :
    GeometricTensor → Prop

  DiffeomorphismCovariant :
    GeometricTensor → Prop

  Symmetric :
    GeometricTensor → Prop

  DivergenceFree :
    GeometricTensor → Prop

  AtMostSecondOrder :
    GeometricTensor → Prop

  EinsteinPlusCosmological :
    GeometricTensor → Prop

  classify :
    FourDimensional →
    ∀ H : GeometricTensor,
      LocalMetricConstruction H →
      DiffeomorphismCovariant H →
      Symmetric H →
      DivergenceFree H →
      AtMostSecondOrder H →
      EinsteinPlusCosmological H

/-
The hypotheses supplied when the external classification is applied to one
selected effective geometric tensor.

Keeping these assumptions in a separate bundle is useful because several of
them have different logical origins in the manuscript.  For example,
second-order closure is argued from the closed-state condition, whereas
four-dimensionality and the continuum tensor representation belong to the
chosen effective regime.
-/
structure LovelockClassificationInput
    (L : StandardLovelockClassification)
    (H : L.GeometricTensor) where

  fourDimensional :
    L.FourDimensional

  localMetricConstruction :
    L.LocalMetricConstruction H

  diffeomorphismCovariant :
    L.DiffeomorphismCovariant H

  symmetric :
    L.Symmetric H

  divergenceFree :
    L.DivergenceFree H

  atMostSecondOrder :
    L.AtMostSecondOrder H

/-
Application of the explicitly imported Lovelock theorem.

Once all of the classification hypotheses have been supplied for the
selected geometric tensor H, the external theorem places H in the
Einstein-plus-cosmological family.

No additional physical assumption is introduced by this proof; Lean merely
checks that the complete hypothesis bundle is passed to the imported
classification interface.
-/
theorem einsteinPlusCosmological_of_standardLovelock
    (L : StandardLovelockClassification)
    (H : L.GeometricTensor)
    (I : LovelockClassificationInput L H) :

    L.EinsteinPlusCosmological H := by

  exact
    L.classify
      I.fourDimensional
      H
      I.localMetricConstruction
      I.diffeomorphismCovariant
      I.symmetric
      I.divergenceFree
      I.atMostSecondOrder

end GR
end SBI
