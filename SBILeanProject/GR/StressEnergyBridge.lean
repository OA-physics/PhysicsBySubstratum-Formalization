import SBILeanProject.GR.LocalConservation

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Bridge from local conservation to an effective source tensor.

The manuscript passes from the pre-tensor conservation statement

    change in a coarse-grained region
      =
    transport through its boundary

for preserved quantities to the familiar continuum statement that the
coarse-grained persistent content is represented by a symmetric source tensor
T_{mu nu} satisfying

    nabla^mu T_{mu nu} = 0.

That passage contains genuine continuum representation input.  The current
Lean development has not constructed a differentiable tensor calculus, nor
has it proved that an arbitrary integral-balance quantity possesses a
symmetric rank-two tensor representation.  This module therefore exposes the
passage as an explicit bridge rather than hiding it inside the GR conclusion.

The logical status is:

  * `LocalConservation.lean` proves source-free local conservation once the
    coarse-grained balance and preservation-to-source bridges are supplied;
  * this file records the additional effective-field representation in which
    the selected coarse-grained quantities are represented tensorially;
  * the implication from the already proved local conservation statement to
    covariant divergence-freedom is itself part of that continuum bridge.

No component formula for T_{mu nu}, covariant derivative, connection, or
metric variation is introduced here.  Those belong to the established
continuum mathematics used by the GR effective description.
-/

/-
Effective source-tensor representation of the conserved coarse-grained
content.

`SourceTensor` is deliberately abstract.  In the physical interpretation it
stands for the effective rank-two source tensor T_{mu nu}.

The three predicates keep separate properties that are often compressed in
ordinary GR prose:

  * `IsTensorial` — the object transforms as the appropriate geometric tensor;
  * `IsSymmetric` — the effective source is symmetric;
  * `IsCovariantlyConserved` — the continuum representation satisfies the
    divergence-free condition corresponding to nabla^mu T_{mu nu} = 0.

`sourceTensor_tensorial` and `sourceTensor_symmetric` are representation
assumptions of the effective metric theory.  They are not consequences of the
abstract integral balance law alone.

`localConservation_to_covariantConservation` is the continuum bridge from the
integral local-conservation statement formalized upstream to the differential
covariant statement used in the Einstein/Lovelock synthesis.
-/
structure EffectiveSourceTensorBridge
    (B : CoarseGrainedLocalBalance)
    (P : PreservedQuantityBridge B) where

  SourceTensor : Type

  sourceTensor :
    B.Quantity → SourceTensor

  IsTensorial :
    SourceTensor → Prop

  IsSymmetric :
    SourceTensor → Prop

  IsCovariantlyConserved :
    SourceTensor → Prop

  sourceTensor_tensorial :
    ∀ q : B.Quantity,
      IsTensorial (sourceTensor q)

  sourceTensor_symmetric :
    ∀ q : B.Quantity,
      IsSymmetric (sourceTensor q)

  localConservation_to_covariantConservation :
    ∀ {q : B.Quantity},
      LocallyConservedQuantity B q →
      IsCovariantlyConserved (sourceTensor q)

/-
A preserved coarse-grained quantity has a tensorial, symmetric and
covariantly conserved effective source representation.

Only the local-conservation premise is derived upstream.  The passage to the
three tensor properties uses the explicit effective source-tensor bridge
above.  The proof therefore displays the manuscript dependency without
pretending that tensor calculus has been derived from A1--A3.
-/
theorem preservedQuantity_has_effectiveConservedSource
    (B : CoarseGrainedLocalBalance)
    (P : PreservedQuantityBridge B)
    (T : EffectiveSourceTensorBridge B P)
    (q : B.Quantity)
    (hPreserved : P.IsPreserved q) :

    T.IsTensorial (T.sourceTensor q)
    ∧ T.IsSymmetric (T.sourceTensor q)
    ∧ T.IsCovariantlyConserved (T.sourceTensor q) := by

  have hLocal :
      LocallyConservedQuantity B q :=
    preservedQuantity_is_locallyConserved
      B P q hPreserved

  exact
    ⟨ T.sourceTensor_tensorial q,
      T.sourceTensor_symmetric q,
      T.localConservation_to_covariantConservation hLocal ⟩

/-
Manuscript-facing predicate for the selected effective source.

This is useful later when applying the external four-dimensional geometric
classification: the source side is already known to possess the tensorial,
symmetric and covariantly conserved properties required by the effective GR
coupling.
-/
def HasAdmissibleEffectiveSource
    (B : CoarseGrainedLocalBalance)
    (P : PreservedQuantityBridge B)
    (T : EffectiveSourceTensorBridge B P)
    (q : B.Quantity) : Prop :=

  T.IsTensorial (T.sourceTensor q)
  ∧ T.IsSymmetric (T.sourceTensor q)
  ∧ T.IsCovariantlyConserved (T.sourceTensor q)

/-
Every quantity marked as preserved by the microscopic-to-coarse-grained
bridge has an admissible effective source in the above sense.
-/
theorem preservedQuantity_has_admissibleEffectiveSource
    (B : CoarseGrainedLocalBalance)
    (P : PreservedQuantityBridge B)
    (T : EffectiveSourceTensorBridge B P)
    (q : B.Quantity)
    (hPreserved : P.IsPreserved q) :

    HasAdmissibleEffectiveSource B P T q := by

  exact
    preservedQuantity_has_effectiveConservedSource
      B P T q hPreserved

end GR
end SBI
