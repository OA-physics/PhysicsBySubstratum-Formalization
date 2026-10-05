import SBILeanProject.GR.GeometricRepresentation

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Coarse-grained local balance and conservation.

This module formalizes the logical core of the manuscript lemma
"Local conservation structure".

The manuscript makes an important coarse-graining step here.  Persistence
and local mediation motivate the claim that changes of coarse-grained
persistent content inside a region can be represented as

    change = boundary transport + local source.

That continuum balance relation is not already a theorem of A1--A3 in the
present Lean development.  It is therefore represented explicitly below as
part of `CoarseGrainedLocalBalance` rather than being silently derived from
the axioms.

Once such a local balance description has been adopted, the conservation
step is elementary but important:

    if a quantity is preserved by the admissible local transformations,
    its local source term vanishes;

therefore

    change = boundary transport.

This is the pre-tensor form of the manuscript's local conservation argument.
The later identification with a symmetric stress-energy tensor satisfying

    ∇^μ T_{μν} = 0

belongs to the effective geometric representation and is not asserted in
this file.
-/

/-
Abstract coarse-grained local balance semantics.

`Region` denotes a coarse-grained region of the effective description.
`Quantity` denotes a coarse-grained quantity whose local balance is being
tracked.

For each region r and quantity q:

  * `change r q` is the net change of q inside the region;
  * `boundaryTransport r q` is the net contribution entering through the
    region boundary;
  * `localSource r q` is the contribution from admissible local
    transformation inside the region.

All three are represented by real numbers only to provide the additive
structure needed for the balance equation.  No coordinate system, tensor
field, derivative operator, or metric is introduced.

The field `balance` is the explicit GR coarse-graining bridge:

    change = boundary transport + local source.

Lean verifies consequences of that bridge; it does not claim that A1--A3
alone have already produced a continuum balance law.
-/
structure CoarseGrainedLocalBalance where

  Region : Type

  Quantity : Type

  change :
    Region → Quantity → Real

  boundaryTransport :
    Region → Quantity → Real

  localSource :
    Region → Quantity → Real

  balance :
    ∀ (r : Region) (q : Quantity),
      change r q =
        boundaryTransport r q + localSource r q

/-
A source-free quantity.

A quantity is source-free when admissible local transformation contributes
no net creation or destruction term in any coarse-grained region.

In the manuscript this is the condition supplied when the underlying
admissible rearrangements preserve the quantity in question.
-/
def SourceFreeQuantity
    (B : CoarseGrainedLocalBalance)
    (q : B.Quantity) : Prop :=

  ∀ r : B.Region,
    B.localSource r q = 0

/-
Local conservation in integral-balance form.

The quantity is locally conserved when its change inside every region is
fully accounted for by transport across the region boundary.

This is the source-free balance statement prior to introducing a continuum
differential notation such as a divergence equation.
-/
def LocallyConservedQuantity
    (B : CoarseGrainedLocalBalance)
    (q : B.Quantity) : Prop :=

  ∀ r : B.Region,
    B.change r q = B.boundaryTransport r q

/-
Source-free local balance implies local conservation.

Starting from

    change = boundary transport + local source

and setting

    local source = 0,

we obtain

    change = boundary transport.

This theorem contains no additional physical assumption beyond the explicit
balance relation and the source-free condition.
-/
theorem sourceFreeQuantity_is_locallyConserved
    (B : CoarseGrainedLocalBalance)
    (q : B.Quantity)
    (hSourceFree : SourceFreeQuantity B q) :

    LocallyConservedQuantity B q := by

  intro r

  have hBalance := B.balance r q

  rw [hSourceFree r] at hBalance

  simpa using hBalance

/-
Bridge from microscopic preservation to the coarse-grained source term.

The manuscript states that, for quantities preserved by the underlying
admissible rearrangements, the local source term vanishes.

That identification is physical coarse-graining information and is not
already encoded by the current SBI axioms.  We therefore expose it as a
separate bridge rather than making `IsPreserved` definitionally identical to
`SourceFreeQuantity`.
-/
structure PreservedQuantityBridge
    (B : CoarseGrainedLocalBalance) where

  IsPreserved :
    B.Quantity → Prop

  preserved_source_free :
    ∀ {q : B.Quantity},
      IsPreserved q →
      SourceFreeQuantity B q

/-
A quantity preserved by the admissible rearrangements is locally conserved
in the coarse-grained balance description.

The logical chain is completely explicit:

    preserved by underlying rearrangements
        ->   [physical coarse-graining bridge]
    zero local source
        ->   [balance identity]
    change accounted for entirely by boundary transport.
-/
theorem preservedQuantity_is_locallyConserved
    (B : CoarseGrainedLocalBalance)
    (P : PreservedQuantityBridge B)
    (q : B.Quantity)
    (hPreserved : P.IsPreserved q) :

    LocallyConservedQuantity B q := by

  exact
    sourceFreeQuantity_is_locallyConserved
      B q
      (P.preserved_source_free hPreserved)

/-
Manuscript-facing bundle: local conservation structure.

A coarse-grained balance description possesses the required local
conservation structure for the selected preserved quantities when every
quantity marked as preserved satisfies the source-free local balance law.
-/
def HasLocalConservationStructure
    (B : CoarseGrainedLocalBalance)
    (P : PreservedQuantityBridge B) : Prop :=

  ∀ q : B.Quantity,
    P.IsPreserved q →
    LocallyConservedQuantity B q

/-
The explicit preservation-to-source bridge together with the local balance
relation supplies local conservation structure.
-/
theorem localBalance_has_conservationStructure
    (B : CoarseGrainedLocalBalance)
    (P : PreservedQuantityBridge B) :

    HasLocalConservationStructure B P := by

  intro q hPreserved

  exact
    preservedQuantity_is_locallyConserved
      B P q hPreserved

end GR
end SBI
