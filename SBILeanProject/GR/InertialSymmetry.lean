import SBILeanProject.GR.InertialPersistence
import SBILeanProject.GR.CausalPropagation

set_option autoImplicit false

namespace SBI
namespace GR

/-
GR — Operational inertial equivalence and invariance of causal structure.

This module formalizes the part of the GR manuscript that lies between the
pre-geometric Newton-I result and the later Lorentz-classification step.

Two logically distinct ingredients are kept separate but explicitly linked.

1. Inertial equivalence

   If two inertial descriptions contain no relational distinction between
   the physical states they represent, then any physically meaningful
   descriptor must assign them the same value.  This is a direct
   specialization of A1 invariance.

2. Causal-structure invariance

   If causal accessibility is itself physically meaningful, then a change
   of inertial description that maps every represented state to an
   operationally equivalent realization cannot alter which pairs are
   causally accessible.

The link between these statements is important.  The operational inertial
criterion is first translated to the canonical relational equivalence used by
A1; only then is causal invariance derived.  This prevents the causal-symmetry
branch from bypassing the manuscript's no-absolute-rest argument.

The file deliberately stops there.  It does NOT prove the standard
classification theorem saying that homogeneous and isotropic inertial
transformations with a finite invariant causal speed are Lorentz
transformations.  That final classification is established external
mathematics and should enter the formal dependency graph as an explicitly
identified imported theorem rather than being silently folded into the SBI
axioms.

Likewise, no coordinate system, spacetime manifold, metric tensor, or
velocity variable is introduced here.
-/

/-
Operational inertial-equivalence semantics.

The manuscript argues that, within the homogeneous/isotropic inertial
regime, two descriptions that differ only by uniform inertial state possess
no accessible relational distinction selecting one as absolute rest.

The genuinely physical bridge is represented explicitly by
`relEq_of_equivalent`: whenever the GR-level operational criterion declares
two inertial realizations equivalent, they are relationally equivalent in
the sense already used by A1.

This structure does not assert that arbitrary states are equivalent.  It
only records the correspondence for the inertial regime to which the
manuscript relativity argument applies.
-/
structure InertialEquivalenceSemantics (M : SBI) where

  OperationallyEquivalent :
    M.Org → M.Org → Prop

  relEq_of_equivalent :
    ∀ {R₁ R₂ : M.Org},
      OperationallyEquivalent R₁ R₂ →
      M.RelEq R₁ R₂

/-
No physically meaningful descriptor can distinguish two operationally
inertial-equivalent realizations.

This is exactly A1 invariance after applying the explicit bridge from the
GR inertial-equivalence relation to the canonical relational-equivalence
relation.

The descriptor may represent any proposed locally observable marker of
absolute inertial state.  If it is physically meaningful and the two
realizations are operationally equivalent, its value must agree.
-/
theorem inertialEquivalent_descriptors_agree
    {M : SBI}
    (I : InertialEquivalenceSemantics M)
    {α : Type}
    (F : M.Org → α)
    (hPhys : M.PhysMeaningful F)
    {R₁ R₂ : M.Org}
    (hEquivalent : I.OperationallyEquivalent R₁ R₂) :

    F R₁ = F R₂ := by

  exact
    M.A1_invariance
      hPhys
      (I.relEq_of_equivalent hEquivalent)

/-
Negative formulation of the no-absolute-inertial-marker result.

A physically meaningful descriptor cannot both distinguish R₁ from R₂ and
satisfy the operational inertial-equivalence condition.
-/
theorem no_physicallyMeaningful_absoluteInertialMarker
    {M : SBI}
    (I : InertialEquivalenceSemantics M)
    {α : Type}
    (F : M.Org → α)
    (hPhys : M.PhysMeaningful F)
    {R₁ R₂ : M.Org}
    (hEquivalent : I.OperationallyEquivalent R₁ R₂) :

    ¬ F R₁ ≠ F R₂ := by

  intro hDifferent

  exact
    hDifferent
      (inertialEquivalent_descriptors_agree
        I F hPhys hEquivalent)

/-
Manuscript-level no-absolute-inertial-marker property.

Rather than fixing one candidate observable, this proposition quantifies over
all physically meaningful descriptors.  Operationally equivalent inertial
realizations must agree under every such descriptor.

This is the pre-coordinate content of the statement that the theory contains
no physically meaningful marker selecting absolute inertial state.
-/
def NoAbsoluteInertialMarker
    {M : SBI}
    (I : InertialEquivalenceSemantics M) : Prop :=

  ∀ (α : Type)
    (F : M.Org → α),
    M.PhysMeaningful F →
    ∀ {R₁ R₂ : M.Org},
      I.OperationallyEquivalent R₁ R₂ →
      F R₁ = F R₂

/-
A1 plus the operational-to-relational equivalence bridge excludes every
physically meaningful absolute inertial marker.
-/
theorem inertialEquivalence_excludes_absoluteMarker
    {M : SBI}
    (I : InertialEquivalenceSemantics M) :

    NoAbsoluteInertialMarker I := by

  intro α F hPhys R₁ R₂ hEquivalent

  exact
    inertialEquivalent_descriptors_agree
      I F hPhys hEquivalent

/-
Physically meaningful causal-accessibility semantics.

`CausallyAccessible P Q` means that Q lies in the admissible causal
accessibility relation from P at the relational level used by the GR
argument.

A1 invariance acts on unary descriptors.  A binary relation can be viewed
as a unary descriptor whose value is a predicate on the second argument.
We therefore require physical meaningfulness in both argument orientations:

  source orientation:
      P ↦ (Q ↦ CausallyAccessible P Q)

  target orientation:
      Q ↦ (P ↦ CausallyAccessible P Q).

This lets A1 establish invariance when either endpoint is replaced by a
relationally equivalent description.
-/
structure CausalAccessibilitySemantics (M : SBI) where

  CausallyAccessible :
    M.Org → M.Org → Prop

  physicallyMeaningful_source :
    M.PhysMeaningful CausallyAccessible

  physicallyMeaningful_target :
    M.PhysMeaningful
      (fun Q : M.Org =>
        fun P : M.Org =>
          CausallyAccessible P Q)

/-
Relationally equivalent source descriptions have identical causal futures.

The result is equality of predicates, not merely pointwise implication:

    CausalFuture(P) = CausalFuture(P').

Thus changing only the relationally redundant description of the source
state cannot change the set of states declared causally accessible from it.
-/
theorem causalFuture_eq_of_relEq
    {M : SBI}
    (Caus : CausalAccessibilitySemantics M)
    {P P' : M.Org}
    (hRel : M.RelEq P P') :

    Caus.CausallyAccessible P =
      Caus.CausallyAccessible P' := by

  exact
    M.A1_invariance
      Caus.physicallyMeaningful_source
      hRel

/-
Two-sided invariance of causal accessibility.

If both endpoint descriptions are replaced by relationally equivalent
representations, the truth value of causal accessibility is unchanged.
This is the formal core of the manuscript statement that admissibility of
the same underlying causal transition cannot depend on which equivalent
inertial description is used.
-/
theorem causalAccessibility_eq_of_relEq
    {M : SBI}
    (Caus : CausalAccessibilitySemantics M)
    {P P' Q Q' : M.Org}
    (hP : M.RelEq P P')
    (hQ : M.RelEq Q Q') :

    Caus.CausallyAccessible P Q =
      Caus.CausallyAccessible P' Q' := by

  have hSource :
      Caus.CausallyAccessible P =
        Caus.CausallyAccessible P' :=
    M.A1_invariance
      Caus.physicallyMeaningful_source
      hP

  have hSourceAtQ :
      Caus.CausallyAccessible P Q =
        Caus.CausallyAccessible P' Q :=
    congrFun hSource Q

  have hTarget :
      (fun R : M.Org => Caus.CausallyAccessible R Q) =
        (fun R : M.Org => Caus.CausallyAccessible R Q') :=
    M.A1_invariance
      Caus.physicallyMeaningful_target
      hQ

  have hTargetAtP' :
      Caus.CausallyAccessible P' Q =
        Caus.CausallyAccessible P' Q' :=
    congrFun hTarget P'

  exact hSourceAtQ.trans hTargetAtP'

/-
A relationally redundant redescription of states.

`map` may be thought of as a change of representation known already to map
each state to a relationally equivalent representation.  This low-level
structure remains useful as the direct input to the A1 causal-invariance
lemma below.

For the manuscript's inertial argument, however, relational equivalence
should not be assumed independently.  `OperationalInertialRedescription`
below supplies the physically relevant construction: operational inertial
equivalence first, relational equivalence as its consequence.
-/
structure InertialRedescription (M : SBI) where

  map :
    M.Org → M.Org

  sameRelationalState :
    ∀ P : M.Org,
      M.RelEq P (map P)

/-
Operational inertial redescription.

This is the missing bridge between the manuscript's operational relativity
argument and the causal-invariance result.  The redescription maps each
represented state to one that is operationally equivalent according to the
same `InertialEquivalenceSemantics` used in the no-absolute-marker argument.

It does NOT independently assume relational equivalence.  That fact is
derived below through `I.relEq_of_equivalent`.
-/
structure OperationalInertialRedescription
    {M : SBI}
    (I : InertialEquivalenceSemantics M) where

  map :
    M.Org → M.Org

  operationallyEquivalent :
    ∀ P : M.Org,
      I.OperationallyEquivalent P (map P)

/-
Every operational inertial redescription induces the lower-level relational
redescription required by A1.

This theorem-level construction is the explicit logical link

    operational inertial equivalence
        -> relational equivalence
        -> causal invariance.
-/
def OperationalInertialRedescription.toInertialRedescription
    {M : SBI}
    {I : InertialEquivalenceSemantics M}
    (T : OperationalInertialRedescription I) :

    InertialRedescription M :=

  { map := T.map
    sameRelationalState :=
      fun P =>
        I.relEq_of_equivalent
          (T.operationallyEquivalent P) }

/-
A redescription preserves causal structure when every ordered pair has the
same causal-accessibility truth value before and after redescription.
-/
def PreservesCausalStructure
    {M : SBI}
    (Caus : CausalAccessibilitySemantics M)
    (T : M.Org → M.Org) : Prop :=

  ∀ P Q : M.Org,
    Caus.CausallyAccessible P Q =
      Caus.CausallyAccessible (T P) (T Q)

/-
Every relationally redundant inertial redescription preserves the full
causal-accessibility relation.
-/
theorem inertialRedescription_preservesCausalStructure
    {M : SBI}
    (Caus : CausalAccessibilitySemantics M)
    (T : InertialRedescription M) :

    PreservesCausalStructure Caus T.map := by

  intro P Q

  exact
    causalAccessibility_eq_of_relEq
      Caus
      (T.sameRelationalState P)
      (T.sameRelationalState Q)

/-
Operational inertial equivalence therefore preserves causal accessibility.

Unlike the lower-level theorem above, this result does not take pointwise
relational equivalence as an independent premise.  It obtains that relation
from the same operational inertial-equivalence semantics used to exclude an
absolute inertial marker.
-/
theorem operationalInertialRedescription_preservesCausalStructure
    {M : SBI}
    (I : InertialEquivalenceSemantics M)
    (Caus : CausalAccessibilitySemantics M)
    (T : OperationalInertialRedescription I) :

    PreservesCausalStructure Caus T.map := by

  exact
    inertialRedescription_preservesCausalStructure
      Caus
      T.toInertialRedescription

/-
The manuscript-facing bundle for the pre-Lorentz symmetry result.
-/
def PreLorentzInertialSymmetry
    {M : SBI}
    (Caus : CausalAccessibilitySemantics M)
    (T : InertialRedescription M) : Prop :=

  PreservesCausalStructure Caus T.map

/-
Every relationally redundant inertial redescription satisfies the
pre-Lorentz causal-symmetry condition.
-/
theorem inertialRedescription_has_preLorentzSymmetry
    {M : SBI}
    (Caus : CausalAccessibilitySemantics M)
    (T : InertialRedescription M) :

    PreLorentzInertialSymmetry Caus T := by

  exact
    inertialRedescription_preservesCausalStructure
      Caus T

/-
Operational inertial equivalence supplies the pre-Lorentz causal symmetry.

This is the manuscript-facing form we want downstream: the same inertial
criterion that removes an absolute inertial marker now also supplies the
relationally redundant redescription needed to preserve causal structure.
-/
theorem operationalInertialRedescription_has_preLorentzSymmetry
    {M : SBI}
    (I : InertialEquivalenceSemantics M)
    (Caus : CausalAccessibilitySemantics M)
    (T : OperationalInertialRedescription I) :

    PreLorentzInertialSymmetry
      Caus
      T.toInertialRedescription := by

  unfold PreLorentzInertialSymmetry

  exact
    operationalInertialRedescription_preservesCausalStructure
      I Caus T

end GR
end SBI
