import SBILeanProject.SBI.Frustration

set_option autoImplicit false

namespace SBI

/-
S2 — Admissible deformation and realization independence.

The preceding development introduced configurations but deliberately
did not introduce a primitive dynamical or temporal evolution law.

We now introduce the relation

    X ⟶ X'

meaning that X' is obtainable from X by one admissible relational
rearrangement.

This relation is structural rather than temporal:
it expresses admissible reachability between relational
configurations.  No duration, time coordinate, or direction of
physical time is assumed.
-/

/-
Semantics of one admissible configuration change.

AdmissibleStep O X X' means that X and X' are related by one
admissible relational rearrangement at observer O's operational
resolution.

The relation is intentionally left abstract here.  Earlier results
constrain physically realized rearrangements through local mediation,
but no particular microscopic rearrangement rule is assumed.
-/
structure ConfigurationChangeSemantics
    {M : SBI}
    {C : NetworkRealizationContext M}
    (K : OperationalContext C) where

  AdmissibleStep :
    (O : Observer M) →
    Configuration K O →
    Configuration K O →
    Prop

/-
Admissible deformation between endpoint configurations.

AdmissibleDeformation D O X X' means that X' is reachable
from X by finitely many admissible relational rearrangements.

There are two constructors:

  • refl:
      every configuration is deformable to itself by zero steps;

  • step:
      if X ⟶ Y by one admissible rearrangement, and Y can be
      finitely deformed to Z, then X can be finitely deformed to Z.

This is the endpoint form of the manuscript sequence

    X = X₀ ⟶ X₁ ⟶ ... ⟶ Xₙ = X'.

It is a structural reachability relation, not a temporal
evolution relation.
-/
inductive AdmissibleDeformation
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (O : Observer M) :
    Configuration K O →
    Configuration K O →
    Prop

  | refl (X : Configuration K O) :
      AdmissibleDeformation D O X X

  | step
      {X Y Z : Configuration K O}
      (hStep : D.AdmissibleStep O X Y)
      (hRest : AdmissibleDeformation D O Y Z) :
      AdmissibleDeformation D O X Z

/-
Admissible deformation is reflexive.

Every configuration is reachable from itself by a deformation
containing zero rearrangement steps.
-/
theorem admissibleDeformation_refl
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (O : Observer M)
    (X : Configuration K O) :

    AdmissibleDeformation D O X X := by

  exact AdmissibleDeformation.refl X

/-
Admissible deformation is transitive.

If

    X ↝ Y

by a finite admissible deformation and

    Y ↝ Z

by another finite admissible deformation, then concatenating
the two finite rearrangement sequences gives

    X ↝ Z.

Thus AdmissibleDeformation is finite admissible reachability.
-/
theorem admissibleDeformation_trans
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (O : Observer M)
    {X Y Z : Configuration K O}
    (hXY : AdmissibleDeformation D O X Y)
    (hYZ : AdmissibleDeformation D O Y Z) :

    AdmissibleDeformation D O X Z := by

  induction hXY with

  | refl X =>
      exact hYZ

  | step hStep hRest ih =>
      exact
        AdmissibleDeformation.step
          hStep
          (ih hYZ)

/-
Definition — Persistence-preserving admissible deformation.

The manuscript first defines an admissible deformation and then adds the
condition that the same persistent identity remain operationally
re-identifiable throughout that deformation.

To preserve that hierarchy explicitly in Lean, we separate:

  • PersistencePreservingPath:
      the step-by-step certificate that persistent identity is
      re-identified along a finite admissible rearrangement sequence;

  • PersistencePreservingDeformation:
      an admissible deformation together with such a certificate.

The second object is the manuscript-facing notion.  In particular it
contains an AdmissibleDeformation as its parent reachability statement
rather than rebuilding an unrelated deformation relation in parallel.
-/

/-
Internal path certificate for persistence preservation.

For a finite sequence

    X₀ ⟶ X₁ ⟶ ... ⟶ Xₙ,

the certificate records operational re-identification across every
successive admissible step.  The zero-step case requires the persistent
identity to be present in the configuration.

This is implementation support for the manuscript-facing
PersistencePreservingDeformation below.
-/
inductive PersistencePreservingPath
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (P : PersistenceContext K)
    (O : Observer M)
    (R : M.Org) :
    Configuration K O →
    Configuration K O →
    Prop

  | refl
      (X : Configuration K O)
      (hPresent :
        PersistentStructuresPresent P O X R) :

      PersistencePreservingPath
        D P O R X X

  | step
      {X Y Z : Configuration K O}
      (hStep :
        D.AdmissibleStep O X Y)
      (hReidentified :
        OperationallyReidentified P O X Y R)
      (hRest :
        PersistencePreservingPath
          D P O R Y Z) :

      PersistencePreservingPath
        D P O R X Z

/-
Every persistence-preserving path certificate determines an admissible
deformation with the same endpoints.

This theorem is used to construct the manuscript-facing refinement below.
-/
theorem persistencePreservingPath_is_admissible
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (P : PersistenceContext K)
    (O : Observer M)
    (R : M.Org)
    {X Y : Configuration K O}
    (hPath :
      PersistencePreservingPath
        D P O R X Y) :

    AdmissibleDeformation D O X Y := by

  induction hPath with

  | refl X hPresent =>
      exact
        AdmissibleDeformation.refl X

  | step hStep hReidentified hRest ih =>
      exact
        AdmissibleDeformation.step
          hStep
          ih

/-
Manuscript-facing persistence-preserving admissible deformation.

This is an actual refinement of AdmissibleDeformation:

  • deformation records finite admissible reachability X ↝ Y;
  • preservingPath records that the persistent identity [R]ₚ remains
    operationally re-identifiable throughout such a finite admissible
    rearrangement sequence.

The explicit parent field is important for traceability: Definition 14 in
S2 first introduces admissible deformation and then qualifies a deformation
as persistence-preserving.
-/
structure PersistencePreservingDeformation
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (P : PersistenceContext K)
    (O : Observer M)
    (R : M.Org)
    (X Y : Configuration K O) : Prop where

  deformation :
    AdmissibleDeformation D O X Y

  preservingPath :
    PersistencePreservingPath
      D P O R X Y

/-
Canonical construction from a persistence-preserving path certificate.

The admissible-deformation component is not a second physical assumption:
it is derived from the same certified sequence of admissible steps.
-/
theorem PersistencePreservingDeformation.ofPath
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (P : PersistenceContext K)
    (O : Observer M)
    (R : M.Org)
    {X Y : Configuration K O}
    (hPath :
      PersistencePreservingPath
        D P O R X Y) :

    PersistencePreservingDeformation
      D P O R X Y :=

  {
    deformation :=
      persistencePreservingPath_is_admissible
        D P O R hPath

    preservingPath := hPath
  }

/-
Every persistence-preserving deformation is, by construction, an
admissible deformation.

This is now a projection from the refinement rather than a bridge between
two independently defined deformation relations.
-/
theorem persistencePreservingDeformation_is_admissible
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (P : PersistenceContext K)
    (O : Observer M)
    (R : M.Org)
    {X Y : Configuration K O}
    (hPreserving :
      PersistencePreservingDeformation
        D P O R X Y) :

    AdmissibleDeformation D O X Y := by

  exact hPreserving.deformation


/-
Internal endpoint lemma for a persistence-preserving path certificate.

This theorem is stated directly on the indexed path object.  The
manuscript-facing refinement structure below carries such a certificate,
but induction is cleaner and more stable when performed on the path itself.
-/
theorem persistencePreservingPath_endpoints_present
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (P : PersistenceContext K)
    (O : Observer M)
    (R : M.Org)
    {X Y : Configuration K O}
    (hPath :
      PersistencePreservingPath
        D P O R X Y) :

    PersistentStructuresPresent P O X R
    ∧
    PersistentStructuresPresent P O Y R := by

  induction hPath with

  | refl X hPresent =>
      exact ⟨hPresent, hPresent⟩

  | step hStep hReidentified hRest ih =>

      rcases hReidentified with
        ⟨R₁, R₂, Dist,
          hOccurs₁,
          hOccurs₂,
          hPersist₁,
          hPersist₂,
          hAccessible,
          hDistinction⟩

      constructor

      · exact ⟨R₁, hOccurs₁, hPersist₁⟩

      · exact ih.2

/-
Persistent identity is present at both endpoints of a
persistence-preserving deformation.

If

    X ↝ Y

preserves the persistent identity [R]ₚ throughout, then [R]ₚ
is present in both X and Y.

The manuscript-facing theorem delegates the inductive argument to the
path certificate stored in PersistencePreservingDeformation.
-/
theorem persistencePreservingDeformation_endpoints_present
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (P : PersistenceContext K)
    (O : Observer M)
    (R : M.Org)
    {X Y : Configuration K O}
    (hPreserving :
      PersistencePreservingDeformation
        D P O R X Y) :

    PersistentStructuresPresent P O X R
    ∧
    PersistentStructuresPresent P O Y R := by

  exact
    persistencePreservingPath_endpoints_present
      D P O R hPreserving.preservingPath


/-
Relational property essential to operational re-identification.

A relational property Q assigns a value to each operational
configuration.

    Q : Configuration K O → α

Q is essential to the operational re-identification of persistent
identity [R]ₚ when any two configurations across which R is
operationally re-identified must have the same value of Q.

Thus preservation of Q is necessary for those two realizations
to count operationally as the same persistent structure.

The codomain α is arbitrary: Q may represent a Boolean property,
a discrete class, an integer-valued invariant, or any other
relational descriptor.
-/
def EssentialToReidentification
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (P : PersistenceContext K)
    (O : Observer M)
    (R : M.Org)
    {α : Type}
    (Q : Configuration K O → α) : Prop :=

  ∀ {X Y : Configuration K O},
    OperationallyReidentified P O X Y R →
    Q X = Q Y

/-
Internal realization-independence lemma for a certified
persistence-preserving path.

The induction is performed directly on PersistencePreservingPath.
-/
theorem realization_independence_of_path
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (P : PersistenceContext K)
    (O : Observer M)
    (R : M.Org)
    {α : Type}
    (Q : Configuration K O → α)
    (hEssential :
      EssentialToReidentification P O R Q)
    {X Y : Configuration K O}
    (hPath :
      PersistencePreservingPath
        D P O R X Y) :

    Q X = Q Y := by

  induction hPath with

  | refl X hPresent =>
      rfl

  | step hStep hReidentified hRest ih =>

      have hFirst :
          Q _ = Q _ :=
        hEssential hReidentified

      exact
        Eq.trans hFirst ih

/-
Theorem — Realization independence.

Let Q be a relational property essential to the operational
re-identification of persistent identity [R]ₚ.

If X can be deformed admissibly into Y while [R]ₚ remains
operationally re-identifiable throughout the deformation, then

    Q(X) = Q(Y).

Thus an essential relational property is invariant under every
persistence-preserving admissible deformation.

The theorem does not assert that Q is unchanged under arbitrary
admissible deformation.  Its invariance is conditional on
continued operational re-identification of the same persistent
structure.
-/
theorem realization_independence
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (P : PersistenceContext K)
    (O : Observer M)
    (R : M.Org)
    {α : Type}
    (Q : Configuration K O → α)
    (hEssential :
      EssentialToReidentification P O R Q)
    {X Y : Configuration K O}
    (hPreserving :
      PersistencePreservingDeformation
        D P O R X Y) :

    Q X = Q Y := by

  exact
    realization_independence_of_path
      D P O R Q hEssential hPreserving.preservingPath


/-
Semantics of context-preserving local deformation.

Let Ω be a relational domain.

A configuration change X ⟶ X' is local to Ω when the relational
change is confined to Ω while the relational organization outside Ω
remains unchanged.

Because we have not introduced a primitive spatial decomposition of
configurations, confinement and preservation of the surrounding
relational organization are represented operationally by predicates.

These predicates specify the meaning of "local to Ω" and
"context-preserving"; they introduce no geometry or background space.
-/
structure LocalDeformationSemantics
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K) where

  /-
  ChangeConfinedTo O Ω X X' means that the relational change between
  X and X' is confined to the relational domain Ω.
  -/
  ChangeConfinedTo :
    (O : Observer M) →
    Domain M →
    Configuration K O →
    Configuration K O →
    Prop

  /-
  OutsideContextUnchanged O Ω X X' means that the relational
  organization outside Ω relevant to the represented configuration
  is unchanged between X and X'.
  -/
  OutsideContextUnchanged :
    (O : Observer M) →
    Domain M →
    Configuration K O →
    Configuration K O →
    Prop

/-
One context-preserving admissible rearrangement local to Ω.

Such a step must satisfy three conditions:

  • it is an admissible configuration change;
  • the change is confined to Ω;
  • the surrounding relational organization outside Ω is unchanged.

This is the one-step form of manuscript Definition 15.
-/
def ContextPreservingLocalStep
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (L : LocalDeformationSemantics D)
    (O : Observer M)
    (Ω : Domain M)
    (X X' : Configuration K O) : Prop :=

  D.AdmissibleStep O X X' ∧
  L.ChangeConfinedTo O Ω X X' ∧
  L.OutsideContextUnchanged O Ω X X'

/-
Definition — Context-preserving local deformation.

The manuscript defines this as an admissible deformation with the additional
condition that every constituent rearrangement is confined to Ω and leaves
the surrounding relational organization unchanged.

As above, the formalization keeps the parent-child relation explicit:

  • ContextPreservingLocalPath is the internal step-by-step certificate;
  • ContextPreservingLocalDeformation is an AdmissibleDeformation carrying
    that certificate.

Thus Definition 15 depends structurally on Definition 14 exactly as in S2.
-/

/-
Internal certificate for a context-preserving local deformation.

Each step is an admissible rearrangement local to Ω and preserves the
outside relational context.  The zero-step path is included reflexively.
-/
inductive ContextPreservingLocalPath
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (L : LocalDeformationSemantics D)
    (O : Observer M)
    (Ω : Domain M) :
    Configuration K O →
    Configuration K O →
    Prop

  | refl
      (X : Configuration K O) :

      ContextPreservingLocalPath
        D L O Ω X X

  | step
      {X Y Z : Configuration K O}
      (hLocal :
        ContextPreservingLocalStep
          D L O Ω X Y)
      (hRest :
        ContextPreservingLocalPath
          D L O Ω Y Z) :

      ContextPreservingLocalPath
        D L O Ω X Z

/-
Every context-preserving local path certificate determines an admissible
deformation with the same endpoints.
-/
theorem contextPreservingLocalPath_is_admissible
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (L : LocalDeformationSemantics D)
    (O : Observer M)
    (Ω : Domain M)
    {X Y : Configuration K O}
    (hPath :
      ContextPreservingLocalPath
        D L O Ω X Y) :

    AdmissibleDeformation D O X Y := by

  induction hPath with

  | refl X =>
      exact
        AdmissibleDeformation.refl X

  | step hLocalStep hRest ih =>

      have hAdmissibleStep :
          D.AdmissibleStep O _ _ :=
        hLocalStep.1

      exact
        AdmissibleDeformation.step
          hAdmissibleStep
          ih

/-
Manuscript-facing context-preserving local deformation.

The parent deformation records admissible finite reachability.  The local
path certificate adds confinement to Ω and preservation of the surrounding
relational context at every step.
-/
structure ContextPreservingLocalDeformation
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (L : LocalDeformationSemantics D)
    (O : Observer M)
    (Ω : Domain M)
    (X Y : Configuration K O) : Prop where

  deformation :
    AdmissibleDeformation D O X Y

  localPath :
    ContextPreservingLocalPath
      D L O Ω X Y

/-
Canonical construction from the local path certificate.

The admissible parent is derived from the same sequence, so no additional
physical assumption is introduced.
-/
theorem ContextPreservingLocalDeformation.ofPath
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (L : LocalDeformationSemantics D)
    (O : Observer M)
    (Ω : Domain M)
    {X Y : Configuration K O}
    (hPath :
      ContextPreservingLocalPath
        D L O Ω X Y) :

    ContextPreservingLocalDeformation
      D L O Ω X Y :=

  {
    deformation :=
      contextPreservingLocalPath_is_admissible
        D L O Ω hPath

    localPath := hPath
  }

/-
Every context-preserving local deformation is, by construction, an
admissible deformation.

Again this is now a projection from the refinement rather than a theorem
relating two parallel deformation relations.
-/
theorem contextPreservingLocalDeformation_is_admissible
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (L : LocalDeformationSemantics D)
    (O : Observer M)
    (Ω : Domain M)
    {X Y : Configuration K O}
    (hLocal :
      ContextPreservingLocalDeformation
        D L O Ω X Y) :

    AdmissibleDeformation D O X Y := by

  exact hLocal.deformation

/-
Persistence-protected property value.

A property value q = Q(X) is persistence-protected when it is
unchanged under context-preserving local deformations through
which the persistent identity [R]ₚ itself remains operationally
re-identifiable.

This is a consequence of realization independence.

It is weaker than being a persistent relational defect:
a genuine defect must resist elimination under every
context-preserving local deformation in the relevant domain,
not only those already known to preserve the identity.
-/
def PersistenceProtectedValue
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
    (X : Configuration K O) : Prop :=

  Q X = q
  ∧
  ∀ Y : Configuration K O,

    ContextPreservingLocalDeformation
      D L O Ω X Y →

    PersistencePreservingDeformation
      D P O R X Y →

    Q Y = q

theorem essentialProperty_is_persistenceProtected
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
    (hEssential :
      EssentialToReidentification P O R Q)
    (X : Configuration K O) :

    PersistenceProtectedValue
      D L P O R Ω Q (Q X) X := by

  constructor

  · rfl

  · intro Y _hLocal hPreserving

    have hInvariant :
        Q X = Q Y :=
      realization_independence
        D P O R Q
        hEssential
        hPreserving

    exact hInvariant.symm

/-
Genuine local defect protection.

A relational property-value q = Q(X) is protected as a defect
within Ω when NO context-preserving admissible deformation local
to Ω can eliminate that value.

Unlike PersistenceProtectedValue, no persistence-preserving
premise is imposed on the deformation.

This is the formal obstruction appearing in the manuscript
definition of a persistent relational defect.
-/
def LocallyNonEliminable
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (L : LocalDeformationSemantics D)
    (O : Observer M)
    (Ω : Domain M)
    {α : Type}
    (Q : Configuration K O → α)
    (q : α)
    (X : Configuration K O) : Prop :=

  Q X = q
  ∧
  ∀ Y : Configuration K O,

    ContextPreservingLocalDeformation
      D L O Ω X Y →

    Q Y = q




/-
Operational re-identifiability of a persistent identity at X.

The identity represented by R is operationally re-identifiable
from configuration X when there exists at least one configuration
Y across which R is operationally re-identified.

This excludes vacuous claims about properties being "essential
to re-identification" when no re-identification occurs at all.
-/
def OperationallyReidentifiableAt
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (P : PersistenceContext K)
    (O : Observer M)
    (R : M.Org)
    (X : Configuration K O) : Prop :=

  ∃ Y : Configuration K O,
    OperationallyReidentified P O X Y R


/-
Definition — Persistent relational defect.

A relational property-value q of configuration X is a persistent
relational defect associated with identity [R]ₚ in relational
domain Ω when

  • R is actually operationally re-identifiable from X;

  • Q is essential to that operational re-identification;

  • q = Q(X) cannot be eliminated by any context-preserving
    admissible deformation local to Ω.

This matches the manuscript requirement that P first be an
operationally re-identifiable persistent structure.

No topological character is assumed.
-/
def PersistentRelationalDefect
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
    (X : Configuration K O) : Prop :=

  OperationallyReidentifiableAt P O R X
  ∧
  EssentialToReidentification P O R Q
  ∧
  LocallyNonEliminable D L O Ω Q q X


/-
A persistent relational defect is genuinely operationally
re-identifiable; this is part of its definition rather than a
vacuous consequence of an identifying predicate.
-/
theorem persistentRelationalDefect_is_reidentifiable
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

    OperationallyReidentifiableAt P O R X := by

  exact hDefect.1


/-
Every persistent relational defect is persistence-protected.

A genuine defect is non-eliminable under every context-preserving
local deformation.

Therefore it is certainly non-eliminable under the narrower
class of context-preserving local deformations that also preserve
the persistent identity.

Thus:

    PersistentRelationalDefect
        ⇒
    PersistenceProtectedValue.

This theorem makes explicit that defect protection is stronger
than realization-independence protection.
-/
theorem persistentRelationalDefect_is_persistenceProtected
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

    PersistenceProtectedValue
      D L P O R Ω Q q X := by

  rcases hDefect with
    ⟨hReidentifiable, hEssential, hNonEliminable⟩

  rcases hNonEliminable with
    ⟨hQX, hProtected⟩

  constructor

  · exact hQX

  · intro Y hLocal _hPreserving

    exact hProtected Y hLocal

/-
Persistent relational defects have finite operational support.

A PersistentRelationalDefect is, by definition, genuinely
operationally re-identifiable from X.

Thus there exists some configuration Y across which the same
persistent identity [R]ₚ is operationally re-identified.

FOA then supplies a finite operational support for that
re-identification, including finite conjunction and direct-
relation support at the network level.

This proves the finite-support clause of the structural
characterization theorem.
-/
theorem persistentRelationalDefect_has_finiteOperationalSupport
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (L : LocalDeformationSemantics D)
    (P : PersistenceContext K)
    (hFOA : FOA C.toNetworkContext)
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

    ∃ Y : Configuration K O,
      ∃ S : OperationalSupport P O X Y R,
        ∃ Efin : List (DirectRelation C O),

          (∀ a : M.Interaction,
            a ∈ S.interactions →
            InteractionConjunction C O a
              ∈ supportConjunctions S)

          ∧

          (∀ e : DirectRelation C O,
            IsSupportDirectRelation S e →
            e ∈ Efin) := by

  rcases hDefect.1 with
    ⟨Y, hReidentified⟩

  rcases
    operationallyReidentified_has_finiteNetworkSupport
      P hFOA O X Y R hReidentified with
    ⟨S, Efin, hConjunctions, hEdges⟩

  exact
    ⟨Y, S, Efin,
      hConjunctions,
      hEdges⟩

/-
The identifying property of a persistent relational defect is
invariant under persistence-preserving admissible deformation.

PersistentRelationalDefect already contains the statement that
Q is essential to operational re-identification of [R]ₚ.

The Realization Independence Theorem therefore gives

    Q(X) = Q(Y)

for every persistence-preserving admissible deformation from
X to Y.

This proves the realization-independence clause of the
structural characterization theorem.
-/
theorem persistentRelationalDefect_identifyingProperty_invariant
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
        D L P O R Ω Q q X)
    {Y : Configuration K O}
    (hPreserving :
      PersistencePreservingDeformation
        D P O R X Y) :

    Q X = Q Y := by

  have hEssential :
      EssentialToReidentification P O R Q :=
    hDefect.2.1

  exact
    realization_independence
      D P O R Q
      hEssential
      hPreserving

/-
A persistent relational defect cannot be eliminated by any
context-preserving local deformation within Ω.

Unlike realization independence, no premise is made here that
the deformation preserves the persistent identity [R]ₚ.

This is the genuine defect obstruction:

    X ↝Ω Y  ⇒  Q(Y) = q.

Thus any admissible local deformation that changes the
identifying property-value must necessarily fail to preserve
the specified external relational context.
-/
theorem persistentRelationalDefect_is_locallyNonEliminable
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
        D L P O R Ω Q q X)
    {Y : Configuration K O}
    (hLocal :
      ContextPreservingLocalDeformation
        D L O Ω X Y) :

    Q Y = q := by

  have hNonEliminable :
      LocallyNonEliminable
        D L O Ω Q q X :=
    hDefect.2.2

  exact hNonEliminable.2 Y hLocal
