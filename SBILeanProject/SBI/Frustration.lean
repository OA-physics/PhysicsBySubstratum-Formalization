import SBILeanProject.SBI.PersistenceLocal

set_option autoImplicit false

namespace SBI

/-
S2 — Local structural frustration.

PersistenceLocal.lean defined the persistence-preserving local
sets

    U_R(v; Y).

We now study what happens when several persistent identities
place simultaneous compatibility requirements on the same
local relational conjunction.

The central question is whether there exists one locally
admissible configuration Z satisfying all of those requirements.

No configuration-change relation or dynamics is introduced yet.
-/

/-
One local persistence requirement.

At fixed observer O and conjunction v, a requirement consists of

  • a persistent identity represented by R;
  • the relational context Y relevant to that identity.

Its compatible local configurations are precisely

    U_R(v; Y).
-/
structure LocalPersistenceRequirement
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O) where

  R : M.Org

  Y : S.RelationalContext O v

/-
Satisfaction of one local persistence requirement.

A local configuration Z satisfies requirement Q exactly when

    Z ∈ U_{Q.R}(v; Q.Y).

Thus satisfaction means both

  • Z is locally admissible at v;
  • the persistent identity represented by Q.R remains
    operationally re-identifiable in context Q.Y.
-/
def SatisfiesPersistenceRequirement
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Q : LocalPersistenceRequirement S O v)
    (Z : LocalConfigurationSpace K O v) : Prop :=

  PersistencePreservingLocal
    S O Q.R v Q.Y Z

/-
Simultaneous satisfaction of a finite family of local
persistence requirements.

A local configuration Z satisfies a list Qs when it satisfies
every requirement appearing in Qs.

For

    Qs = [Q₁, Q₂, ..., Qₙ]

this means

    Z ∈ U_{Q₁.R}(v; Q₁.Y)
    ∧
    Z ∈ U_{Q₂.R}(v; Q₂.Y)
    ∧
    ...
    ∧
    Z ∈ U_{Qₙ.R}(v; Qₙ.Y).

The empty list is trivially satisfied.
-/
def SatisfiesAllRequirements
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O) :
    List (LocalPersistenceRequirement S O v) →
    LocalConfigurationSpace K O v →
    Prop

  | [], _ =>
      True

  | Q :: Qs, Z =>
      SatisfiesPersistenceRequirement S O v Q Z ∧
      SatisfiesAllRequirements S O v Qs Z

/-
Definition — Finite local structural frustration.

A finite nonempty collection Qs of local persistence
requirements is structurally frustrated at conjunction v when
there exists no single local configuration Z satisfying every
requirement in Qs.

For

    Qs = [Q₁, ..., Qₙ]

this is the formal counterpart of

    ⋂ᵢ U_{Qᵢ.R}(v; Qᵢ.Y) = ∅.

The explicit requirement

    Qs ≠ []

avoids the degenerate empty-family case.  Structural frustration
therefore refers to an actual collection of persistence
requirements.
-/
def FiniteLocalStructuralFrustration
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Qs : List (LocalPersistenceRequirement S O v)) : Prop :=

  Qs ≠ [] ∧
  ¬ ∃ Z : LocalConfigurationSpace K O v,
      SatisfiesAllRequirements S O v Qs Z

/-
Finite local compatibility.

A finite collection Qs of local persistence requirements is
compatible at conjunction v when there exists at least one
local configuration Z satisfying every requirement in Qs.

For

    Qs = [Q₁, ..., Qₙ]

this is the formal counterpart of

    ⋂ᵢ U_{Qᵢ.R}(v; Qᵢ.Y) ≠ ∅.
-/
def FiniteLocalCompatibility
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Qs : List (LocalPersistenceRequirement S O v)) : Prop :=

  ∃ Z : LocalConfigurationSpace K O v,
    SatisfiesAllRequirements S O v Qs Z

/-
For a nonempty finite family of persistence requirements,
structural frustration is exactly the failure of finite local
compatibility.

The nonempty hypothesis is needed because
FiniteLocalStructuralFrustration explicitly excludes the empty
family, whereas the empty family is trivially compatible.
-/
theorem finiteFrustration_iff_not_compatible
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Qs : List (LocalPersistenceRequirement S O v))
    (hNonempty : Qs ≠ []) :

    FiniteLocalStructuralFrustration S O v Qs ↔
    ¬ FiniteLocalCompatibility S O v Qs := by

  constructor

  · intro hFrustrated

    exact hFrustrated.2

  · intro hNotCompatible

    exact ⟨hNonempty, hNotCompatible⟩

/-
Full family of local persistence requirements.

At a fixed observer O and conjunction v, FullRequirementFamily
specifies which local persistence requirements are actually
present in the relational situation under consideration.

It is represented as a predicate on LocalPersistenceRequirement,
rather than as a finite List, because the full family need not
be assumed finite.

This distinction is important:

  • full-family incompatibility is a statement about all
    persistence requirements present at v;

  • finite structural frustration is witnessed by some finite
    subfamily whose common compatibility set is empty.
-/
def FullRequirementFamily
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O) :=

  LocalPersistenceRequirement S O v → Prop

/-
Full-family local compatibility.

A local configuration Z is compatible with the full family F
when it satisfies every persistence requirement belonging to F.
-/
def SatisfiesFullRequirementFamily
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (F : FullRequirementFamily S O v)
    (Z : LocalConfigurationSpace K O v) : Prop :=

  ∀ Q : LocalPersistenceRequirement S O v,
    F Q →
    SatisfiesPersistenceRequirement S O v Q Z

/-
Full-family local incompatibility.

The complete family F of persistence requirements at v is
locally incompatible when no single local configuration Z
satisfies every requirement in F.

Formally:

    ⋂_{Q ∈ F} U_{Q.R}(v; Q.Y) = ∅.

No finiteness of F is assumed.
-/
def FullLocalIncompatibility
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (F : FullRequirementFamily S O v) : Prop :=

  ¬ ∃ Z : LocalConfigurationSpace K O v,
      SatisfiesFullRequirementFamily S O v F Z


/-
Finite subfamily of a full requirement family.

Qs is a finite subfamily of F when every requirement appearing
in the finite List Qs belongs to F.

Because Qs is a List, finiteness is automatic.
-/
def IsFiniteSubfamily
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (F : FullRequirementFamily S O v)
    (Qs : List (LocalPersistenceRequirement S O v)) : Prop :=

  ∀ Q : LocalPersistenceRequirement S O v,
    Q ∈ Qs →
    F Q

/-
Finite frustration witness.

A finite list Qs witnesses the incompatibility of the full
requirement family F when

  • every requirement in Qs belongs to F;
  • Qs is already structurally frustrated.

Thus Qs is a finite subfamily whose persistence-compatible
sets have empty common intersection.

Manuscript content:

    Q₁, ..., Qₙ ∈ F

and

    ⋂ᵢ U_{Qᵢ.R}(v; Qᵢ.Y) = ∅.
-/
def IsFiniteFrustrationWitness
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (F : FullRequirementFamily S O v)
    (Qs : List (LocalPersistenceRequirement S O v)) : Prop :=

  IsFiniteSubfamily S O v F Qs ∧
  FiniteLocalStructuralFrustration S O v Qs

/-
If Z satisfies every requirement in a finite list Qs, then
it satisfies any particular requirement Q occurring in Qs.

This lets later proofs extract one persistence requirement
from SatisfiesAllRequirements without repeating list induction.
-/
theorem satisfiesAllRequirements_of_mem
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Qs : List (LocalPersistenceRequirement S O v))
    (Z : LocalConfigurationSpace K O v)
    (hAll :
      SatisfiesAllRequirements S O v Qs Z)
    {Q : LocalPersistenceRequirement S O v}
    (hMem : Q ∈ Qs) :

    SatisfiesPersistenceRequirement S O v Q Z := by

  induction Qs with

  | nil =>
      simp at hMem

  | cons Q₀ rest ih =>

      change
        SatisfiesPersistenceRequirement S O v Q₀ Z ∧
        SatisfiesAllRequirements S O v rest Z
        at hAll

      rcases hAll with
        ⟨hHead, hRest⟩

      rcases List.mem_cons.mp hMem with
        hEq | hTail

      · subst Q
        exact hHead

      · exact ih hRest hTail

/-
Finite realization of full-family incompatibility.

Assume:

  • C(I(v)) has a finite exhaustive list Cfin;
  • C(I(v)) contains at least one configuration;
  • the full persistence-requirement family F is incompatible.

For each local configuration Z, full incompatibility implies
that Z must fail at least one requirement Q_Z belonging to F.

Choose one such Q_Z for every Z in the finite configuration
space.  Since there are finitely many Z, this produces a finite
family of requirements.

Every possible local configuration fails its own selected
requirement, so no configuration satisfies the selected family.
Hence that finite family is a structural-frustration witness.
-/
theorem fullIncompatibility_has_finiteWitness
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (F : FullRequirementFamily S O v)
    (Cfin : List (LocalConfigurationSpace K O v))
    (hCfin :
      ∀ Z : LocalConfigurationSpace K O v,
        Z ∈ Cfin)
    (hNonempty :
      Nonempty (LocalConfigurationSpace K O v))
    (hIncompatible :
      FullLocalIncompatibility S O v F) :

    ∃ Qs : List (LocalPersistenceRequirement S O v),
      IsFiniteFrustrationWitness S O v F Qs := by

  classical

  /-
  Every local configuration fails at least one requirement
  belonging to F.
  -/
  have hFailure :
      ∀ Z : LocalConfigurationSpace K O v,
        ∃ Q : LocalPersistenceRequirement S O v,
          F Q ∧
          ¬ SatisfiesPersistenceRequirement S O v Q Z := by

    intro Z

    by_cases hExists :
        ∃ Q : LocalPersistenceRequirement S O v,
          F Q ∧
          ¬ SatisfiesPersistenceRequirement S O v Q Z

    · exact hExists

    ·
      have hSatisfiesFull :
          SatisfiesFullRequirementFamily S O v F Z := by

        intro Q hFQ

        by_cases hSatisfied :
            SatisfiesPersistenceRequirement S O v Q Z

        · exact hSatisfied

        ·
          have hFalse : False :=
            hExists ⟨Q, hFQ, hSatisfied⟩

          exact False.elim hFalse

      have hFalse : False :=
        hIncompatible ⟨Z, hSatisfiesFull⟩

      exact False.elim hFalse

  /-
  Select one failed requirement for each local configuration.
  -/
  let chooseRequirement :
      LocalConfigurationSpace K O v →
      LocalPersistenceRequirement S O v :=
    fun Z =>
      Classical.choose (hFailure Z)

  refine
    ⟨Cfin.map chooseRequirement, ?_⟩

  unfold IsFiniteFrustrationWitness

  constructor

  /-
  Every selected requirement belongs to F.
  -/
  · intro Q hQ

    rcases List.mem_map.mp hQ with
      ⟨Z, hZ, hEq⟩

    subst Q

    exact
      (Classical.choose_spec (hFailure Z)).1

  /-
  The selected finite family is structurally frustrated.
  -/
  · unfold FiniteLocalStructuralFrustration

    constructor

    /-
    The selected family is nonempty because the local
    configuration space is nonempty and Cfin exhausts it.
    -/
    · rcases hNonempty with
        ⟨Z₀⟩

      have hZ₀ :
          Z₀ ∈ Cfin :=
        hCfin Z₀

      have hMapped :
          chooseRequirement Z₀
            ∈ Cfin.map chooseRequirement := by

        apply List.mem_map.mpr

        exact ⟨Z₀, hZ₀, rfl⟩

      intro hEmpty

      simp [hEmpty] at hMapped


    /-
    No local configuration satisfies all selected requirements.
    -/
    · intro hCompatible

      rcases hCompatible with
        ⟨Z, hAll⟩

      have hZ :
          Z ∈ Cfin :=
        hCfin Z

      have hChosenMem :
          chooseRequirement Z
            ∈ Cfin.map chooseRequirement := by

        apply List.mem_map.mpr

        exact ⟨Z, hZ, rfl⟩

      have hChosenSatisfied :
          SatisfiesPersistenceRequirement
            S O v
            (chooseRequirement Z)
            Z :=

        satisfiesAllRequirements_of_mem
          S O v
          (Cfin.map chooseRequirement)
          Z
          hAll
          hChosenMem

      have hChosenFails :
          ¬ SatisfiesPersistenceRequirement
              S O v
              (chooseRequirement Z)
              Z :=

        (Classical.choose_spec (hFailure Z)).2

      exact
        hChosenFails hChosenSatisfied

/-
Local persistence situation.

At conjunction v, a local persistence situation consists of

  • a locally admissible relational configuration Z;
  • the finite collection of persistence requirements whose
    relational organization is being considered.

The requirements include both the persistent identity R and
its relational context Y.

This is a relational description only.  It introduces no
temporal ordering between situations.
-/
structure LocalPersistenceSituation
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O) where

  Z :
    LocalConfigurationSpace K O v

  /-
  A local persistence situation is, by definition, an admissible
  local relational realization.  This field is the formal counterpart
  of the manuscript condition

      Z ∈ A(I(v)).

  Admissibility is carried by the situation itself, independently of
  whether its persistence requirements are mutually satisfied.
  -/
  admissible :
    IsAdmissibleLocal K O v Z

  requirements :
    List (LocalPersistenceRequirement S O v)

/-
Semantic equality of individual persistence requirements.

The manuscript requirement is Q = (P,Y), where P is a persistence
class rather than a distinguished representative.  Lean stores a
representative R.  Two requirements therefore represent the same
physical requirement exactly when

  • their representatives belong to the same persistence class, and
  • their relational contexts are equal.

This prevents a mere change of representative R within [R]_p from
being counted as a change in persistence-requirement organization.
-/
def SamePersistenceRequirement
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Q₁ Q₂ : LocalPersistenceRequirement S O v) : Prop :=

  M.Persist Q₁.R Q₂.R ∧
  Q₁.Y = Q₂.Y

/-
Semantic equality is symmetric because persistence is an equivalence
relation and ordinary equality of relational contexts is symmetric.
-/
theorem samePersistenceRequirement_symm
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    {Q₁ Q₂ : LocalPersistenceRequirement S O v}
    (hSame : SamePersistenceRequirement S O v Q₁ Q₂) :

    SamePersistenceRequirement S O v Q₂ Q₁ := by

  exact
    ⟨M.persist_symm hSame.1,
     hSame.2.symm⟩

/-
Extensional equality of persistence-requirement families.

Two finite lists represent the same requirement family when every
requirement in either list has a semantically identical requirement
in the other list.  Ordering and duplicate entries therefore have no
physical significance, and persistence-equivalent representatives of
the same identity are also identified.
-/
def SameRequirementFamily
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Qs₁ Qs₂ :
      List (LocalPersistenceRequirement S O v)) : Prop :=

  (∀ Q₁ : LocalPersistenceRequirement S O v,
      Q₁ ∈ Qs₁ →
      ∃ Q₂ : LocalPersistenceRequirement S O v,
        Q₂ ∈ Qs₂ ∧
        SamePersistenceRequirement S O v Q₁ Q₂)
  ∧
  (∀ Q₂ : LocalPersistenceRequirement S O v,
      Q₂ ∈ Qs₂ →
      ∃ Q₁ : LocalPersistenceRequirement S O v,
        Q₁ ∈ Qs₁ ∧
        SamePersistenceRequirement S O v Q₁ Q₂)

/-
SameRequirementFamily is symmetric.
-/
theorem sameRequirementFamily_symm
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    {Qs₁ Qs₂ : List (LocalPersistenceRequirement S O v)}
    (hSame : SameRequirementFamily S O v Qs₁ Qs₂) :

    SameRequirementFamily S O v Qs₂ Qs₁ := by

  constructor

  · intro Q₂ hQ₂
    rcases hSame.2 Q₂ hQ₂ with ⟨Q₁, hQ₁, hReq⟩
    exact
      ⟨Q₁, hQ₁,
       samePersistenceRequirement_symm S O v hReq⟩

  · intro Q₁ hQ₁
    rcases hSame.1 Q₁ hQ₁ with ⟨Q₂, hQ₂, hReq⟩
    exact
      ⟨Q₂, hQ₂,
       samePersistenceRequirement_symm S O v hReq⟩

/-
Definition — Relational reorganization.

A relational reorganization occurs between two local persistence
situations when either

  • the local relational configuration changes, or
  • the relational organization represented by the persistence
    requirements changes.

Thus a mere reordering of the requirement List does not count
as reorganization.

Manuscript content:

    change in local relational configuration
        OR
    change in relational organization contributing to
    operational re-identification.

No temporal direction is implied by Situation₁ and Situation₂.
They are two relational realizations being compared.
-/
def RelationalReorganization
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Situation₁ Situation₂ :
      LocalPersistenceSituation S O v) : Prop :=

  Situation₁.Z ≠ Situation₂.Z
  ∨
  ¬ SameRequirementFamily
      S O v
      Situation₁.requirements
      Situation₂.requirements

/-
Persistence compatibility of a local situation.

A LocalPersistenceSituation is persistence-compatible when its
local configuration Z satisfies every persistence requirement
belonging to that situation.

Thus, for Situation with

    Z = Situation.Z
    Qs = Situation.requirements,

compatibility means

    Z ∈ ⋂_{Q ∈ Qs} U_{Q.R}(v; Q.Y).

This is a relational compatibility statement only.  It does not
assert that the situation follows another one temporally.
-/
def SituationPreservesRequirements
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Situation : LocalPersistenceSituation S O v) : Prop :=

  SatisfiesAllRequirements
    S O v
    Situation.requirements
    Situation.Z

/-
Satisfaction passes to a finite subfamily.

If every requirement occurring in Qs₂ also occurs in Qs₁,
then any configuration satisfying all requirements in Qs₁
also satisfies all requirements in Qs₂.
-/
theorem satisfiesAllRequirements_of_subfamily
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Qs₁ : List (LocalPersistenceRequirement S O v))
    (Z : LocalConfigurationSpace K O v)
    (hAll :
      SatisfiesAllRequirements S O v Qs₁ Z) :

    ∀ Qs₂ : List (LocalPersistenceRequirement S O v),
      (∀ Q : LocalPersistenceRequirement S O v,
        Q ∈ Qs₂ → Q ∈ Qs₁) →
      SatisfiesAllRequirements S O v Qs₂ Z := by

  intro Qs₂

  induction Qs₂ with

  | nil =>
      intro hSub
      trivial

  | cons Q rest ih =>

      intro hSub

      change
        SatisfiesPersistenceRequirement S O v Q Z ∧
        SatisfiesAllRequirements S O v rest Z

      constructor

      ·
        have hQin₁ :
            Q ∈ Qs₁ :=
          hSub Q
            (List.mem_cons.mpr (Or.inl rfl))

        exact
          satisfiesAllRequirements_of_mem
            S O v Qs₁ Z hAll hQin₁

      ·
        apply ih

        intro Q' hQrest

        exact
          hSub Q'
            (List.mem_cons.mpr (Or.inr hQrest))

/-
Satisfaction is invariant under semantic equality of one persistence
requirement.  The context is the same, while representative independence
of U_R(v;Y) identifies persistence-equivalent representatives.
-/
theorem satisfiesPersistenceRequirement_same
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Q₁ Q₂ : LocalPersistenceRequirement S O v)
    (Z : LocalConfigurationSpace K O v)
    (hSame : SamePersistenceRequirement S O v Q₁ Q₂) :

    SatisfiesPersistenceRequirement S O v Q₁ Z ↔
    SatisfiesPersistenceRequirement S O v Q₂ Z := by

  rcases hSame with ⟨hPersist, hY⟩

  unfold SatisfiesPersistenceRequirement

  simpa [hY] using
    (persistencePreservingLocal_rep_independent
      S O v Q₂.Y Z hPersist)

/-
Satisfaction passes from a family Qs₁ to any family Qs₂ whose
requirements are all semantically represented in Qs₁.
-/
theorem satisfiesAllRequirements_of_semanticSubfamily
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Qs₁ : List (LocalPersistenceRequirement S O v))
    (Z : LocalConfigurationSpace K O v)
    (hAll : SatisfiesAllRequirements S O v Qs₁ Z) :

    ∀ Qs₂ : List (LocalPersistenceRequirement S O v),
      (∀ Q₂ : LocalPersistenceRequirement S O v,
        Q₂ ∈ Qs₂ →
        ∃ Q₁ : LocalPersistenceRequirement S O v,
          Q₁ ∈ Qs₁ ∧
          SamePersistenceRequirement S O v Q₁ Q₂) →
      SatisfiesAllRequirements S O v Qs₂ Z := by

  intro Qs₂

  induction Qs₂ with

  | nil =>
      intro hSub
      trivial

  | cons Q₂ rest ih =>

      intro hSub

      change
        SatisfiesPersistenceRequirement S O v Q₂ Z ∧
        SatisfiesAllRequirements S O v rest Z

      constructor

      · rcases
          hSub Q₂
            (List.mem_cons.mpr (Or.inl rfl))
          with ⟨Q₁, hQ₁, hReq⟩

        have hSat₁ :
            SatisfiesPersistenceRequirement S O v Q₁ Z :=
          satisfiesAllRequirements_of_mem
            S O v Qs₁ Z hAll hQ₁

        exact
          (satisfiesPersistenceRequirement_same
            S O v Q₁ Q₂ Z hReq).mp hSat₁

      · apply ih

        intro Q' hQ'

        exact
          hSub Q'
            (List.mem_cons.mpr (Or.inr hQ'))

/-
Satisfaction is preserved under semantic equality of requirement
families.

If Qs₁ and Qs₂ represent the same persistence requirements, then any
local configuration satisfying Qs₁ also satisfies Qs₂.  Ordering,
duplicates, and a mere change of representative inside one persistence
class have no physical significance.
-/
theorem satisfiesAllRequirements_sameFamily
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Qs₁ Qs₂ :
      List (LocalPersistenceRequirement S O v))
    (Z : LocalConfigurationSpace K O v)
    (hSame :
      SameRequirementFamily S O v Qs₁ Qs₂)
    (hAll :
      SatisfiesAllRequirements S O v Qs₁ Z) :

    SatisfiesAllRequirements S O v Qs₂ Z := by

  exact
    satisfiesAllRequirements_of_semanticSubfamily
      S O v Qs₁ Z hAll Qs₂ hSame.2

/-
Lemma — Frustration requires relational reorganization.

Assume that the persistence-requirement family represented in
Situation₁ is structurally frustrated:

    no local configuration satisfies all of its requirements.

Assume also that Situation₂ preserves all of its persistence
requirements.

Then Situation₂ cannot have the same persistence-requirement
family as Situation₁.  Otherwise Situation₂.Z would provide a
configuration satisfying the frustrated family.

Therefore the relational organization contributing to
persistence must differ, and hence a RelationalReorganization
has occurred.

No temporal precedence between Situation₁ and Situation₂ is
assumed.  The theorem compares two relational realizations.
-/
theorem frustration_requires_reorganization
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Situation₁ Situation₂ :
      LocalPersistenceSituation S O v)
    (hFrustrated :
      FiniteLocalStructuralFrustration
        S O v Situation₁.requirements)
    (hPreserves₂ :
      SituationPreservesRequirements
        S O v Situation₂) :

    RelationalReorganization
      S O v Situation₁ Situation₂ := by

  /-
  It is enough to prove that the persistence-requirement
  organization cannot remain the same.
  -/
  apply Or.inr

  intro hSame

  /-
  Situation₂.Z satisfies Situation₂.requirements.
  Since the two requirement families are assumed extensionally
  equal, it must also satisfy Situation₁.requirements.
  -/
  have hSameReverse :
      SameRequirementFamily
        S O v
        Situation₂.requirements
        Situation₁.requirements :=

    sameRequirementFamily_symm
      S O v hSame

  have hSatisfiesFrustrated :
      SatisfiesAllRequirements
        S O v
        Situation₁.requirements
        Situation₂.Z :=

    satisfiesAllRequirements_sameFamily
      S O v
      Situation₂.requirements
      Situation₁.requirements
      Situation₂.Z
      hSameReverse
      hPreserves₂

  /-
  But frustration says that no such local configuration exists.
  -/
  exact
    hFrustrated.2
      ⟨Situation₂.Z, hSatisfiesFrustrated⟩

/-
Operational realization of relational reorganization.

A required relational reorganization is a statement about two
different relational situations.  To apply A2, we must separately
represent the admissible interactions through which that
reorganization is physically effected.

ReorganizationRealization S O v Situation₁ Situation₂ L means
that the finite interaction list L operationally realizes the
reorganization between those two situations.

The coherence fields state that an operational realization
really is a relational reorganization in the sense of Definition 16
and that mediation passes successively through the interactions in L.

This does not make locality an additional assumption.
Locality of each mediation step will be obtained from A2.
-/
structure ReorganizationMediationSemantics
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O) where

  ReorganizationRealization :
    LocalPersistenceSituation S O v →
    LocalPersistenceSituation S O v →
    List M.Interaction →
    Prop

  /-
  A sequence can realize a reorganization only between situations
  that actually differ in the sense of RelationalReorganization.

  This field ties the operational realization semantics back to
  Definition 16.  Without it, the abstract realization predicate
  could in principle hold even for two relationally unchanged
  situations.
  -/
  realization_requires_reorganization :
    ∀ (Situation₁ Situation₂ :
        LocalPersistenceSituation S O v)
      (L : List M.Interaction),

      ReorganizationRealization
        Situation₁ Situation₂ L →

      RelationalReorganization
        S O v Situation₁ Situation₂

  realization_is_mediation :
    ∀ (Situation₁ Situation₂ :
        LocalPersistenceSituation S O v)
      (L : List M.Interaction),

      ReorganizationRealization
        Situation₁ Situation₂ L →

      MediationChain M L

/-
Any interaction realization of a relational reorganization is
locally mediated.

The realization semantics gives a MediationChain.
A2 then implies that every successive mediation step shares
relational participation, i.e. the realization is a
DirectMediationChain.

This is the formal separation:

    frustration + continued persistence
        → reorganization required

while

    reorganization realized by admissible interaction + A2
        → locally mediated realization.
-/
theorem reorganizationRealization_is_locallyMediated
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Rsem : ReorganizationMediationSemantics S O v)
    (Situation₁ Situation₂ :
      LocalPersistenceSituation S O v)
    (L : List M.Interaction)
    (hRealizes :
      Rsem.ReorganizationRealization
        Situation₁ Situation₂ L) :

    DirectMediationChain M L := by

  have hMediation :
      MediationChain M L :=
    Rsem.realization_is_mediation
      Situation₁ Situation₂ L hRealizes

  exact
    mediationChain_is_direct M hMediation

/-
Theorem — Frustration, persistence, and local reorganization.

Suppose:

  • Situation₁ carries a structurally frustrated family of
    persistence requirements;

  • Situation₂ nevertheless preserves its persistence
    requirements;

  • the resulting relational reorganization is physically
    realized by a finite interaction list L.

Then:

  1. a relational reorganization between Situation₁ and
     Situation₂ is required;

  2. its interaction realization L is locally mediated.

The two conclusions have distinct logical origins:

    frustration + persistence
        → reorganization required;

    A2 + interaction realization
        → local mediation.

This separation prevents locality from being smuggled into
the frustration argument itself.
-/
theorem frustration_persistence_requires_localReorganization
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Rsem : ReorganizationMediationSemantics S O v)
    (Situation₁ Situation₂ :
      LocalPersistenceSituation S O v)
    (L : List M.Interaction)
    (hFrustrated :
      FiniteLocalStructuralFrustration
        S O v Situation₁.requirements)
    (hPreserves₂ :
      SituationPreservesRequirements
        S O v Situation₂)
    (hRealizes :
      Rsem.ReorganizationRealization
        Situation₁ Situation₂ L) :

    RelationalReorganization
        S O v Situation₁ Situation₂
    ∧
    DirectMediationChain M L := by

  constructor

  · exact
      frustration_requires_reorganization
        S O v
        Situation₁ Situation₂
        hFrustrated
        hPreserves₂

  · exact
      reorganizationRealization_is_locallyMediated
        S O v
        Rsem
        Situation₁ Situation₂
        L
        hRealizes

/-
One episode of recurrent local structural frustration.

An episode records:

  • the local conjunction v at which frustration occurs;
  • the relational situation carrying the frustrated requirements;
  • a second situation in which the contributing persistent
    requirements continue to be satisfied;
  • a finite interaction realization of the required
    reorganization.

The episode index used later is only a mathematical label for
successive recurrence.  It is not a primitive physical time
parameter.
-/
structure FrustrationReorganizationEpisode
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (Rsem :
      ∀ v : LocalRelationalConjunction C O,
        ReorganizationMediationSemantics S O v) where

  v :
    LocalRelationalConjunction C O

  Situation₁ :
    LocalPersistenceSituation S O v

  Situation₂ :
    LocalPersistenceSituation S O v

  interactions :
    List M.Interaction

  frustrated :
    FiniteLocalStructuralFrustration
      S O v Situation₁.requirements

  continuedPersistence :
    SituationPreservesRequirements
      S O v Situation₂

  realizes :
    (Rsem v).ReorganizationRealization
      Situation₁ Situation₂ interactions

/-
Recurrent local structural frustration.

A recurrent process is represented by one frustration-
reorganization episode for every natural-number index.

Nat is used only to enumerate recurrent occurrences.  No
duration, temporal metric, or physical time coordinate is
introduced.
-/
def RecurrentStructuralFrustration
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (Rsem :
      ∀ v : LocalRelationalConjunction C O,
        ReorganizationMediationSemantics S O v) :=

  Nat → FrustrationReorganizationEpisode S O Rsem

/-
Theorem — Continual reorganization under recurrent frustration.

If structural frustration recurs indefinitely, and each recurrence
is accompanied by continued persistence together with an admissible
interaction realization of the required reorganization, then at
every recurrence:

  • relational reorganization is required;
  • its interaction realization is locally mediated.

The natural-number index n merely labels recurrent episodes.
It is not a physical time variable.

Thus "continual" means that the requirement for reorganization
recurs without a terminal episode, not that a continuous temporal
dynamics has been assumed.
-/
theorem recurrentFrustration_requires_continualReorganization
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (Rsem :
      ∀ v : LocalRelationalConjunction C O,
        ReorganizationMediationSemantics S O v)
    (Episodes :
      RecurrentStructuralFrustration S O Rsem) :

    ∀ n : Nat,

      RelationalReorganization
        S O
        (Episodes n).v
        (Episodes n).Situation₁
        (Episodes n).Situation₂

      ∧

      DirectMediationChain
        M
        (Episodes n).interactions := by

  intro n

  exact
    frustration_persistence_requires_localReorganization
      S
      O
      (Episodes n).v
      (Rsem (Episodes n).v)
      (Episodes n).Situation₁
      (Episodes n).Situation₂
      (Episodes n).interactions
      (Episodes n).frustrated
      (Episodes n).continuedPersistence
      (Episodes n).realizes
