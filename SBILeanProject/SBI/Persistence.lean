import SBILeanProject.SBI.Operational

set_option autoImplicit false

namespace SBI

/-
S2 — Operational persistence.

The operational configuration structure has already been
established.

We now connect configurations to the persistent-identity
relation introduced by A3.

No configuration-change relation, temporal ordering, or
dynamical law is introduced at this stage.
-/

/-
Persistence context.

Occurs O R X means that relational organization R occurs as
a realization within global configuration X at observer O's
operational resolution.

This is the bridge between

    R ∈ 𝓡

from the primitive relational layer and

    X ∈ 𝓒

from the operational configuration layer.

It introduces no claim that R is uniquely represented by X,
or that X contains only one relational organization.
-/
structure PersistenceContext
    {M : SBI}
    {C : NetworkRealizationContext M}
    (K : OperationalContext C) where

  Occurs :
    (O : Observer M) →
    M.Org →
    Configuration K O →
    Prop
  /-
  ReidentificationDistinction O R₁ R₂ D means that D is the
  operational distinction by which realizations R₁ and R₂ are
  identified as realizations of the same persistent structure.

  Whether D is observer-accessible is stated separately.
  -/
  ReidentificationDistinction :
    (O : Observer M) →
    M.Org →
    M.Org →
    C.Distinction →
    Prop

/-
Presence of a persistent identity class in a configuration.

The persistence relation Persist is an equivalence relation.
Therefore a persistent identity may be represented by any
relational organization R belonging to that equivalence class.

PersistenceClassPresent P O X R means:

    some realization R' occurs in X
    and
    R' ~ₚ R.

Manuscript content:

    [R]ₚ ∈ P(X)

iff some realization belonging to [R]ₚ occurs in X.

At this stage R is only a representative of the class [R]ₚ.
No quotient construction is required.
-/
def PersistenceClassPresent
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (P : PersistenceContext K)
    (O : Observer M)
    (X : Configuration K O)
    (R : M.Org) : Prop :=

  ∃ R' : M.Org,
    P.Occurs O R' X ∧
    M.Persist R' R

/-
Presence of a persistent identity class is independent of
the chosen representative.

If

    R₁ ~ₚ R₂,

then

    [R₁]ₚ is present in X
        ↔
    [R₂]ₚ is present in X.

This confirms that PersistenceClassPresent really represents
membership of an equivalence class rather than membership of
one particular relational realization.
-/
theorem persistenceClassPresent_rep_independent
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (P : PersistenceContext K)
    (O : Observer M)
    (X : Configuration K O)
    {R₁ R₂ : M.Org}
    (hPersist : M.Persist R₁ R₂) :

    PersistenceClassPresent P O X R₁ ↔
    PersistenceClassPresent P O X R₂ := by

  constructor

  · intro hPresent

    rcases hPresent with
      ⟨R', hOccurs, hR'R₁⟩

    have hR'R₂ :
        M.Persist R' R₂ :=
      M.persist_trans hR'R₁ hPersist

    exact ⟨R', hOccurs, hR'R₂⟩

  · intro hPresent

    rcases hPresent with
      ⟨R', hOccurs, hR'R₂⟩

    have hR₂R₁ :
        M.Persist R₂ R₁ :=
      M.persist_symm hPersist

    have hR'R₁ :
        M.Persist R' R₁ :=
      M.persist_trans hR'R₂ hR₂R₁

    exact ⟨R', hOccurs, hR'R₁⟩

/-
Persistent structures present in a configuration.

Manuscript notation:

    P(X) = { [R]ₚ :
             some realization belonging to [R]ₚ occurs in X }.

Because persistence classes are represented by arbitrary
representatives R, P(X) is formalized as a predicate on M.Org.

Representative independence has already been proved above, so
this predicate depends only on the persistence class [R]ₚ.
-/
def PersistentStructuresPresent
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (P : PersistenceContext K)
    (O : Observer M)
    (X : Configuration K O) :
    M.Org → Prop :=

  fun R =>
    PersistenceClassPresent P O X R

/-
Operational re-identification of a persistent structure.

The persistence class represented by R is operationally
re-identified across X₁ and X₂ when there exist realizations

    R₁ occurring in X₁
    R₂ occurring in X₂

such that

    R₁ ~ₚ R
    R₂ ~ₚ R,

and there is an observer-accessible relational distinction D
which distinguishes R₁ and R₂ as realizations of the same
persistent structure.

This is stronger than merely requiring [R]ₚ to be present in
both configurations.
-/
def OperationallyReidentified
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (P : PersistenceContext K)
    (O : Observer M)
    (X₁ X₂ : Configuration K O)
    (R : M.Org) : Prop :=

  ∃ (R₁ R₂ : M.Org)
    (D : C.Distinction),

    P.Occurs O R₁ X₁ ∧
    P.Occurs O R₂ X₂ ∧
    M.Persist R₁ R ∧
    M.Persist R₂ R ∧
    C.AccessibleDistinction O D ∧
    P.ReidentificationDistinction O R₁ R₂ D

/-
Operational re-identification is independent of the chosen
representative of the persistence class.
-/
theorem operationallyReidentified_rep_independent
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (P : PersistenceContext K)
    (O : Observer M)
    (X₁ X₂ : Configuration K O)
    {R₁ R₂ : M.Org}
    (hPersist : M.Persist R₁ R₂) :

    OperationallyReidentified P O X₁ X₂ R₁ ↔
    OperationallyReidentified P O X₁ X₂ R₂ := by

  constructor

  · intro hReidentified

    rcases hReidentified with
      ⟨Q₁, Q₂, D,
        hOccurs₁, hOccurs₂,
        hQ₁R₁, hQ₂R₁,
        hAccessible, hDistinction⟩

    have hQ₁R₂ :
        M.Persist Q₁ R₂ :=
      M.persist_trans hQ₁R₁ hPersist

    have hQ₂R₂ :
        M.Persist Q₂ R₂ :=
      M.persist_trans hQ₂R₁ hPersist

    exact
      ⟨Q₁, Q₂, D,
        hOccurs₁, hOccurs₂,
        hQ₁R₂, hQ₂R₂,
        hAccessible, hDistinction⟩

  · intro hReidentified

    rcases hReidentified with
      ⟨Q₁, Q₂, D,
        hOccurs₁, hOccurs₂,
        hQ₁R₂, hQ₂R₂,
        hAccessible, hDistinction⟩

    have hR₂R₁ :
        M.Persist R₂ R₁ :=
      M.persist_symm hPersist

    have hQ₁R₁ :
        M.Persist Q₁ R₁ :=
      M.persist_trans hQ₁R₂ hR₂R₁

    have hQ₂R₁ :
        M.Persist Q₂ R₁ :=
      M.persist_trans hQ₂R₂ hR₂R₁

    exact
      ⟨Q₁, Q₂, D,
        hOccurs₁, hOccurs₂,
        hQ₁R₁, hQ₂R₁,
        hAccessible, hDistinction⟩

/-
Operational support witness.

An operational support witness for persistent identity [R]ₚ
across configurations X₁ and X₂ consists of

  • realizations R₁ and R₂ occurring in X₁ and X₂;
  • an accessible distinction D by which they are operationally
    re-identified as the same persistent structure;
  • one specific finite FOA witness L establishing D.

Thus the SAME finite interaction list L carries the operational
distinction sufficient to re-identify the persistent structure.

The corresponding local relational conjunctions and direct
relations are obtained from the network representation of L.
-/
structure OperationalSupport
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (P : PersistenceContext K)
    (O : Observer M)
    (X₁ X₂ : Configuration K O)
    (R : M.Org) where

  R₁ : M.Org
  R₂ : M.Org

  D : C.Distinction

  interactions : List M.Interaction

  occurs₁ :
    P.Occurs O R₁ X₁

  occurs₂ :
    P.Occurs O R₂ X₂

  persist₁ :
    M.Persist R₁ R

  persist₂ :
    M.Persist R₂ R

  accessible :
    C.AccessibleDistinction O D

  reidentifies :
    P.ReidentificationDistinction O R₁ R₂ D

  foaWitness :
    FOAWitness
      C.toNetworkContext
      O D interactions


/-
Finite operational support exists.

If persistent identity [R]ₚ is operationally re-identified
across X₁ and X₂, then derived FOA supplies a finite operational
support for that re-identification.

OperationallyReidentified supplies:

  • realizations R₁ and R₂;
  • their membership in the persistence class [R]ₚ;
  • an observer-accessible re-identification distinction D.

FOA then supplies one particular finite interaction list L
establishing that same accessible distinction D.

Together these data form an OperationalSupport.

The result is stated using Nonempty:

    Nonempty (OperationalSupport ...)

which simply means that at least one such support exists.
-/
theorem operationallyReidentified_has_finiteSupport
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (P : PersistenceContext K)
    (hFOA : FOA C.toNetworkContext)
    (O : Observer M)
    (X₁ X₂ : Configuration K O)
    (R : M.Org)
    (hReidentified :
      OperationallyReidentified P O X₁ X₂ R) :

    Nonempty (OperationalSupport P O X₁ X₂ R) := by

  rcases hReidentified with
    ⟨R₁, R₂, D,
      hOccurs₁,
      hOccurs₂,
      hPersist₁,
      hPersist₂,
      hAccessible,
      hReidentifies⟩

  rcases foa_supplies_witness
    C.toNetworkContext
    hFOA
    O D
    hAccessible with
    ⟨L, hFOAWitness⟩

  exact ⟨{
    R₁ := R₁
    R₂ := R₂
    D := D
    interactions := L

    occurs₁ := hOccurs₁
    occurs₂ := hOccurs₂

    persist₁ := hPersist₁
    persist₂ := hPersist₂

    accessible := hAccessible
    reidentifies := hReidentifies

    foaWitness := hFOAWitness
  }⟩
/-
Finite conjunction support of an OperationalSupport.

Every elementary interaction in the finite operational support
has a corresponding local relational conjunction in the
observer's incidence-network representation.

For

    interactions = [a₁, ..., aₙ]

we obtain

    [vₐ₁, ..., vₐₙ],

where

    vₐ = InteractionConjunction C O a.

Because the interaction support is a List, the conjunction
support is automatically finite.
-/
def supportConjunctions
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    {O : Observer M}
    {X₁ X₂ : Configuration K O}
    {R : M.Org}
    (S : OperationalSupport P O X₁ X₂ R) :
    List (LocalRelationalConjunction C O) :=

  S.interactions.map
    (InteractionConjunction C O)

/-
Every interaction in an OperationalSupport contributes its
corresponding local relational conjunction to the finite
conjunction support.

If

    a ∈ S.interactions,

then

    InteractionConjunction C O a
        ∈ supportConjunctions S.

This is the direct network-level image of membership in the
finite interaction witness.
-/
theorem interaction_mem_implies_conjunction_mem
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    {O : Observer M}
    {X₁ X₂ : Configuration K O}
    {R : M.Org}
    (S : OperationalSupport P O X₁ X₂ R)
    {a : M.Interaction}
    (ha : a ∈ S.interactions) :

    InteractionConjunction C O a
      ∈ supportConjunctions S := by

  unfold supportConjunctions

  apply List.mem_map.mpr

  exact ⟨a, ha, rfl⟩

/-
Direct relations participating in an OperationalSupport.

A DirectRelation e belongs to the support when it participates
in at least one elementary interaction contained in the finite
support witness.

Thus e is a support relation when

    ∃ a ∈ S.interactions,
      SigmaOp a e.val.

Because e is already a DirectRelation, observer accessibility
is built into its type.

This is the edge-level counterpart of supportConjunctions.
-/
def IsSupportDirectRelation
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    {O : Observer M}
    {X₁ X₂ : Configuration K O}
    {R : M.Org}
    (S : OperationalSupport P O X₁ X₂ R)
    (e : DirectRelation C O) : Prop :=

  ∃ a : M.Interaction,
    a ∈ S.interactions ∧
    M.SigmaOp a e.val

/-
Finite direct relations carried by a finite interaction list.

Suppose L is a finite list of elementary interactions and, for
every a ∈ L, there is a finite exhaustive list P of all
operationally resolved participations in a.

Then all observer-accessible DirectRelations participating
operationally in some interaction of L are contained in one
finite list.  The finiteness therefore comes from the same
SigmaOp structure supplied by A2 and packaged by derived FOA.

The proof proceeds recursively through L and concatenates the
finite direct-relation lists obtained for each interaction.
-/
theorem finiteDirectRelations_of_interactionList
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (L : List M.Interaction)
    (hFinite :
      ∀ a : M.Interaction,
        a ∈ L →
        ∃ P : List M.Participation,
          ∀ p : M.Participation,
            M.SigmaOp a p → p ∈ P) :

    ∃ Efin : List (DirectRelation C O),
      ∀ e : DirectRelation C O,
        (∃ a : M.Interaction,
          a ∈ L ∧
          M.SigmaOp a e.val) →
        e ∈ Efin := by

  induction L with

  | nil =>
      refine ⟨[], ?_⟩

      intro e hSupport

      rcases hSupport with
        ⟨a, ha, hSigma⟩

      simp at ha

  | cons a rest ih =>

      have haFinite :
          ∃ P : List M.Participation,
            ∀ p : M.Participation,
              M.SigmaOp a p → p ∈ P :=
        hFinite a (by simp)

      rcases haFinite with
        ⟨P, hP⟩

      have hRestFinite :
          ∀ b : M.Interaction,
            b ∈ rest →
            ∃ Q : List M.Participation,
              ∀ p : M.Participation,
                M.SigmaOp b p → p ∈ Q := by

        intro b hb

        exact hFinite b (by
          simp [hb])

      rcases ih hRestFinite with
        ⟨Erest, hErest⟩

      refine
        ⟨directRelationsInList C O P ++ Erest, ?_⟩

      intro e hSupport

      rcases hSupport with
        ⟨b, hb, hSigma⟩

      rcases List.mem_cons.mp hb with
        hHead | hTail

      · subst b

        have hMemP :
            e.val ∈ P :=
          hP e.val hSigma

        have hMemHead :
            e ∈ directRelationsInList C O P :=
          directRelation_mem_directRelationsInList
            C O e hMemP

        apply List.mem_append.mpr
        exact Or.inl hMemHead

      ·
        have hMemRest :
          e ∈ Erest :=
        hErest e ⟨b, hTail, hSigma⟩
        apply List.mem_append.mpr
        exact Or.inr hMemRest

/-
The direct-relation part of an OperationalSupport is finite.

The FOAWitness carried by S supplies finite operational participation data
for every interaction in S.interactions. The preceding lemma
therefore produces one finite exhaustive list containing every
DirectRelation participating in the support.

This completes the edge-level part of the manuscript's finite
operational support statement.
-/
theorem supportDirectRelations_is_finite
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    {O : Observer M}
    {X₁ X₂ : Configuration K O}
    {R : M.Org}
    (S : OperationalSupport P O X₁ X₂ R) :

    ∃ Efin : List (DirectRelation C O),
      ∀ e : DirectRelation C O,
        IsSupportDirectRelation S e →
        e ∈ Efin := by

  rcases S.foaWitness with
    ⟨hEstablishes, hFinite⟩

  have hParticipationFinite :
      ∀ a : M.Interaction,
        a ∈ S.interactions →
        ∃ P : List M.Participation,
          ∀ p : M.Participation,
            M.SigmaOp a p → p ∈ P := by

    intro a ha

    exact (hFinite a ha).1

  exact
    finiteDirectRelations_of_interactionList
      C O
      S.interactions
      hParticipationFinite

  /-
Proposition — Finite operational support.

If a persistent identity [R]ₚ is operationally re-identified
across configurations X₁ and X₂, then within the observer-accessible
operational domain there exists a support whose network
realization is finite.

More explicitly, there exist

  • an OperationalSupport S;
  • a finite list of local relational conjunctions,
        supportConjunctions S;
  • a finite list Efin of direct relations;

such that every interaction in the support contributes its
corresponding conjunction, and every direct relation participating
in the support belongs to Efin.

This is the network-language form of the manuscript statement
that operational support may be chosen finite.
-/
theorem operationallyReidentified_has_finiteNetworkSupport
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (P : PersistenceContext K)
    (hFOA : FOA C.toNetworkContext)
    (O : Observer M)
    (X₁ X₂ : Configuration K O)
    (R : M.Org)
    (hReidentified :
      OperationallyReidentified P O X₁ X₂ R) :

    ∃ S : OperationalSupport P O X₁ X₂ R,
      ∃ Efin : List (DirectRelation C O),

        (∀ a : M.Interaction,
          a ∈ S.interactions →
          InteractionConjunction C O a
            ∈ supportConjunctions S)
        ∧

        (∀ e : DirectRelation C O,
          IsSupportDirectRelation S e →
          e ∈ Efin) := by

  rcases
    operationallyReidentified_has_finiteSupport
      P hFOA O X₁ X₂ R hReidentified with
    ⟨S⟩

  rcases supportDirectRelations_is_finite S with
    ⟨Efin, hEfin⟩

  refine ⟨S, Efin, ?_, hEfin⟩

  intro a ha

  exact
    interaction_mem_implies_conjunction_mem
      S ha
end SBI
