import SBILeanProject.SBI.Network

set_option autoImplicit false

namespace SBI

/-
S2 — Operational structure.

The incidence-network representation has now been derived.

Only at this stage do we introduce relational configurations
and local admissibility.

No temporal parameter, dynamical law, configuration-change
relation, geometry, or intrinsic state of a vertex is assumed.
-/

/-
Incident set of a local relational conjunction.

For a conjunction v, I(v) is the collection of direct relations
incident on v.

Manuscript notation:

    I(v) = { e ∈ E : (e,v) ∈ ι }.

Because we are not using Set machinery yet, I(v) is represented
as a predicate on DirectRelation:

    IncidentSet C O v e

means

    e ∈ I(v).

This definition introduces no new physical structure; it is
simply the incidence relation already present in ObserverNetwork.
-/
def IncidentSet
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (v : LocalRelationalConjunction C O) :
    DirectRelation C O → Prop :=

  fun e => Incident C O e v
/-
Operational configuration context.

Only after the incidence-network representation has been
established do we introduce configuration language.

For each observer O:

  • GlobalConfig O is the type of admissible global relational
    configurations represented at the operational resolution;

  • LocalConfig O v is the type of operationally distinguishable
    configurations on the incident set I(v);

  • Restrict O X v is the restriction

        X|_{I(v)}

    of global configuration X to the incident relations of v;

  • AdmissibleLocal O v Y says that local configuration Y belongs
    to the admissible subset A(I(v)).

The context introduces representational vocabulary only.
No temporal ordering, evolution law, transition relation, or
configuration-change operation is introduced here.
-/
structure OperationalContext
    {M : SBI}
    (C : NetworkRealizationContext M) where

  /-
  Manuscript notation: 𝓒.

  We write GlobalConfig O because the network realization already
  has observer-relative operational resolution.
  -/
  GlobalConfig :
    Observer M → Type

  /-
  Manuscript notation: 𝓒(I(v)).

  LocalConfig O v contains all operationally distinguishable local
  configurations at the incident set I(v), whether or not they arise
  as restrictions of global admissible configurations.
  -/
  LocalConfig :
    (O : Observer M) →
    LocalRelationalConjunction C O →
    Type

  /-
  Restriction of a global configuration to I(v):

      X ↦ X|_{I(v)}.
  -/
  Restrict :
    (O : Observer M) →
    GlobalConfig O →
    (v : LocalRelationalConjunction C O) →
    LocalConfig O v

  /-
  Manuscript notation:

      𝓐(I(v)) ⊆ 𝓒(I(v)).

  Since LocalConfig O v already represents 𝓒(I(v)),
  the admissible subset is represented by a predicate.
  -/
  AdmissibleLocal :
    (O : Observer M) →
    (v : LocalRelationalConjunction C O) →
    LocalConfig O v →
    Prop

   /-
  Every admissible global configuration restricts to an
  admissible local configuration.

  Manuscript statement:

      X ∈ 𝓒
          ⇒
      X|_{I(v)} ∈ 𝓐(I(v)).

  Since GlobalConfig already denotes admissible global
  configurations, no separate global admissibility premise
  is required.
  -/
  restriction_admissible :
    ∀ (O : Observer M)
      (X : GlobalConfig O)
      (v : LocalRelationalConjunction C O),
      AdmissibleLocal O v (Restrict O X v)

  /-
Readable names for the configuration objects introduced above.

These are only notational/formal wrappers around OperationalContext.
They introduce no additional structure.
-/

/-
Global admissible relational configuration.

Manuscript notation:

    X ∈ 𝓒.
-/
abbrev Configuration
    {M : SBI}
    {C : NetworkRealizationContext M}
    (K : OperationalContext C)
    (O : Observer M) :=
  K.GlobalConfig O

/-
Local configuration space at I(v).

Manuscript notation:

    𝓒(I(v)).

This is the full space of operationally distinguishable local
configurations, not merely those obtained by restricting a
global admissible configuration.
-/
abbrev LocalConfigurationSpace
    {M : SBI}
    {C : NetworkRealizationContext M}
    (K : OperationalContext C)
    (O : Observer M)
    (v : LocalRelationalConjunction C O) :=
  K.LocalConfig O v

/-
Restriction of a global configuration X to the incident set I(v).

Manuscript notation:

    X|_{I(v)}.
-/
def LocalRestriction
    {M : SBI}
    {C : NetworkRealizationContext M}
    (K : OperationalContext C)
    (O : Observer M)
    (X : Configuration K O)
    (v : LocalRelationalConjunction C O) :
    LocalConfigurationSpace K O v :=

  K.Restrict O X v

/-
Membership in the admissible local subset.

Manuscript notation:

    Y ∈ 𝓐(I(v)).

Because 𝓐(I(v)) is a subset of 𝓒(I(v)), it is represented
as a predicate on LocalConfigurationSpace.
-/
def IsAdmissibleLocal
    {M : SBI}
    {C : NetworkRealizationContext M}
    (K : OperationalContext C)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Y : LocalConfigurationSpace K O v) : Prop :=

  K.AdmissibleLocal O v Y

/-
Every admissible global configuration induces an admissible
local configuration.

Manuscript statement:

    X ∈ 𝓒
        ⇒
    X|_{I(v)} ∈ 𝓐(I(v)).

Because Configuration K O is already the type of admissible
global configurations, the premise X ∈ 𝓒 is encoded by the
type of X itself.
-/
theorem localRestriction_is_admissible
    {M : SBI}
    {C : NetworkRealizationContext M}
    (K : OperationalContext C)
    (O : Observer M)
    (X : Configuration K O)
    (v : LocalRelationalConjunction C O) :

    IsAdmissibleLocal
      K O v
      (LocalRestriction K O X v) := by

  exact K.restriction_admissible O X v

/-
Global realizability of a local configuration.

A local configuration Y at I(v) is globally realizable when
there exists some global admissible configuration X whose
restriction to I(v) is exactly Y.

Manuscript content:

    Y is globally realizable
      ↔
    ∃ X ∈ 𝓒 such that X|_{I(v)} = Y.

Because Configuration K O already denotes the admissible global
configuration type, no separate membership predicate for X is
required.
-/
def GloballyRealizableLocal
    {M : SBI}
    {C : NetworkRealizationContext M}
    (K : OperationalContext C)
    (O : Observer M)
    (v : LocalRelationalConjunction C O)
    (Y : LocalConfigurationSpace K O v) : Prop :=

  ∃ X : Configuration K O,
    LocalRestriction K O X v = Y


/-
A particular finite operational witness satisfying the
local finiteness conditions packaged by FOA.

FOA is now derived in NetworkCore from the operational meaning of
observer accessibility together with A2.  FOAWitness does not add
another assumption; it records the data carried by one particular
finite establishing list L.

This distinction is important: all properties below refer
to the SAME witness L.
-/
def FOAWitness
    {M : SBI}
    (C : NetworkContext M)
    (O : Observer M)
    (D : C.Distinction)
    (L : List M.Interaction) : Prop :=

  C.Establishes O D L ∧
  ∀ a : M.Interaction,
    a ∈ L →
      (∃ P : List M.Participation,
        ∀ p : M.Participation,
          M.SigmaOp a p → p ∈ P)
      ∧
      (∃ Ω : List (C.Alternative a),
        ∀ ω : C.Alternative a,
          ω ∈ Ω)

/-
An operationally witnessed local relational conjunction.

A conjunction v belongs to the observer-accessible operational domain
when there exist

  • an elementary interaction a realizing v,
  • an accessible distinction D,
  • one specific FOA witness L for D,

such that a occurs in that same witness L.

This is a property of one conjunction v, rather than a global
assumption that every mathematically definable conjunction is
operationally realized.
-/
def IsOperationalConjunction
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (v : LocalRelationalConjunction C O) : Prop :=

  ∃ (a : M.Interaction)
    (D : C.Distinction)
    (L : List M.Interaction),

    (∀ e : DirectRelation C O,
      IncidentSet C O v e ↔
      M.SigmaOp a e.val)
    ∧
    C.AccessibleDistinction O D
    ∧
    FOAWitness C.toNetworkContext O D L
    ∧
    a ∈ L

/-
The local relational conjunctions belonging to the
observer-accessible operational domain.

An OperationalConjunction contains

  • a local relational conjunction v;
  • proof that v occurs in a specific finite operational witness.

This does not claim that every underlying conjunction is
operationally accessible.
-/
def OperationalConjunction
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M) :=
  {v : LocalRelationalConjunction C O //
    IsOperationalConjunction C O v}

/-
Local finiteness on the observer-accessible operational domain.

For every OperationalConjunction v:

  • its incident direct relations admit a finite exhaustive list;
  • its local configuration space admits a finite exhaustive list.

This is the precise operational form of

    |I(v)| < ∞
    and
    |C(I(v))| < ∞.

No claim is made that every mathematically definable conjunction
of the underlying relational structure is finite.
-/
def OperationallyLocallyFinite
    {M : SBI}
    {C : NetworkRealizationContext M}
    (K : OperationalContext C)
    (O : Observer M) : Prop :=

  ∀ v : OperationalConjunction C O,

    (∃ Efin : List (DirectRelation C O),
      ∀ e : DirectRelation C O,
        IncidentSet C O v.val e →
        e ∈ Efin)
    ∧

    (∃ Cfin : List (LocalConfigurationSpace K O v.val),
      ∀ Y : LocalConfigurationSpace K O v.val,
        Y ∈ Cfin)


/-
Derived FOA supplies a concrete operational witness for every accessible
operational distinction.

The derived FOA proposition states existentially that such a finite
witness exists.  FOAWitness merely packages the properties of one
particular witness list L.

Thus FOAWitness introduces no additional physical assumption.
-/
theorem foa_supplies_witness
    {M : SBI}
    (C : NetworkContext M)
    (hFOA : FOA C)
    (O : Observer M)
    (D : C.Distinction)
    (hAccessible : C.AccessibleDistinction O D) :

    ∃ L : List M.Interaction,
      FOAWitness C O D L := by

  rcases hFOA O D hAccessible with
    ⟨L, hEstablishes, hFinite⟩

  exact ⟨L, hEstablishes, hFinite⟩

/-
Extract the direct relations from a finite list of primitive
relational participations.

For each participation p in P:

  • if p satisfies IsDirectRelation C O p, retain it as an element
    of DirectRelation C O;

  • otherwise omit it.

This uses classical decidability only as mathematical bookkeeping:
we are proving that a finite containing list exists, not specifying
a physically executable decision procedure.
-/
noncomputable def directRelationsInList
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (P : List M.Participation) :
    List (DirectRelation C O) := by

  classical

  induction P with

  | nil =>
      exact []

  | cons p ps ih =>
      by_cases h : IsDirectRelation C O p

      · exact ⟨p, h⟩ :: ih

      · exact ih

/-
A DirectRelation whose underlying participation occurs in P
also occurs in the list obtained by extracting all direct
relations from P.

This is the technical bridge from a finite list of operationally
resolved participations supplied by derived FOA to a finite list
of network edges.
-/
theorem directRelation_mem_directRelationsInList
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (e : DirectRelation C O)
    {P : List M.Participation}
    (hMem : e.val ∈ P) :

    e ∈ directRelationsInList C O P := by

  classical

  induction P with

  | nil =>
      simp at hMem

  | cons p ps ih =>

      rcases List.mem_cons.mp hMem with hHead | hTail

      ·
        /-
        The head p is the underlying participation of e.
        -/
        subst p

        have hDirect :
            IsDirectRelation C O e.val :=
          e.property

        simp only [directRelationsInList, dif_pos hDirect]

        exact List.mem_cons.mpr
          (Or.inl (Subtype.ext (by rfl)))

      ·
        /-
        The underlying participation of e occurs in the tail.
        -/
        have hInTail :
            e ∈ directRelationsInList C O ps :=
          ih hTail

        by_cases hDirect :
            IsDirectRelation C O p

        ·
          simp only [directRelationsInList, dif_pos hDirect]

          exact List.mem_cons.mpr
            (Or.inr hInTail)

        ·
          simp only [directRelationsInList, dif_neg hDirect]

          exact hInTail

/-
Finite incident set for an operational conjunction.

An OperationalConjunction v already carries proof that it belongs
to the observer-accessible operational domain. Therefore no global
assumption that every LocalRelationalConjunction is witnessed
is required.

For the specific conjunction v:

  • v.property supplies an interaction a realizing v;
  • a occurs in one specific FOA witness L;
  • that same witness supplies a finite exhaustive list P of
    operationally resolved participations for a;
  • every incident DirectRelation has its underlying participation
    in P.

Hence I(v) is finite at operational resolution.
-/
theorem operationalConjunction_incidentSet_is_finite
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (v : OperationalConjunction C O) :

    ∃ Efin : List (DirectRelation C O),
      ∀ e : DirectRelation C O,
        IncidentSet C O v.val e →
        e ∈ Efin := by

  rcases v.property with
    ⟨a, D, L,
      hRealizes,
      hAccessible,
      hFOAWitness,
      haL⟩

  rcases hFOAWitness with
    ⟨hEstablishes, hFinite⟩

  have hFiniteAtA :=
    hFinite a haL

  rcases hFiniteAtA.1 with
    ⟨P, hP⟩

  refine
    ⟨directRelationsInList C O P, ?_⟩

  intro e hIncident

  have hSigmaOp :
      M.SigmaOp a e.val :=
    (hRealizes e).1 hIncident

  have hMemP :
      e.val ∈ P :=
    hP e.val hSigmaOp

  exact
    directRelation_mem_directRelationsInList
      C O e hMemP


/-
Local configurations are represented by interaction alternatives.

If an elementary interaction a realizes the local relational
conjunction v, then every operationally distinguishable local
configuration in C(I(v)) is represented by some operational
alternative of a.

We express this by requiring a surjective representation map

    Alternative a → LocalConfigurationSpace K O v.

Surjectivity is all that is needed for finiteness: different
alternatives may represent the same local configuration.

This formalizes the manuscript statement that the finitely many
operationally distinguishable alternatives of the interaction
are represented by the local relational configurations in C(I(v)).
-/
def LocalConfigurationsRepresentedByAlternatives
    {M : SBI}
    {C : NetworkRealizationContext M}
    (K : OperationalContext C)
    (O : Observer M) : Prop :=

  ∀ (v : LocalRelationalConjunction C O)
    (a : M.Interaction),

    (∀ e : DirectRelation C O,
      IncidentSet C O v e ↔
      M.SigmaOp a e.val) →

    ∃ f :
        C.Alternative a →
        LocalConfigurationSpace K O v,

      ∀ Y : LocalConfigurationSpace K O v,
        ∃ ω : C.Alternative a,
          f ω = Y


/-
Finite local configuration space for an operational conjunction.

For an OperationalConjunction v:

  • v.property supplies the specific interaction a realizing v;
  • the same FOA witness supplies a finite exhaustive list Ω
    of alternatives of a;
  • LocalConfigurationsRepresentedByAlternatives supplies a
    surjective map from those alternatives to C(I(v)).

Mapping the finite list Ω through that representation map gives
a finite exhaustive list of local configurations.

Thus

    |C(I(v))| < ∞

for every conjunction in the observer-accessible operational domain.
-/
theorem operationalConjunction_localConfigurationSpace_is_finite
    {M : SBI}
    (C : NetworkRealizationContext M)
    (K : OperationalContext C)
    (O : Observer M)
    (hRepresented :
      LocalConfigurationsRepresentedByAlternatives K O)
    (v : OperationalConjunction C O) :

    ∃ Cfin : List (LocalConfigurationSpace K O v.val),
      ∀ Y : LocalConfigurationSpace K O v.val,
        Y ∈ Cfin := by

  rcases v.property with
    ⟨a, D, L,
      hRealizes,
      hAccessible,
      hFOAWitness,
      haL⟩

  rcases hFOAWitness with
    ⟨hEstablishes, hFinite⟩

  have hFiniteAtA :=
    hFinite a haL

  rcases hFiniteAtA.2 with
    ⟨Ω, hΩ⟩

  rcases hRepresented v.val a hRealizes with
    ⟨f, hSurjective⟩

  refine ⟨Ω.map f, ?_⟩

  intro Y

  rcases hSurjective Y with
    ⟨ω, hImage⟩

  have hω :
      ω ∈ Ω :=
    hΩ ω

  have hfω :
      f ω ∈ Ω.map f := by
    apply List.mem_map.mpr
    exact ⟨ω, hω, rfl⟩

  rw [hImage] at hfω

  exact hfω



/-
Proposition — Operational local finiteness.

Every conjunction in the observer-accessible operational domain has

    |I(v)| < ∞

and

    |C(I(v))| < ∞.

The two parts were proved separately from the same FOA witness
carried by the OperationalConjunction.
-/
theorem operational_domain_is_locallyFinite
    {M : SBI}
    (C : NetworkRealizationContext M)
    (K : OperationalContext C)
    (O : Observer M)
    (hRepresented :
      LocalConfigurationsRepresentedByAlternatives K O) :

    OperationallyLocallyFinite K O := by

  intro v

  constructor

  · exact
      operationalConjunction_incidentSet_is_finite
        C O v

  · exact
      operationalConjunction_localConfigurationSpace_is_finite
        C K O hRepresented v

end SBI
