import SBILeanProject.SBI.Persistence

set_option autoImplicit false

namespace SBI

/-
S2 — Local persistence compatibility.

Persistence.lean established operational re-identification and
finite operational support.

This file studies the local configurations compatible with
maintaining a given persistent identity.

The central object is

    U_P(v; Y),

the set of admissible local configurations at v that preserve
persistent identity P when the surrounding relational context
is held fixed.

No configuration-change relation, temporal ordering, or dynamics
is introduced at this stage.
-/

/-
Local persistence semantics.

For each observer O and local relational conjunction v:

  • RelationalContext O v is the type of relational contexts Y
    outside I(v) that may be relevant to persistence at v;

  • PreservesReidentification O R v Y Z means that the
    persistent identity represented by R remains operationally
    re-identifiable when the local configuration at v is Z
    while the relevant surrounding relational context is Y.

This introduces the semantic vocabulary needed for

    U_R(v; Y).

No temporal ordering, transition relation, or dynamics is
introduced.  Z and Y specify a relational realization, not
a change from one realization to another.
-/
structure LocalPersistenceSemantics
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (P : PersistenceContext K) where

  /-
  Manuscript notation: Y.

  A relational context relevant at the local conjunction v.
  -/
  RelationalContext :
    (O : Observer M) →
    LocalRelationalConjunction C O →
    Type

  /-
  Persistence under a local admissible configuration.

  PreservesReidentification O R v Y Z means that the
  persistence class [R]ₚ remains operationally re-identifiable
  with local configuration Z at v in relational context Y.
  -/
  PreservesReidentification :
    (O : Observer M) →
    (R : M.Org) →
    (v : LocalRelationalConjunction C O) →
    RelationalContext O v →
    LocalConfigurationSpace K O v →
    Prop

  /-
  Representative independence of local persistence semantics.

  The manuscript object is the persistence class [R]ₚ rather than a
  distinguished representative R.  Therefore replacing R by any
  persistence-equivalent representative must not change whether a local
  realization preserves operational re-identification.

  This field makes the class-level meaning explicit while allowing the
  formalization to continue using representatives instead of quotient
  types.
  -/
  preserves_rep_independent :
    ∀ (O : Observer M)
      {R₁ R₂ : M.Org}
      (v : LocalRelationalConjunction C O)
      (Y : RelationalContext O v)
      (Z : LocalConfigurationSpace K O v),
      M.Persist R₁ R₂ →
      (PreservesReidentification O R₁ v Y Z ↔
       PreservesReidentification O R₂ v Y Z)

/-
Persistence-preserving local admissibility set.

Manuscript notation:

    U_R(v; Y)

or, when the persistent identity is denoted P,

    U_P(v; Y).

A local configuration Z belongs to U_R(v; Y) exactly when

  • Z is locally admissible at v, and
  • the persistent identity represented by R remains
    operationally re-identifiable in relational context Y.

Thus

    U_R(v; Y) ⊆ A(I(v)).

The set is represented as a predicate on the local
configuration space rather than as a separate Set object.

No transition from one configuration to another is implied.
The definition concerns compatibility of a local realization
with persistence.
-/
def PersistencePreservingLocal
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (R : M.Org)
    (v : LocalRelationalConjunction C O)
    (Y : S.RelationalContext O v) :
    LocalConfigurationSpace K O v → Prop :=

  fun Z =>
    IsAdmissibleLocal K O v Z ∧
    S.PreservesReidentification O R v Y Z


/-
The persistence-preserving local set depends only on the persistence
class [R]ₚ, not on the representative used to denote that class.

If R₁ and R₂ are persistence-equivalent, then

    U_{R₁}(v; Y) = U_{R₂}(v; Y)

extensionally.  Local admissibility is unchanged, and representative
independence of PreservesReidentification supplies the persistence
component.
-/
theorem persistencePreservingLocal_rep_independent
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    {R₁ R₂ : M.Org}
    (v : LocalRelationalConjunction C O)
    (Y : S.RelationalContext O v)
    (Z : LocalConfigurationSpace K O v)
    (hPersist : M.Persist R₁ R₂) :

    PersistencePreservingLocal S O R₁ v Y Z ↔
    PersistencePreservingLocal S O R₂ v Y Z := by

  constructor

  · intro hR₁

    exact
      ⟨hR₁.1,
       (S.preserves_rep_independent O v Y Z hPersist).mp hR₁.2⟩

  · intro hR₂

    exact
      ⟨hR₂.1,
       (S.preserves_rep_independent O v Y Z hPersist).mpr hR₂.2⟩

/-
Every persistence-preserving local configuration is locally admissible.

This is immediate from the definition of U_R(v; Y):

    Z ∈ U_R(v; Y)

means

    Z ∈ A(I(v))
    and
    persistence is preserved.

Therefore

    U_R(v; Y) ⊆ A(I(v)).
-/
theorem persistencePreservingLocal_is_admissible
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (R : M.Org)
    (v : LocalRelationalConjunction C O)
    (Y : S.RelationalContext O v)
    (Z : LocalConfigurationSpace K O v)
    (hZ :
      PersistencePreservingLocal S O R v Y Z) :

    IsAdmissibleLocal K O v Z := by

  exact hZ.1

/-
Every member of U_R(v; Y) preserves the persistent identity
represented by R in the specified relational context.

From

    Z ∈ U_R(v; Y)

we obtain directly

    PreservesReidentification O R v Y Z.

This is the second component of the definition of
PersistencePreservingLocal.
-/
theorem persistencePreservingLocal_preserves
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (R : M.Org)
    (v : LocalRelationalConjunction C O)
    (Y : S.RelationalContext O v)
    (Z : LocalConfigurationSpace K O v)
    (hZ :
      PersistencePreservingLocal S O R v Y Z) :

    S.PreservesReidentification O R v Y Z := by

  exact hZ.2

/-
Restricted persistence compatibility.

Persistence imposes a nontrivial local restriction at v in
context Y when there exists at least one locally admissible
configuration Z which does NOT preserve the persistent identity
represented by R.

Formally:

    ∃ Z ∈ A(I(v)) such that Z ∉ U_R(v; Y).

Equivalently, U_R(v; Y) is a proper subset of the locally
admissible configurations.

This is NOT asserted here as a consequence of A3 alone.
It is a definition of what it means for persistence to constrain
local admissibility nontrivially.
-/
def PersistenceRestrictsLocally
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (R : M.Org)
    (v : LocalRelationalConjunction C O)
    (Y : S.RelationalContext O v) : Prop :=

  ∃ Z : LocalConfigurationSpace K O v,
    IsAdmissibleLocal K O v Z ∧
    ¬ S.PreservesReidentification O R v Y Z

/-
Restricted persistence compatibility excludes at least one
otherwise admissible local configuration from U_R(v; Y).

If persistence constrains local admissibility nontrivially, then

    ∃ Z,
      Z ∈ A(I(v))
      and
      Z ∉ U_R(v; Y).

This is the explicit proper-subset witness for

    U_R(v; Y) ⊊ A(I(v)).
-/
theorem persistenceRestrictsLocally_excludes_admissible
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (R : M.Org)
    (v : LocalRelationalConjunction C O)
    (Y : S.RelationalContext O v)
    (hRestricts :
      PersistenceRestrictsLocally S O R v Y) :

    ∃ Z : LocalConfigurationSpace K O v,
      IsAdmissibleLocal K O v Z ∧
      ¬ PersistencePreservingLocal S O R v Y Z := by

  rcases hRestricts with
    ⟨Z, hAdmissible, hNotPreserved⟩

  refine ⟨Z, hAdmissible, ?_⟩

  intro hInU

  have hPreserved :
      S.PreservesReidentification O R v Y Z :=
    persistencePreservingLocal_preserves
      S O R v Y Z hInU

  exact hNotPreserved hPreserved

/-
Definition — Relational adaptation.

A relational adaptation of persistent identity [R]ₚ at a local
conjunction v consists of two persistence-compatible local
realizations

    (Y₁, Z₁)
    (Y₂, Z₂)

such that the relational realization actually differs:

    Y₁ ≠ Y₂  or  Z₁ ≠ Z₂.

In both realizations, the local configuration belongs to the
persistence-preserving set:

    Z₁ ∈ U_R(v; Y₁)
    Z₂ ∈ U_R(v; Y₂).

Thus the persistent identity remains operationally
re-identifiable while its relational realization changes.

This records two relational realizations and their relation.
It does NOT introduce a temporal parameter, evolution law,
or primitive configuration-transition relation.
-/
structure RelationalAdaptation
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (O : Observer M)
    (R : M.Org)
    (v : LocalRelationalConjunction C O) where

  Y₁ : S.RelationalContext O v
  Y₂ : S.RelationalContext O v

  Z₁ : LocalConfigurationSpace K O v
  Z₂ : LocalConfigurationSpace K O v

  preserves₁ :
    PersistencePreservingLocal S O R v Y₁ Z₁

  preserves₂ :
    PersistencePreservingLocal S O R v Y₂ Z₂

  changed :
    Y₁ ≠ Y₂ ∨ Z₁ ≠ Z₂

/-
Nonincident local relational conjunctions.

Two conjunctions v₁ and v₂ are nonincident when there exists
no DirectRelation edge incident on both of them.

Formally:

    ¬ ∃ e,
        ι(e,v₁) ∧ ι(e,v₂).

This is a purely incidence-network notion. It introduces no
metric, distance, geometry, or embedding.
-/
def NonIncidentConjunctions
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (v₁ v₂ : LocalRelationalConjunction C O) : Prop :=

  ¬ ∃ e : DirectRelation C O,
      Incident C O e v₁ ∧
      Incident C O e v₂

/-
Relational-domain representation of local conjunctions.

The finite-local-mediation theorem is stated at the primitive
relational-domain level, whereas relational adaptation is stated
at the incidence-network level.

ConjunctionDomainSemantics supplies the bridge between these
descriptions.

For each observer O and local relational conjunction v,

    AsDomain O v

is a relational domain representing that conjunction at the
primitive relational level.

Because v belongs to the observer-accessible network,
the representing domain is required to be accessible to O.

No uniqueness or injectivity is assumed:
different conjunctions need not be represented by distinct
elements of Domain M.
-/
structure ConjunctionDomainSemantics
    {M : SBI}
    (C : NetworkRealizationContext M) where

  AsDomain :
    (O : Observer M) →
    LocalRelationalConjunction C O →
    Domain M

  accessible :
    ∀ (O : Observer M)
      (v : LocalRelationalConjunction C O),
      C.Accesses O (AsDomain O v)

/-
Semantics of induced relational adaptation.

Induces is the actual relation saying that adaptation A₁
at v₁ induces adaptation A₂ at v₂.

The second field states the operational consequence needed
for the propagation lemma: if A₁ induces A₂, then the
conjunction-domains carrying those adaptations are
observer-accessibly relationally connected.

Thus "induces" is not identified with connectivity itself.
Connectivity is a necessary operational realization of the
induced dependence.
-/
structure AdaptationInductionSemantics
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (D : ConjunctionDomainSemantics C) where

  Induces :
    ∀ (O : Observer M)
      (R : M.Org)
      {v₁ v₂ : LocalRelationalConjunction C O},
      RelationalAdaptation S O R v₁ →
      RelationalAdaptation S O R v₂ →
      Prop

  induces_relational_connection :
    ∀ (O : Observer M)
      (R : M.Org)
      {v₁ v₂ : LocalRelationalConjunction C O}
      (A₁ : RelationalAdaptation S O R v₁)
      (A₂ : RelationalAdaptation S O R v₂),

      Induces O R A₁ A₂ →

      ObserverRelConnected
        C.toNetworkContext
        O
        (D.AsDomain O v₁)
        (D.AsDomain O v₂)

/-
A₁ induces A₂ according to the specified adaptation-induction
semantics.

Unlike the earlier provisional definition, this proposition
really depends on the two adaptations themselves.
-/
def AdaptationInduces
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (D : ConjunctionDomainSemantics C)
    (I : AdaptationInductionSemantics S D)
    (O : Observer M)
    (R : M.Org)
    {v₁ v₂ : LocalRelationalConjunction C O}
    (A₁ : RelationalAdaptation S O R v₁)
    (A₂ : RelationalAdaptation S O R v₂) : Prop :=

  I.Induces O R A₁ A₂

/-
Induced relational adaptation has finite local mediation.

If adaptation A₁ at v₁ induces adaptation A₂ at v₂, then the
adaptation-induction semantics supplies an observer-accessible
relational connection between the domains representing v₁ and v₂.

The previously proved finite-observer-local-mediation theorem
then gives a finite list of elementary interactions in which
successive interactions share observer-accessible relational
participation.

Thus:

    A₁ induces A₂
        + operational connection semantics
        + derived finite operational accessibility
    -----------------------------------------------
        finite observer-accessible mediation chain.

Finite operational accessibility is not an independent hypothesis here.
It is derived upstream from the operational meaning of accessibility
together with A2.  No temporal ordering or geometric distance is
introduced.
-/
theorem inducedAdaptation_has_finiteLocalMediation
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (Dsem : ConjunctionDomainSemantics C)
    (I : AdaptationInductionSemantics S Dsem)
    (hSemantics : OperationalConnectionSemantics C)
    (O : Observer M)
    (R : M.Org)
    {v₁ v₂ : LocalRelationalConjunction C O}
    (A₁ : RelationalAdaptation S O R v₁)
    (A₂ : RelationalAdaptation S O R v₂)
    (hInduces :
      AdaptationInduces S Dsem I O R A₁ A₂) :

    ∃ (D : C.Distinction) (L : List M.Interaction),
      C.AccessibleDistinction O D ∧
      C.ConnectionDistinction
        O
        (Dsem.AsDomain O v₁)
        (Dsem.AsDomain O v₂)
        D
      ∧
      C.Establishes O D L
      ∧
      ObserverDirectMediationChain C O L := by

  have hConnected :
      ObserverRelConnected
        C.toNetworkContext
        O
        (Dsem.AsDomain O v₁)
        (Dsem.AsDomain O v₂) :=
    I.induces_relational_connection
      O R A₁ A₂ hInduces

  exact
    finite_observer_local_mediation_of_connected
      C
      hSemantics
      hConnected

/-
Lemma — Local propagation of relational adaptation.

Let v₁ and v₂ be nonincident local relational conjunctions.
If adaptation A₁ of persistent identity [R]ₚ at v₁ induces
adaptation A₂ at v₂, then the induced relation is realized by
a finite observer-accessible local mediation chain.

The nonincidence hypothesis expresses the manuscript case of
adaptation propagating beyond direct incidence.

The proof itself does not require nonincidence: the stronger
result inducedAdaptation_has_finiteLocalMediation was already
proved for arbitrary conjunctions. Thus nonincidence restricts
the physical case being described rather than supplying an
additional inferential step.
-/
theorem localPropagation_of_relationalAdaptation
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {P : PersistenceContext K}
    (S : LocalPersistenceSemantics P)
    (Dsem : ConjunctionDomainSemantics C)
    (I : AdaptationInductionSemantics S Dsem)
    (hSemantics : OperationalConnectionSemantics C)
    (O : Observer M)
    (R : M.Org)
    {v₁ v₂ : LocalRelationalConjunction C O}
    (A₁ : RelationalAdaptation S O R v₁)
    (A₂ : RelationalAdaptation S O R v₂)
    (_hNonIncident :
  NonIncidentConjunctions C O v₁ v₂)
    (hInduces :
      AdaptationInduces S Dsem I O R A₁ A₂) :

    ∃ (D : C.Distinction) (L : List M.Interaction),
      C.AccessibleDistinction O D ∧
      C.ConnectionDistinction
        O
        (Dsem.AsDomain O v₁)
        (Dsem.AsDomain O v₂)
        D
      ∧
      C.Establishes O D L
      ∧
      ObserverDirectMediationChain C O L := by

  exact
    inducedAdaptation_has_finiteLocalMediation
      S
      Dsem
      I
      hSemantics
      O
      R
      A₁
      A₂
      hInduces
