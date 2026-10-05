import SBILeanProject.SBI.Axioms

set_option autoImplicit false

namespace SBI


/-
S2 — The Relational Substratum

At this stage we assume no:
  • finite operational accessibility,
  • network representation,
  • configuration space,
  • geometry,
  • temporal order,
  • dynamics.

The only imported physical assumptions are those of S1.
-/

/-
A relational domain is represented at this level by an
admissible relational organization.

We introduce this abbreviation primarily for readability.
-/
abbrev Domain (M : SBI) := M.Org

/-
An embedded observer is itself physically realized relational
organization, rather than an external observing entity.

At this primitive level we therefore represent it by an
admissible relational organization as well.
-/
abbrev Observer (M : SBI) := M.Org

/-
Observer accessibility.

Accesses O S means that relational organization belonging
to domain S is physically accessible to embedded observer O.

At this stage accessibility is left abstract.

In particular, we do not yet assume:
  • finite operational establishment,
  • a chain of elementary interactions,
  • network connectivity,
  • geometry.

Those structures will be introduced later.
-/
structure SubstratumContext (M : SBI) where
  Accesses : Observer M → Domain M → Prop

/-
Co-accessibility.

CoAccess C O S₁ S₂ means that the two relational domains
S₁ and S₂ are both physically accessible to the same
embedded observer O.

This is only a definition. It does not yet imply that
S₁ and S₂ are relationally connected.
-/
def CoAccess
    {M : SBI}
    (C : SubstratumContext M)
    (O : Observer M)
    (S₁ S₂ : Domain M) : Prop :=
  C.Accesses O S₁ ∧ C.Accesses O S₂

/-
Embedded observer.

For an embedded observer O, the statement that two domains
are both accessible to that same observer is itself a physically
meaningful relational statement.

This formalizes the manuscript requirement that the identity of
the observer cannot be supplied by an external label.

No connectivity conclusion is assumed here.
-/
def EmbeddedObserver
    {M : SBI}
    (C : SubstratumContext M)
    (O : Observer M) : Prop :=
  M.PhysMeaningful (CoAccess C O)

/-
Operational relational connectivity.

Two relational domains are operationally relationally connected
when there exists a relational witness involving both domains.

This is the formal counterpart of the manuscript definition:
relational organization involving both domains is distinguishable
through admissible interaction.
-/
def RelConnected
    (M : SBI)
    (S₁ S₂ : Domain M) : Prop :=
  M.RelWitness S₁ S₂

/-
Lemma — Uniqueness of the observer-accessible relational organization.

If the same embedded observer O has access to two relational domains
S₁ and S₂, then those domains are operationally relationally connected.

Dependencies:
  • A1 relational support
  • definition of EmbeddedObserver
  • definition of CoAccess
  • definition of RelConnected
-/
theorem one_substratum
    {M : SBI}
    (C : SubstratumContext M)
    {O : Observer M}
    {S₁ S₂ : Domain M}
    (hEmbedded : EmbeddedObserver C O)
    (h₁ : C.Accesses O S₁)
    (h₂ : C.Accesses O S₂) :
    RelConnected M S₁ S₂ := by

  exact M.A1_relational_support hEmbedded ⟨h₁, h₂⟩

/-
Observer-accessible relational family.

AccessibleFamily C O is the collection of relational domains
that are physically accessible to observer O.

At this stage this is represented as a predicate on domains,
rather than as a single aggregated relational organization.
-/
def AccessibleFamily
    {M : SBI}
    (C : SubstratumContext M)
    (O : Observer M) :
    Domain M → Prop :=
  fun S => C.Accesses O S

/-
Every pair of domains in the observer-accessible family
of an embedded observer is operationally relationally connected.

This is the family-level form of the uniqueness lemma.
-/
theorem accessibleFamily_pairwise_connected
    {M : SBI}
    (C : SubstratumContext M)
    {O : Observer M}
    (hEmbedded : EmbeddedObserver C O) :
    ∀ {S₁ S₂ : Domain M},
      AccessibleFamily C O S₁ →
      AccessibleFamily C O S₂ →
      RelConnected M S₁ S₂ := by

  intro S₁ S₂ h₁ h₂

  exact one_substratum C hEmbedded h₁ h₂

/-
Observer-accessible relational substratum.

The substratum S_O of observer O is the complete family
of relational domains physically accessible to O.

Manuscript notation:

    S_O

At this stage S_O is represented extensionally: by specifying
exactly which relational domains belong to it. No additional
global object or union operation is assumed.
-/
def ObserverSubstratum
    {M : SBI}
    (C : SubstratumContext M)
    (O : Observer M) :
    Domain M → Prop :=
  AccessibleFamily C O

/-
The observer-accessible substratum of an embedded observer
is pairwise relationally connected.

If S₁ and S₂ both belong to S_O, then they are
operationally relationally connected.

This is the formal core of the Substratum Theorem.
-/
theorem observerSubstratum_connected
    {M : SBI}
    (C : SubstratumContext M)
    {O : Observer M}
    (hEmbedded : EmbeddedObserver C O) :
    ∀ {S₁ S₂ : Domain M},
      ObserverSubstratum C O S₁ →
      ObserverSubstratum C O S₂ →
      RelConnected M S₁ S₂ := by

  intro S₁ S₂ h₁ h₂

  exact accessibleFamily_pairwise_connected
    C hEmbedded h₁ h₂

/-
Every relational domain accessible to observer O belongs
to the observer-accessible substratum S_O.

This is definitional: S_O was defined as exactly the family
of domains accessible to O.
-/
theorem accessible_mem_observerSubstratum
    {M : SBI}
    (C : SubstratumContext M)
    {O : Observer M}
    {S : Domain M}
    (hAccess : C.Accesses O S) :
    ObserverSubstratum C O S := by

  exact hAccess

/-
Membership in the observer-accessible substratum is equivalent
to physical accessibility by the observer.

Thus S_O contains exactly the relational domains accessible to O:
neither more nor less.

Manuscript meaning:

    S ∈ S_O  ↔  O has access to S.
-/
theorem observerSubstratum_iff_accesses
    {M : SBI}
    (C : SubstratumContext M)
    {O : Observer M}
    {S : Domain M} :
    ObserverSubstratum C O S ↔
    C.Accesses O S := by

  rfl

/-
Theorem — The Substratum Theorem.

For any embedded observer O:

1. The observer-accessible substratum S_O contains exactly
   the relational domains physically accessible to O.

2. Any two domains belonging to S_O are operationally
   relationally connected.

Thus the observer-accessible world of O forms one
relationally connected organization, and no accessible
domain lies outside S_O.

Dependencies:
  • A1 relational support
  • EmbeddedObserver
  • ObserverSubstratum
  • observerSubstratum_iff_accesses
  • observerSubstratum_connected

No A2, A3, FOA, network structure, configuration space,
geometry, or dynamics is required.
-/
theorem substratum_theorem
    {M : SBI}
    (C : SubstratumContext M)
    {O : Observer M}
    (hEmbedded : EmbeddedObserver C O) :

    (∀ S : Domain M,
      ObserverSubstratum C O S ↔
      C.Accesses O S)
    ∧
    (∀ S₁ S₂ : Domain M,
      ObserverSubstratum C O S₁ →
      ObserverSubstratum C O S₂ →
      RelConnected M S₁ S₂) := by

  constructor

  · intro S
    exact observerSubstratum_iff_accesses C

  · intro S₁ S₂ h₁ h₂
    exact observerSubstratum_connected
      C hEmbedded h₁ h₂

end SBI
