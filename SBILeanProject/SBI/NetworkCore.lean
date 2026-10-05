import SBILeanProject.SBI.Substratum

set_option autoImplicit false

namespace SBI

/-
S2 — Network Representation

This file formalizes:
  • derived finite operational accessibility (FOA),
  • finite local mediation,
  • direct relations,
  • local relational conjunctions,
  • the incidence-network representation.

At this stage no network, configuration space, or geometry
is assumed.
-/

/-
Formal vocabulary required to state FOA.

This extends the observer-accessibility context introduced
in Substratum.lean.  It adds the operational vocabulary required
to state finite establishment and connection distinctions, but
introduces no additional physical axiom.
-/
structure NetworkContext (M : SBI)
    extends SubstratumContext M where

  /-
  Observer-accessible relational distinctions.

  A Distinction is something that may be operationally
  established by an embedded observer.
  -/
  Distinction : Type

  /-
  AccessibleDistinction O D means that the relational
  distinction D is operationally accessible to observer O.

  The field below names the operational relation.  Its finite
  establishment content is fixed separately by
  accessible_has_establishment, so downstream code can retain
  the established AccessibleDistinction interface.
  -/
  AccessibleDistinction :
    Observer M → Distinction → Prop

  /-
  Establishes O D interactions means that the listed
  elementary admissible interactions are sufficient to
  operationally establish distinction D for observer O.

  Lean's List is intrinsically finite.  A witness carried by
  Establishes therefore represents a completed finite
  operational realization, without introducing a temporal
  parameter or assuming microscopic discreteness.
  -/
  Establishes :
    Observer M →
    Distinction →
    List M.Interaction →
    Prop

  /-
  Operational meaning of accessibility.

  If a distinction is accessible to an embedded observer, some
  completed finite list of elementary admissible interactions
  establishes it.

  This is not an additional physical axiom.  It fixes the
  operational meaning of AccessibleDistinction: a distinction
  for which no completed operational realization exists is not
  an established distinction available to the observer.

  Finiteness follows from the use of List and concerns the
  operational witness only.
  -/
  accessible_has_establishment :
    ∀ (O : Observer M) (D : Distinction),
      AccessibleDistinction O D →
      ∃ L : List M.Interaction,
        Establishes O D L
    /-
  ConnectionDistinction O S₁ S₂ D means that D is specifically
  the operational distinction by which observer O establishes
  relational connection between domains S₁ and S₂.

  This does not say that all distinctions are connection
  distinctions.
  -/
  ConnectionDistinction :
    Observer M →
    Domain M →
    Domain M →
    Distinction →
    Prop
  /-
  Compatibility name for the operational alternatives associated
  with elementary interaction a.

  The operational alternative type is now supplied by A2.  This
  field is retained temporarily so that downstream files can keep
  using C.Alternative while the formalization is migrated.
  alternative_matches_A2 ensures that it introduces no independent
  alternative structure.
  -/
  Alternative :
    M.Interaction → Type

  /-
  The NetworkContext alternative type is exactly the operational
  alternative type supplied by A2.

  This equality is a compatibility bridge only.  Once downstream
  files use M.Alternative directly, both this field and the bridge
  can be removed.
  -/
  alternative_matches_A2 :
    ∀ a : M.Interaction,
      Alternative a = M.Alternative a

/-
Finite Operational Accessibility (FOA).

FOA is retained as a named proposition because many later results
use its finite-witness interface.  Its logical status has changed:
it is no longer an independent assumption.

For every relational distinction accessible to an observer:

  • the operational meaning of accessibility supplies a finite
    list L of elementary interactions sufficient to establish
    that distinction;

  • A2 supplies a finite enumeration of the relational
    participations operationally resolved in every interaction
    a in L;

  • A2 also supplies a finite enumeration of the operational
    alternatives distinguished by every such interaction.

The finiteness is therefore entirely operational.  It neither
imposes global finiteness nor discrete structure on the
substratum.
-/
def FOA
    {M : SBI}
    (C : NetworkContext M) : Prop :=

  ∀ (O : Observer M) (D : C.Distinction),
    C.AccessibleDistinction O D →
    ∃ L : List M.Interaction,
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
Proposition — Finite Operational Accessibility.

This theorem is the formal counterpart of the revised FOA result
in Supplementary Discussion S2.

The proof separates the two sources of finiteness:

  1. operational accessibility supplies a completed finite
     establishing witness L;

  2. A2 supplies finite operational participation and finite
     operational alternative resolution for each interaction.

FOA therefore packages already specified operational structure
for reuse by the later network and persistence proofs.  It is
not a fourth physical axiom.
-/
theorem finite_operational_accessibility
    {M : SBI}
    (C : NetworkContext M) :
    FOA C := by

  intro O D hAccessible

  rcases
      C.accessible_has_establishment O D hAccessible with
    ⟨L, hEstablishes⟩

  refine ⟨L, hEstablishes, ?_⟩

  intro a _ha

  constructor

  · exact M.sigmaOp_finite a

  ·
    rw [C.alternative_matches_A2 a]
    exact M.alternative_finite a


/-
A mediation chain is a finite sequence of elementary admissible
interactions in which mediation passes successively from each
interaction to the next.

For

    [a₁, a₂, ..., aₙ]

this expresses

    MediationStep a₁ a₂
    ∧ MediationStep a₂ a₃
    ∧ ...
    ∧ MediationStep aₙ₋₁ aₙ.

The empty list and a single interaction are trivially chains.

This is only a definition. In particular, it does NOT assert
that every finite operational witness supplied by FOA is a
mediation chain.
-/
def MediationChain
    (M : SBI) :
    List M.Interaction → Prop

  | [] =>
      True

  | [_] =>
      True

  | a :: b :: rest =>
      M.MediationStep a b ∧
      MediationChain M (b :: rest)

/-
A direct mediation chain is a finite sequence of elementary
interactions in which every successive pair shares at least
one relational participation.

For

    [a₁, a₂, ..., aₙ]

this expresses

    Direct a₁ a₂
    ∧ Direct a₂ a₃
    ∧ ...
    ∧ Direct aₙ₋₁ aₙ,

where

    Direct a b

means

    ∃ p, SigmaOp a p ∧ SigmaOp b p.

The empty list and a single interaction are trivially
direct chains.

This is only a definition. A2 will be used next to prove that
every MediationChain is a DirectMediationChain.
-/
def DirectMediationChain
    (M : SBI) :
    List M.Interaction → Prop

  | [] =>
      True

  | [_] =>
      True

  | a :: b :: rest =>
      (∃ p : M.Participation,
      M.SigmaOp a p ∧ M.SigmaOp b p) ∧
    DirectMediationChain M (b :: rest)

/-
Semantic coherence of connection distinctions.

If D is specifically a distinction establishing relational
connection between S₁ and S₂, and a list L of elementary
interactions establishes D, then those interactions must form
a mediation chain.

This is not a new physical axiom. It specifies what we mean
when we use Establishes for a ConnectionDistinction.

In particular, it prevents an arbitrary unordered collection
of interactions from counting as an operational witness of
relational connection.
-/
def ConnectionEstablishmentCoherent
    {M : SBI}
    (C : NetworkContext M) : Prop :=

  ∀ (O : Observer M)
    (S₁ S₂ : Domain M)
    (D : C.Distinction)
    (L : List M.Interaction),

    C.ConnectionDistinction O S₁ S₂ D →
    C.Establishes O D L →
    MediationChain M L

/-
Observer-accessible relational connectivity.

Two relational domains S₁ and S₂ are operationally connected
for observer O when there exists an observer-accessible
distinction D whose content is precisely their relational
connection.

This makes explicit the operational content already present
in the manuscript definition of relational connectivity.
-/
def ObserverRelConnected
    {M : SBI}
    (C : NetworkContext M)
    (O : Observer M)
    (S₁ S₂ : Domain M) : Prop :=

  ∃ D : C.Distinction,
    C.AccessibleDistinction O D ∧
    C.ConnectionDistinction O S₁ S₂ D

/-
Operational resolution of relational connectivity.

At the primitive Substratum level,

    RelConnected M S₁ S₂

means that the relation between S₁ and S₂ has a relational
witness accessible through admissible interaction.

At the finer operational level introduced in Network.lean,
that same accessible relational connection must be resolvable
as an observer-accessible ConnectionDistinction.

This condition therefore bridges the primitive relational
language of Substratum.lean to the explicit operational
distinction language used in the network construction.

It is a semantic refinement of RelConnected at operational
resolution, not an additional physical axiom.
-/
def OperationalResolutionOfRelConnected
    {M : SBI}
    (C : NetworkContext M) : Prop :=

  ∀ (O : Observer M)
    (S₁ S₂ : Domain M),

    C.Accesses O S₁ →
    C.Accesses O S₂ →
    RelConnected M S₁ S₂ →
    ObserverRelConnected C O S₁ S₂


/-
Observer-substratum connectivity resolves operationally.

Let O be an embedded observer and let S₁ and S₂ both belong
to the observer-accessible substratum S_O.

The Substratum Theorem establishes that:

  • membership in S_O is equivalent to accessibility by O;
  • every pair of domains in S_O is relationally connected.

OperationalResolutionOfRelConnected then upgrades that primitive
relational connectivity to an observer-accessible connection
distinction.

This theorem is therefore the explicit bridge

    Substratum Theorem
          ↓
    operationally resolved connectivity

required by the network construction.
-/
theorem observerSubstratum_is_operationallyConnected
    {M : SBI}
    (C : NetworkContext M)
    (hResolution : OperationalResolutionOfRelConnected C)
    {O : Observer M}
    (hEmbedded :
      EmbeddedObserver C.toSubstratumContext O)
    {S₁ S₂ : Domain M}
    (h₁ :
      ObserverSubstratum C.toSubstratumContext O S₁)
    (h₂ :
      ObserverSubstratum C.toSubstratumContext O S₂) :

    ObserverRelConnected C O S₁ S₂ := by

  /-
  Invoke the named Substratum Theorem itself.

  hSub.1 gives:
      S ∈ S_O ↔ Accesses O S

  hSub.2 gives:
      S₁,S₂ ∈ S_O → RelConnected S₁ S₂
  -/
  have hSub :=
    substratum_theorem
      C.toSubstratumContext
      hEmbedded

  have hAccess₁ : C.Accesses O S₁ :=
    (hSub.1 S₁).1 h₁

  have hAccess₂ : C.Accesses O S₂ :=
    (hSub.1 S₂).1 h₂

  have hRelConnected :
      RelConnected M S₁ S₂ :=
    hSub.2 S₁ S₂ h₁ h₂

  exact hResolution
    O S₁ S₂
    hAccess₁
    hAccess₂
    hRelConnected

/-
A2 localizes every mediation chain.

If mediation passes successively through a finite list of
elementary interactions, then every successive pair shares at least one operationally
distinguished relational participation.

This is exactly where the local-mediation clause of A2 enters
the network derivation.
-/
theorem mediationChain_is_direct
    (M : SBI)
    {L : List M.Interaction}
    (hChain : MediationChain M L) :
    DirectMediationChain M L := by

  induction L with

  | nil =>
      trivial

  | cons a tail ih =>
      cases tail with

      | nil =>
          trivial

      | cons b rest =>
          change
            M.MediationStep a b ∧
            MediationChain M (b :: rest)
            at hChain

          rcases hChain with ⟨hStep, hRest⟩

          change
            (∃ p : M.Participation,
              M.SigmaOp a p ∧ M.SigmaOp b p) ∧
            DirectMediationChain M (b :: rest)

          constructor

          · exact M.A2_local_mediation hStep

          · exact ih hRest

/-
Generic finite local mediation from an already established
observer-resolved relational connection.

This is the reusable core result. It does not specify where the
connection came from.  Finite operational accessibility is no longer
an input to the theorem: the proof derives it internally from
finite_operational_accessibility.
-/
theorem finite_local_mediation_of_connected
    {M : SBI}
    (C : NetworkContext M)
    (hCoherent : ConnectionEstablishmentCoherent C)
    {O : Observer M}
    {S₁ S₂ : Domain M}
    (hConnected : ObserverRelConnected C O S₁ S₂) :

    ∃ (D : C.Distinction) (L : List M.Interaction),
      C.AccessibleDistinction O D ∧
      C.ConnectionDistinction O S₁ S₂ D ∧
      C.Establishes O D L ∧
      DirectMediationChain M L := by

  rcases hConnected with
    ⟨D, hAccessible, hConnection⟩

  /-
  FOA is not supplied as an extra hypothesis.  It is derived here
  from the operational meaning of accessibility together with A2.
  Keeping this derivation inside the theorem makes the manuscript-level
  dependency explicit in the checked proof.
  -/
  have hFOA : FOA C :=
    finite_operational_accessibility C

  rcases hFOA O D hAccessible with
    ⟨L, hEstablishes, _hFiniteResolution⟩

  have hChain : MediationChain M L :=
    hCoherent
      O S₁ S₂ D L
      hConnection
      hEstablishes

  have hDirect : DirectMediationChain M L :=
    mediationChain_is_direct M hChain

  exact
    ⟨D, L,
      hAccessible,
      hConnection,
      hEstablishes,
      hDirect⟩

/-
Lemma — Finite local mediation.

Let O be an embedded observer and let S₁ and S₂ belong to
its observer-accessible substratum.

The Substratum Theorem establishes primitive relational
connectivity between them. Operational resolution represents
that connection by an observer-accessible connection
distinction. Finite operational accessibility is derived from the
operational meaning of accessibility together with A2 and supplies a
finite interaction witness. Connection semantics makes that witness a
mediation chain, and A2 converts the chain into shared operationally
resolved relational participation.

Thus the named theorem itself follows the manuscript-level
dependency structure.
-/
theorem finite_local_mediation
    {M : SBI}
    (C : NetworkContext M)
    (hCoherent : ConnectionEstablishmentCoherent C)
    (hResolution : OperationalResolutionOfRelConnected C)
    {O : Observer M}
    (hEmbedded :
      EmbeddedObserver C.toSubstratumContext O)
    {S₁ S₂ : Domain M}
    (h₁ :
      ObserverSubstratum C.toSubstratumContext O S₁)
    (h₂ :
      ObserverSubstratum C.toSubstratumContext O S₂) :

    ∃ (D : C.Distinction) (L : List M.Interaction),
      C.AccessibleDistinction O D ∧
      C.ConnectionDistinction O S₁ S₂ D ∧
      C.Establishes O D L ∧
      DirectMediationChain M L := by

  have hConnected :
      ObserverRelConnected C O S₁ S₂ :=
    observerSubstratum_is_operationallyConnected
      C
      hResolution
      hEmbedded
      h₁
      h₂

  exact finite_local_mediation_of_connected
    C
    hCoherent
    hConnected

end SBI
