import SBILeanProject.SBI.NetworkOperational

set_option autoImplicit false

namespace SBI

/-
S2 — Network realization and Network Representation Theorem.

This module converts observer-accessible mediation chains into
incidence-network chains and proves the final representation result.
-/

/-
Every elementary interaction determines a local relational
conjunction at the observer's operational resolution.

For interaction a, define the conjunction consisting exactly
of those DirectRelations e for which

    SigmaOp a e.val.

Because LocalRelationalConjunction requires only that such a
collection be realized by some elementary interaction, a itself
provides the required witness.

This construction does not require that all participations in a
are observer-accessible. It retains exactly the accessible direct
relations participating in a.
-/
def InteractionConjunction
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (a : M.Interaction) :
    LocalRelationalConjunction C O := by

  refine ⟨
    (fun e : DirectRelation C O =>
      M.SigmaOp a e.val),
    ?_
  ⟩

  unfold IsLocalRelationalConjunction

  refine ⟨a, ?_⟩

  intro e

  rfl

/-
Shared accessible participation gives a common network edge.

Suppose p is

  • operationally accessible to observer O,
  • operationally resolved in elementary interaction a, and
  • operationally resolved in elementary interaction b.

Then p determines an edge e of ObserverNetwork C O, and that same edge is
incident, through the incidence relation of that network, on both
conjunction-vertices

    InteractionConjunction C O a

and

    InteractionConjunction C O b.

This is the precise network realization of the statement that
successive locally mediated interactions are joined by a shared
direct relation.
-/
theorem sharedParticipation_gives_commonEdge
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    {a b : M.Interaction}
    {p : M.Participation}
    (hAccessible : C.AccessibleParticipation O p)
    (ha : M.SigmaOp a p)
    (hb : M.SigmaOp b p) :

    ∃ e : (ObserverNetwork C O).Edge,
      (ObserverNetwork C O).Incidence
        e (InteractionConjunction C O a) ∧
      (ObserverNetwork C O).Incidence
        e (InteractionConjunction C O b) := by

  let e : (ObserverNetwork C O).Edge :=
    ⟨p, hAccessible, ⟨a, ha⟩⟩

  refine ⟨e, ?_, ?_⟩

  · exact ha

  · exact hb

/-
Incidence-network realization of an interaction chain.

A list of elementary interactions

    [a₁, a₂, ..., aₙ]

is realized as a chain in ObserverNetwork C O when, for every successive
pair aᵢ and aᵢ₊₁, there exists an edge of that network incident on both
corresponding conjunction-vertices

    InteractionConjunction C O aᵢ
    InteractionConjunction C O aᵢ₊₁.

The empty list and a single interaction are trivially network
chains.

The reference to ObserverNetwork is deliberate: the formal chain now uses
the same bundled incidence-network object G_O = (V_O, E_O, ι_O) that appears
in the manuscript, rather than reconstructing its edge and incidence fields
independently.

This definition does not require distinct vertices or distinct edges, and
imposes no geometry or metric.
-/
def NetworkIncidenceChain
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M) :
    List M.Interaction → Prop

  | [] =>
      True

  | [_] =>
      True

  | a :: b :: rest =>
      (∃ e : (ObserverNetwork C O).Edge,
        (ObserverNetwork C O).Incidence
          e (InteractionConjunction C O a) ∧
        (ObserverNetwork C O).Incidence
          e (InteractionConjunction C O b))
      ∧
      NetworkIncidenceChain C O (b :: rest)

/-
Every observer-accessible direct mediation chain has an
incidence-network realization.

For each successive pair of interactions a and b, the
ObserverDirectMediationChain supplies an observer-accessible
participation p that belongs to SigmaOp for both interactions.

Because DirectRelation and local conjunction membership are now
defined directly at the same operational resolution, the witness
passes into the network construction without any conversion through
the unrestricted Sigma relation.

Induction applies the same construction to the remainder of
the chain.
-/
theorem observerDirectChain_is_networkChain
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    {L : List M.Interaction}
    (hChain : ObserverDirectMediationChain C O L) :
    NetworkIncidenceChain C O L := by

  induction L with

  | nil =>
      trivial

  | cons a tail ih =>
      cases tail with

      | nil =>
          trivial

      | cons b rest =>
          change
            (∃ p : M.Participation,
              C.AccessibleParticipation O p ∧
              M.SigmaOp a p ∧
              M.SigmaOp b p) ∧
            ObserverDirectMediationChain C O (b :: rest)
            at hChain

          rcases hChain with ⟨hShared, hRest⟩
          rcases hShared with
            ⟨p, hAccessible, ha, hb⟩

          change
            (∃ e : (ObserverNetwork C O).Edge,
              (ObserverNetwork C O).Incidence
                e (InteractionConjunction C O a) ∧
              (ObserverNetwork C O).Incidence
                e (InteractionConjunction C O b))
            ∧
            NetworkIncidenceChain C O (b :: rest)

          constructor

          · exact sharedParticipation_gives_commonEdge
              C O hAccessible
              ha
              hb

          · exact ih hRest

/-
Finite network realization of an operational connection.

If relational domains S₁ and S₂ are operationally connected for
observer O, then within the observer-accessible operational domain
there exists a finite list L of elementary interactions which

  • operationally establishes the relevant connection distinction,
  • and is realized as an incidence chain in ObserverNetwork.

The semantic content of connection establishment is carried by
OperationalConnectionSemantics rather than by separate coherence
hypotheses.  Finite operational accessibility is derived upstream
and is therefore not supplied as an independent hypothesis here.
-/
theorem finite_network_realization
    {M : SBI}
    (C : NetworkRealizationContext M)
    (hSemantics : OperationalConnectionSemantics C)
    (hResolution :
      OperationalResolutionOfRelConnected C.toNetworkContext)
    {O : Observer M}
    (hEmbedded :
      EmbeddedObserver
        C.toNetworkContext.toSubstratumContext O)
    {S₁ S₂ : Domain M}
    (h₁ :
      ObserverSubstratum
        C.toNetworkContext.toSubstratumContext O S₁)
    (h₂ :
      ObserverSubstratum
        C.toNetworkContext.toSubstratumContext O S₂) :

    ∃ (D : C.Distinction) (L : List M.Interaction),
      C.AccessibleDistinction O D ∧
      C.ConnectionDistinction O S₁ S₂ D ∧
      C.Establishes O D L ∧
      NetworkIncidenceChain C O L := by

  rcases finite_observer_local_mediation
    C
    hSemantics
    hResolution
    hEmbedded
    h₁
    h₂ with
    ⟨D, L, hAccessible, hConnection, hEstablishes, hObserverChain⟩

  have hNetworkChain :
      NetworkIncidenceChain C O L :=
    observerDirectChain_is_networkChain
      C O hObserverChain

  exact ⟨D, L,
    hAccessible,
    hConnection,
    hEstablishes,
    hNetworkChain⟩

/-
Theorem — Network Representation.

Let O be an embedded observer, and let S₁ and S₂ be any two
relational domains belonging to the observer-accessible
substratum S_O.

Then, within the observer-accessible operational domain, their
relational connection admits a finite incidence-network
realization in ObserverNetwork C O.

More explicitly, there exist

    • an accessible connection distinction D, and
    • a finite list L of elementary interactions

such that L establishes the connection between S₁ and S₂ and
is realized as an incidence chain of local relational
conjunctions joined by direct relations.

Logical dependency:

    A1
      |
  Substratum Theorem
      |
  relational connectivity
      |
  operational resolution
      |
  finite operational accessibility
  (derived from accessibility + A2)
      |
  operational connection semantics
      |
      v
  finite incidence-network realization

No metric, geometry, coordinates, embedding, fixed valence,
or pairwise fundamental relation is assumed.
-/
theorem network_representation_theorem
    {M : SBI}
    (C : NetworkRealizationContext M)
    (hSemantics : OperationalConnectionSemantics C)
    (hResolution :
      OperationalResolutionOfRelConnected C.toNetworkContext)
    {O : Observer M}
    (hEmbedded :
      EmbeddedObserver
        C.toNetworkContext.toSubstratumContext O)
    {S₁ S₂ : Domain M}
    (h₁ :
      ObserverSubstratum
        C.toNetworkContext.toSubstratumContext O S₁)
    (h₂ :
      ObserverSubstratum
        C.toNetworkContext.toSubstratumContext O S₂) :

    ∃ (D : C.Distinction) (L : List M.Interaction),
      C.AccessibleDistinction O D ∧
      C.ConnectionDistinction O S₁ S₂ D ∧
      C.Establishes O D L ∧
      NetworkIncidenceChain C O L := by

  exact finite_network_realization
    C
    hSemantics
    hResolution
    hEmbedded
    h₁
    h₂

end SBI
