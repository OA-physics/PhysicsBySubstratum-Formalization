import SBILeanProject.SBI.NetworkObjects

set_option autoImplicit false

namespace SBI

/-
S2 — Operational realization of local mediation.

This module specifies the operational semantics that connect
finite local mediation to observer-accessible direct relations.
-/

/-
Observer-accessible direct mediation chain.

This strengthens DirectMediationChain by requiring the shared
relational participation between successive interactions to be
operationally distinguishable for observer O.

For successive interactions a and b we require

    ∃ p,
      AccessibleParticipation O p
      ∧ SigmaOp a p
      ∧ SigmaOp b p.

Such a p is therefore eligible to become a DirectRelation
and hence an edge of ObserverNetwork.

The empty list and a single interaction are trivially chains.

This is only a definition; no new assumption is introduced.
-/
def ObserverDirectMediationChain
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M) :
    List M.Interaction → Prop

  | [] =>
      True

  | [_] =>
      True

  | a :: b :: rest =>
      (∃ p : M.Participation,
        C.AccessibleParticipation O p ∧
        M.SigmaOp a p ∧
        M.SigmaOp b p) ∧
      ObserverDirectMediationChain C O (b :: rest)

/-
Operational accessibility of shared mediation.

For an operational witness L establishing a connection distinction
for observer O, every successive mediation link that is realized
through shared relational participation must admit at least one
shared participation that is operationally accessible to O.

This is weaker than requiring every participation in every
interaction to be observable. It says only that the relational
link by which the operational connection is established must itself
be operationally available.

This is a semantic condition on an operational connection witness,
not an additional physical axiom.
-/
def SharedMediationAccessible
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M) :
    List M.Interaction → Prop

  | [] =>
      True

  | [_] =>
      True

  | a :: b :: rest =>
      ((∃ p : M.Participation,
          M.SigmaOp a p ∧
          M.SigmaOp b p) →
       ∃ p : M.Participation,
          C.AccessibleParticipation O p ∧
          M.SigmaOp a p ∧
          M.SigmaOp b p)
      ∧
      SharedMediationAccessible C O (b :: rest)

/-
Operational connection witness.

A finite list L counts as an operational witness of the
relational connection between S₁ and S₂ for observer O when

  • D is specifically the connection distinction between S₁ and S₂;
  • L operationally establishes D;
  • L is a mediation chain;
  • the shared mediation links used by L are operationally
    accessible to O.

These conditions specify the meaning of operationally
establishing a relational connection. They are not additional
physical axioms.
-/
def OperationalConnectionWitness
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (S₁ S₂ : Domain M)
    (D : C.Distinction)
    (L : List M.Interaction) : Prop :=

  C.ConnectionDistinction O S₁ S₂ D ∧
  C.Establishes O D L ∧
  MediationChain M L ∧
  SharedMediationAccessible C O L

/-
Semantic contract for operational connection establishment.

If D is specifically the relational connection distinction
between S₁ and S₂ for observer O, and L establishes D, then L
must satisfy the full definition of an OperationalConnectionWitness.

This collects into one place what it means for a list of
elementary interactions to operationally establish a relational
connection.

It is not an additional physical axiom. It is the semantic
specification of Establishes when the distinction being
established is a connection distinction.
-/
def OperationalConnectionSemantics
    {M : SBI}
    (C : NetworkRealizationContext M) : Prop :=

  ∀ (O : Observer M)
    (S₁ S₂ : Domain M)
    (D : C.Distinction)
    (L : List M.Interaction),

    C.ConnectionDistinction O S₁ S₂ D →
    C.Establishes O D L →
    OperationalConnectionWitness C O S₁ S₂ D L

/-
Operational connection semantics implies mediation coherence.

Once the full meaning of an operational connection witness has
been specified by OperationalConnectionSemantics, the older
ConnectionEstablishmentCoherent condition follows automatically.

Thus mediation coherence is no longer an independent semantic
assumption.
-/
theorem operationalSemantics_implies_connectionCoherent
    {M : SBI}
    (C : NetworkRealizationContext M)
    (hSemantics : OperationalConnectionSemantics C) :
    ConnectionEstablishmentCoherent C.toNetworkContext := by

  intro O S₁ S₂ D L hConnection hEstablishes

  have hWitness :
      OperationalConnectionWitness C O S₁ S₂ D L :=
    hSemantics O S₁ S₂ D L hConnection hEstablishes

  exact hWitness.2.2.1
/-
Accessible shared mediation yields an observer-direct chain.

If

  • every successive pair in L shares relational participation, and
  • the shared mediation links used in the operational witness
    have observer-accessible representatives,

then every successive pair shares an observer-accessible
relational participation.

Thus:

    DirectMediationChain
        +
    SharedMediationAccessible
        --------------------------------
    ObserverDirectMediationChain

No new physical assumption is introduced in this theorem.
It merely combines the two previously stated properties.
-/
theorem directChain_is_observerDirect
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    {L : List M.Interaction}
    (hDirect : DirectMediationChain M L)
    (hAccessible : SharedMediationAccessible C O L) :
    ObserverDirectMediationChain C O L := by

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
              M.SigmaOp a p ∧ M.SigmaOp b p) ∧
            DirectMediationChain M (b :: rest)
            at hDirect

          change
            (((∃ p : M.Participation,
                M.SigmaOp a p ∧ M.SigmaOp b p) →
              ∃ p : M.Participation,
                C.AccessibleParticipation O p ∧
                M.SigmaOp a p ∧
                M.SigmaOp b p) ∧
            SharedMediationAccessible C O (b :: rest))
            at hAccessible

          rcases hDirect with
            ⟨hShared, hDirectRest⟩

          rcases hAccessible with
            ⟨hAccessibleStep, hAccessibleRest⟩

          change
            (∃ p : M.Participation,
              C.AccessibleParticipation O p ∧
              M.SigmaOp a p ∧
              M.SigmaOp b p) ∧
            ObserverDirectMediationChain C O (b :: rest)

          constructor

          · exact hAccessibleStep hShared

          · exact ih hDirectRest hAccessibleRest

/-
Operational accessibility coherence for connection witnesses.

If a list L operationally establishes a connection distinction
between S₁ and S₂ for observer O, then the shared mediation links
used by that witness must be operationally accessible to O.

This is the network-level counterpart of
ConnectionEstablishmentCoherent:

  ConnectionEstablishmentCoherent
      says the witness is a mediation chain;

  AccessibleConnectionEstablishmentCoherent
      says its relational links are accessible at the
      observer's operational resolution.

This is a semantic condition on what it means for L to
operationally establish a connection. It is not A1, A2, A3,
or FOA.
-/
def AccessibleConnectionEstablishmentCoherent
    {M : SBI}
    (C : NetworkRealizationContext M) : Prop :=

  ∀ (O : Observer M)
    (S₁ S₂ : Domain M)
    (D : C.Distinction)
    (L : List M.Interaction),

    C.ConnectionDistinction O S₁ S₂ D →
    C.Establishes O D L →
    SharedMediationAccessible C O L

/-
Operational connection semantics implies accessibility coherence.

The full OperationalConnectionSemantics already requires an
operational connection witness to have observer-accessible shared
mediation links.

Therefore AccessibleConnectionEstablishmentCoherent is not an
independent semantic assumption.
-/
theorem operationalSemantics_implies_accessibleCoherent
    {M : SBI}
    (C : NetworkRealizationContext M)
    (hSemantics : OperationalConnectionSemantics C) :
    AccessibleConnectionEstablishmentCoherent C := by

  intro O S₁ S₂ D L hConnection hEstablishes

  have hWitness :
      OperationalConnectionWitness C O S₁ S₂ D L :=
    hSemantics O S₁ S₂ D L hConnection hEstablishes

  exact hWitness.2.2.2

/-
Generic observer-resolved finite mediation from an already
established observer-resolved relational connection.
-/
theorem finite_observer_local_mediation_of_connected
    {M : SBI}
    (C : NetworkRealizationContext M)
    (hSemantics : OperationalConnectionSemantics C)
    {O : Observer M}
    {S₁ S₂ : Domain M}
    (hConnected :
      ObserverRelConnected C.toNetworkContext O S₁ S₂) :

    ∃ (D : C.Distinction) (L : List M.Interaction),
      C.AccessibleDistinction O D ∧
      C.ConnectionDistinction O S₁ S₂ D ∧
      C.Establishes O D L ∧
      ObserverDirectMediationChain C O L := by

  have hCoherent :
      ConnectionEstablishmentCoherent C.toNetworkContext :=
    operationalSemantics_implies_connectionCoherent
      C hSemantics

  have hAccessibleCoherent :
      AccessibleConnectionEstablishmentCoherent C :=
    operationalSemantics_implies_accessibleCoherent
      C hSemantics

  rcases finite_local_mediation_of_connected
    C.toNetworkContext
    hCoherent
    hConnected with
    ⟨D, L, hAccessible, hConnection, hEstablishes, hDirect⟩

  have hSharedAccessible :
      SharedMediationAccessible C O L :=
    hAccessibleCoherent
      O S₁ S₂ D L
      hConnection
      hEstablishes

  have hObserverDirect :
      ObserverDirectMediationChain C O L :=
    directChain_is_observerDirect
      C O hDirect hSharedAccessible

  exact
    ⟨D, L,
      hAccessible,
      hConnection,
      hEstablishes,
      hObserverDirect⟩

/-
Lemma — Finite observer-accessible local mediation.

If S₁ and S₂ are operationally relationally connected for
observer O, then within the observer-accessible operational domain
their connection can be established by a finite list L of
elementary interactions such that every successive pair shares
an observer-accessible relational participation.

Logical structure:

    operational accessibility
              +
             A2
              |
              v
 finite_operational_accessibility
              |
        finite witness L
              |
    OperationalConnectionSemantics
              |
      MediationChain L
        + accessible shared links
              |
              v
    ObserverDirectMediationChain L

The FOA proposition is therefore not supplied as a hypothesis here.
Its finite witness is obtained through the derived theorem in
NetworkCore.

OperationalConnectionSemantics specifies what it means for
an interaction list to establish a connection distinction.
It is not an additional physical axiom.

No geometry, metric, embedding, fixed valence, or pairwise
fundamental relation is assumed.
-/
theorem finite_observer_local_mediation
    {M : SBI}
    (C : NetworkRealizationContext M)
    (hSemantics : OperationalConnectionSemantics C)
    (hResolution :
      OperationalResolutionOfRelConnected C.toNetworkContext)
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
      ObserverDirectMediationChain C O L := by

  have hConnected :
      ObserverRelConnected C.toNetworkContext O S₁ S₂ :=
    observerSubstratum_is_operationallyConnected
      C.toNetworkContext
      hResolution
      hEmbedded
      h₁
      h₂

  exact finite_observer_local_mediation_of_connected
    C
    hSemantics
    hConnected


end SBI
