import SBILeanProject.SBI.NetworkCore

set_option autoImplicit false

namespace SBI

/-
S2 — Incidence-network objects.

This module introduces the observer-level relational objects
used in the network representation: direct relations, local
relational conjunctions, incidence, and the abstract network
G_O = (V_O, E_O, ι_O).
-/

/-
Additional context needed for the network representation.

The preceding finite-local-mediation lemma is already complete
and does not depend on this structure.

AccessibleParticipation O p means that relational participation p
is operationally distinguishable for observer O.

No graph, edge, vertex, geometry, or pairwise relation is assumed.
-/
structure NetworkRealizationContext (M : SBI)
    extends NetworkContext M where

  AccessibleParticipation :
    Observer M → M.Participation → Prop

/-
Definition — Direct relation.

A relational participation p is a direct relation for observer O
when

  1. p is operationally distinguishable for O, and
  2. p is operationally resolved in at least one elementary
     admissible interaction.

Manuscript content:

    direct relation
      = observer-accessible relational participation
        belonging to SigmaOp(a) for some elementary interaction a.

Using SigmaOp here is essential: the manuscript definition concerns
operationally distinguished participation, not arbitrary microscopic
participation in the unrestricted Sigma(a).

This definition does NOT make relations pairwise. A single
participation p may occur in arbitrarily many elementary
interactions and, later, may be incident on arbitrarily many
local relational conjunctions.
-/
def IsDirectRelation
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (p : M.Participation) : Prop :=

  C.AccessibleParticipation O p ∧
  ∃ a : M.Interaction,
    M.SigmaOp a p

/-
The type of direct relations accessible to observer O.

An element e : DirectRelation C O contains:

  • an underlying relational participation e.val;
  • a proof that this participation is operationally accessible
    and capable of elementary interaction.

This is still not yet a graph edge. It is the relational object
from which the eventual edge set E will be built.
-/
def DirectRelation
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M) :=
  {p : M.Participation // IsDirectRelation C O p}

/-
Definition — Local relational conjunction.

A local relational conjunction J is a collection of direct
relations that are jointly operationally resolved in one elementary
admissible interaction.

J is represented as a predicate on DirectRelation:

    J e

means that the direct relation e belongs to the conjunction.

The existential witness a is the elementary interaction in
which all and only the observer-accessible direct relations
belonging to J occur in SigmaOp(a).

No number of relations in J is assumed. In particular, a
conjunction may involve two, three, or arbitrarily many direct
relations.
-/
def IsLocalRelationalConjunction
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (J : DirectRelation C O → Prop) : Prop :=

  ∃ a : M.Interaction,
    ∀ e : DirectRelation C O,
      J e ↔ M.SigmaOp a e.val

/-
The type of local relational conjunctions accessible to observer O.

An element v : LocalRelationalConjunction C O consists of

  • a collection of direct relations, represented by v.val;
  • a proof that this collection is exactly the operationally
    resolved direct-relation content of an elementary admissible
    interaction.

These objects will become the vertices V of the incidence
network.

No fixed valence or relation arity is assumed.
-/
def LocalRelationalConjunction
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M) :=
  {J : DirectRelation C O → Prop //
    IsLocalRelationalConjunction C O J}

/-
Definition — Incidence relation.

A direct relation e is incident on a local relational
conjunction v exactly when e belongs to the collection of
direct relations represented by v.

Manuscript notation:

    ι ⊆ E × V

with

    ι(e,v)

meaning that relation e participates in conjunction v.

This incidence relation imposes no fixed arity:

  • one conjunction may contain arbitrarily many relations;
  • one direct relation may be incident on arbitrarily many
    conjunctions.

Thus the construction is not restricted to pairwise relations
or ordinary graph valence.
-/
def Incident
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (e : DirectRelation C O)
    (v : LocalRelationalConjunction C O) : Prop :=

  v.val e

/-
Abstract incidence network.

An incidence network consists only of:

  • a type V of vertices,
  • a type E of edges/direct relations,
  • an incidence relation ι : E → V → Prop.

Unlike an ordinary graph definition, this does NOT require
each edge to have exactly two endpoints.

This is therefore suitable for the relational realization used
in the manuscript, where a direct relation may participate in
any number of local relational conjunctions.
-/
structure IncidenceNetwork where

  Vertex : Type

  Edge : Type

  Incidence :
    Edge → Vertex → Prop

/-
Observer-relative incidence-network realization.

For observer O:

  • vertices are local relational conjunctions;
  • edges are direct relations;
  • incidence is participation of a direct relation in a
    local relational conjunction.

This realizes the manuscript structure

    G_O = (V_O, E_O, ι_O)

without introducing geometry, coordinates, edge lengths,
fixed valence, or pairwise endpoint structure.
-/
def ObserverNetwork
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M) :
    IncidenceNetwork where

  Vertex :=
    LocalRelationalConjunction C O

  Edge :=
    DirectRelation C O

  Incidence :=
    fun e v => Incident C O e v


end SBI
