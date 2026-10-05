import Mathlib.Data.Nat.Find
import SBILeanProject.Time.Records

set_option autoImplicit false

namespace SBI.Time

/-
Local semantics required for persistent-record formation.

The manuscript distinguishes two local compatibility questions inside a
relational domain Ω:

  • does a configuration reconstruct the pre-interaction operational
    relations of X, subject to the surrounding relational context induced
    by Y?

  • does it preserve the persistence-relevant relational support of the
    record candidate R?

The SBI development already supplies relational domains, operational
configurations, and context-preserving local deformation.  What is not
fixed by that structural vocabulary is the configuration-level meaning of
"reconstructs X" or "preserves the persistence-relevant support of R".

Those meanings are therefore supplied here as semantic predicates.  They
introduce no new reachability, temporal ordering, or propagation law.
-/
structure LocalRecordFormationSemantics
    {M : SBI}
    {C : NetworkRealizationContext M}
    (K : OperationalContext C) where

  /-
  `SupportContainedIn O R Ω` means that Ω contains the
  persistence-relevant relational support of the operational distinction R.

  This is the formal counterpart of the manuscript condition that Ω contain
  the relational organization relevant to continued operational
  re-identification of R and of the persistent structures defining R.
  -/
  SupportContainedIn :
    (O : Observer M) →
    C.Distinction →
    Domain M →
    Prop

  /-
  `ReconstructsPreInteraction O Ω X Y Z` means that configuration Z
  reconstructs, within Ω, the pre-interaction operational relations
  represented by X, subject to the relational context induced by Y outside Ω.
  -/
  ReconstructsPreInteraction :
    (O : Observer M) →
    (Ω : Domain M) →
    (X Y Z : Configuration K O) →
    Prop

  /-
  `PreservesPersistenceRelevantSupport O R Ω Y Z` means that Z is
  compatible with continued operational re-identification of the persistent
  structures and relations comprising the persistence-relevant support of R,
  in the relational context induced by Y.
  -/
  PreservesPersistenceRelevantSupport :
    (O : Observer M) →
    (R : C.Distinction) →
    (Ω : Domain M) →
    (Y Z : Configuration K O) →
    Prop

/-
Local reconstruction set.

Manuscript notation:

    U_X(Ω; Y).

A configuration Z belongs to this set when, within relational domain Ω
and subject to the surrounding relational context induced by Y, it
reconstructs the pre-interaction operational relations represented by X.

`Configuration K O` already denotes an admissible global configuration.
The predicate below therefore represents the subset selected by its
behavior in Ω; no additional admissibility predicate is required.
-/
def LocalReconstructionSet
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (S : LocalRecordFormationSemantics K)
    (O : Observer M)
    (Ω : Domain M)
    (X Y : Configuration K O) :
    Configuration K O → Prop :=

  fun Z =>
    S.ReconstructsPreInteraction O Ω X Y Z


/-
Persistence-compatible configuration set.

Manuscript notation:

    U_R(Ω; Y).

A configuration Z belongs to this set when its realization within Ω,
in the relational context induced by Y, remains compatible with
operational re-identification of the persistent structures and relations
forming the persistence-relevant support of R.
-/
def PersistenceCompatibleSet
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (S : LocalRecordFormationSemantics K)
    (O : Observer M)
    (R : C.Distinction)
    (Ω : Domain M)
    (Y : Configuration K O) :
    Configuration K O → Prop :=

  fun Z =>
    S.PreservesPersistenceRelevantSupport O R Ω Y Z

/-
Local reconstruction-persistence incompatibility.

The manuscript assumes that, in a relational domain Ω containing the
relevant persistence support, no admissible configuration can simultaneously

  • reconstruct the pre-interaction organization represented by X, and
  • preserve the persistence-relevant relational support of record
    candidate R,

while the surrounding relational context is that induced by Y.

In set notation this is

    U_X(Ω; Y) ∩ U_R(Ω; Y) = ∅.

The condition that Ω actually contains the relevant support is kept as a
separate hypothesis.  This definition states only the incompatibility of
the two local requirements.
-/
def LocalReconstructionPersistenceIncompatible
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (S : LocalRecordFormationSemantics K)
    (O : Observer M)
    (R : C.Distinction)
    (Ω : Domain M)
    (X Y : Configuration K O) : Prop :=

  ¬ ∃ Z : Configuration K O,
      LocalReconstructionSet S O Ω X Y Z ∧
      PersistenceCompatibleSet S O R Ω Y Z

/-
Lemma — Local reconstruction obstruction.

Let Ω contain the persistence-relevant relational support of record
candidate R.  If

    U_X(Ω; Y) ∩ U_R(Ω; Y) = ∅,

then no admissible configuration can both reconstruct the pre-interaction
relations of X within Ω and preserve the persistence-relevant support of R
while retaining the relational context induced by Y outside Ω.

Because `LocalReconstructionSet` was defined explicitly subject to that
fixed outside context, this is the formal counterpart of the manuscript
statement that reconstruction requires reorganization beyond Ω.

The support-containment hypothesis specifies when the lemma applies
physically.  The contradiction itself follows from the empty-intersection
condition.
-/
theorem local_reconstruction_obstruction
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (S : LocalRecordFormationSemantics K)
    (O : Observer M)
    (R : C.Distinction)
    (Ω : Domain M)
    (X Y : Configuration K O)
    (_hSupport :
      S.SupportContainedIn O R Ω)
    (hIncompatible :
      LocalReconstructionPersistenceIncompatible
        S O R Ω X Y) :

    ∀ Z : Configuration K O,
      PersistenceCompatibleSet S O R Ω Y Z →
      ¬ LocalReconstructionSet S O Ω X Y Z := by

  intro Z hPersistence hReconstruction

  exact
    hIncompatible
      ⟨Z, hReconstruction, hPersistence⟩


/-
Derived nonlocal-resolution requirement.

The local obstruction theorem says that, while the persistence-relevant
support of record candidate R is retained, reconstruction of the
pre-interaction organization X cannot be completed by changing only the
relational organization inside Ω while leaving the outside context fixed.

We name that derived conclusion explicitly because it is the precise
interface needed by the next physical condition. It does NOT yet say which
outside relational structures must be reorganized. In particular, it does
not by itself imply contact with the persistence-critical dependency front.
-/
def ReconstructionRequiresNonlocalResolution
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (S : LocalRecordFormationSemantics K)
    (O : Observer M)
    (R : C.Distinction)
    (Ω : Domain M)
    (X Y : Configuration K O) : Prop :=

  ∀ Z : Configuration K O,
    PersistenceCompatibleSet S O R Ω Y Z →
    ¬ LocalReconstructionSet S O Ω X Y Z

/-
Lemma — Local incompatibility requires nonlocal resolution.

This theorem packages the local reconstruction obstruction under the name
used by the subsequent bridge. The conclusion is therefore derived from the
local incompatibility condition; no additional physical premise is
introduced here.
-/
theorem reconstruction_requires_nonlocal_resolution
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (S : LocalRecordFormationSemantics K)
    (O : Observer M)
    (R : C.Distinction)
    (Ω : Domain M)
    (X Y : Configuration K O)
    (hSupport :
      S.SupportContainedIn O R Ω)
    (hIncompatible :
      LocalReconstructionPersistenceIncompatible
        S O R Ω X Y) :

    ReconstructionRequiresNonlocalResolution
      S O R Ω X Y := by

  exact
    local_reconstruction_obstruction
      S O R Ω X Y hSupport hIncompatible

/-
Operational representation of a relational domain in the incidence network.

The SBI framework already has abstract relational domains `Domain M` and,
independently, observer-relative local relational conjunctions forming the
incidence network.

For propagation depth we must be able to say that a particular conjunction
belongs to the operational realization of a relational domain Ω.

`ConjunctionInDomain O Ω v` supplies exactly this representational bridge.

It introduces no geometry, metric, temporal order, or propagation law.
-/
structure RelationalDomainSemantics
    {M : SBI}
    {C : NetworkRealizationContext M} where

  ConjunctionInDomain :
    (O : Observer M) →
    Domain M →
    LocalRelationalConjunction C O →
    Prop

/-
One relational incidence step between local conjunctions.

The manuscript defines relational propagation depth using successive
locally mediated relational incidences connecting conjunctions.

In the incidence-network representation, two local relational conjunctions
are directly connected at one such step when they share a direct relation.

Thus `RelationallyAdjacent C O v w` means that there exists a direct
relation e incident on both v and w.

This definition introduces no metric, spatial distance, propagation speed,
or temporal parameter.  It uses only the incidence structure already
derived from local mediation.
-/
def RelationallyAdjacent
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (v w : LocalRelationalConjunction C O) : Prop :=

  ∃ e : DirectRelation C O,
    Incident C O e v ∧
    Incident C O e w

/-
Finite relational incidence chain.

`RelationalIncidenceChain C O n v w` means that v and w are connected by
exactly n successive relational-incidence steps.

The constructors have the expected interpretation:

  • `refl`:
      a conjunction is connected to itself by a chain of length zero;

  • `step`:
      if v is relationally adjacent to u and there is a chain of length n
      from u to w, then there is a chain of length n + 1 from v to w.

The natural number n counts locally mediated incidence steps.  It is not a
spatial length or a temporal duration.

This object will be used next to define the manuscript's relational
propagation depth d(v,w) as the minimum possible chain length.
-/
inductive RelationalIncidenceChain
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M) :
    Nat →
    LocalRelationalConjunction C O →
    LocalRelationalConjunction C O →
    Prop

  | refl
      (v : LocalRelationalConjunction C O) :
      RelationalIncidenceChain C O 0 v v

  | step
      {n : Nat}
      {v u w : LocalRelationalConjunction C O}
      (hAdjacent :
        RelationallyAdjacent C O v u)
      (hRest :
        RelationalIncidenceChain C O n u w) :
      RelationalIncidenceChain C O (n + 1) v w

/-
Relational propagation depth.

Manuscript notation:

    d(v,w).

A natural number n is the relational propagation depth from conjunction v
to conjunction w when

  • there exists a relational-incidence chain of exactly n steps from v
    to w; and

  • every relational-incidence chain from v to w has length at least n.

Thus n is the minimum number of successive locally mediated relational
incidences connecting v and w.

This is a purely combinatorial depth in the incidence structure.  It is
not a geometric distance and introduces no spatial metric or temporal
duration.

We use a proposition rather than immediately defining a total function
d(v,w), because the present formalization has not yet asserted that every
mathematically representable pair of conjunctions is connected by such a
chain.
-/
def RelationalPropagationDepth
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (v w : LocalRelationalConjunction C O)
    (n : Nat) : Prop :=

  RelationalIncidenceChain C O n v w ∧
  ∀ m : Nat,
    RelationalIncidenceChain C O m v w →
    n ≤ m

/-
Relational propagation depth from a conjunction to a relational domain.

Manuscript notation:

    d(v, Ω) = min_{w ∈ Ω} d(v,w).

A natural number n is the depth of v from Ω when

  • some conjunction w belonging to Ω has pairwise propagation depth n
    from v; and

  • no conjunction belonging to Ω has a smaller defined pairwise depth.

As with pairwise propagation depth, this is represented as a proposition
rather than a total numerical function.  We therefore do not assume that
every mathematically representable conjunction is connected to Ω.
-/
def RelationalPropagationDepthToDomain
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (v : LocalRelationalConjunction C O)
    (n : Nat) : Prop :=

  (∃ w : LocalRelationalConjunction C O,
      RDom.ConjunctionInDomain O Ω w ∧
      RelationalPropagationDepth C O v w n)
  ∧
  ∀ (w : LocalRelationalConjunction C O) (m : Nat),
    RDom.ConjunctionInDomain O Ω w →
    RelationalPropagationDepth C O v w m →
    n ≤ m


/-
Relational shell of depth n about a relational domain Ω.

Manuscript notation:

    ∂ₙ Ω = { v : d(v, Ω) = n }.

A conjunction belongs to the nth relational shell exactly when its
minimum relational propagation depth from Ω is n.

The shell is represented as a predicate on local relational conjunctions.
It is purely relational and combinatorial: no background geometry,
coordinate radius, or spatial metric is introduced.
-/
def RelationalShell
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (n : Nat) :
    LocalRelationalConjunction C O → Prop :=

  fun v =>
    RelationalPropagationDepthToDomain
      C RDom O Ω v n

/-
Limiting relational propagation front.

Manuscript notation:

    Fₙ ⊆ ∂ₙ Ω.

A propagation front is represented as a predicate on local relational
conjunctions.  It is limiting at propagation stage n when every conjunction
belonging to the front has minimum relational propagation depth exactly n
from the reference domain Ω.

The stage number is therefore encoded relationally by shell depth.  No
background time, spatial radius, or propagation velocity is introduced.
-/
def LimitingPropagationFront
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (n : Nat)
    (F : LocalRelationalConjunction C O → Prop) : Prop :=

  ∀ v : LocalRelationalConjunction C O,
    F v →
    RelationalShell C RDom O Ω n v

/-
Conjunction lying within a bounded relational propagation depth.

`WithinRelationalDepth C RDom O Ω r v` means that the conjunction v has
some defined minimum propagation depth d from Ω with

    d ≤ r.

This represents the manuscript set

    { v : d(v, Ω) ≤ r }.

The bound is entirely relational.  It does not describe a geometric ball
or a distance travelled in physical time.
-/
def WithinRelationalDepth
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (r : Nat)
    (v : LocalRelationalConjunction C O) : Prop :=

  ∃ d : Nat,
    RelationalPropagationDepthToDomain
      C RDom O Ω v d
    ∧
    d ≤ r

/-
Stage-by-stage locally mediated reconstruction propagation.

The manuscript denotes by Q_m the relational support reachable by a
reconstruction influence after m further propagation stages.

To formalize the statement that such influence propagates only through
successive locally mediated interactions, we represent its support at each
stage and require that every newly reached conjunction be either

  • already present at the preceding stage, or
  • relationally adjacent to some conjunction present at the preceding
    stage.

Thus one propagation stage can enlarge the support by at most one
relational-incidence step.

`initial_bound` formalizes the statement that reconstruction begins k
propagation stages behind a limiting front at depth n.  The hypothesis
k ≤ n is explicit because shell depths are natural numbers and the
initial bound is n - k.

No temporal duration is represented by the stage index.  It counts only
successive locally mediated propagation steps.
-/
structure LocallyMediatedReconstructionPropagation
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (n k : Nat) where

  support :
    Nat →
    LocalRelationalConjunction C O →
    Prop

    /-
  The reconstruction lag k cannot exceed the current front depth n.

  This makes the natural-number expression n - k represent the intended
  depth k stages behind the front, rather than truncated subtraction.
  -/
  lag_within_front :
    k ≤ n

  initial_bound :
    ∀ v : LocalRelationalConjunction C O,
      support 0 v →
      WithinRelationalDepth
        C RDom O Ω (n - k) v

  step_local :
    ∀ (m : Nat)
      (v : LocalRelationalConjunction C O),
      support (m + 1) v →
      support m v ∨
      ∃ u : LocalRelationalConjunction C O,
        support m u ∧
        RelationallyAdjacent C O u v


/-
Relational adjacency is symmetric.

If conjunctions v and w share a direct relation e, then the same e also
witnesses adjacency from w to v.

This is a property of the incidence representation itself; no reversible
dynamics or temporal assumption is involved.
-/
theorem relationallyAdjacent_symm
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    {v w : LocalRelationalConjunction C O}
    (hAdjacent :
      RelationallyAdjacent C O v w) :

    RelationallyAdjacent C O w v := by

  rcases hAdjacent with
    ⟨e, hev, hew⟩

  exact
    ⟨e, hew, hev⟩

/-
Relational propagation depth is unique when it exists.

If both n₁ and n₂ satisfy the minimum-chain characterization of d(v,w),
then each must be less than or equal to the other.  Hence n₁ = n₂.

This justifies treating `RelationalPropagationDepth` as the graph of a
well-defined partial numerical function, without assuming that a depth
exists for every pair of conjunctions.
-/
theorem relationalPropagationDepth_unique
    {M : SBI}
    (C : NetworkRealizationContext M)
    (O : Observer M)
    (v w : LocalRelationalConjunction C O)
    {n₁ n₂ : Nat}
    (h₁ :
      RelationalPropagationDepth C O v w n₁)
    (h₂ :
      RelationalPropagationDepth C O v w n₂) :

    n₁ = n₂ := by

  apply Nat.le_antisymm

  · exact h₁.2 n₂ h₂.1

  · exact h₂.2 n₁ h₁.1

/-
Relational propagation depth to a domain is unique when it exists.

If both n₁ and n₂ satisfy the minimum-depth characterization of d(v, Ω),
then each is bounded above by the other, using a minimizing conjunction
witness from the opposite characterization.  Hence n₁ = n₂.

This makes the shell index in

    ∂ₙ Ω = { v : d(v, Ω) = n }

well defined whenever the depth exists.
-/
theorem relationalPropagationDepthToDomain_unique
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (v : LocalRelationalConjunction C O)
    {n₁ n₂ : Nat}
    (h₁ :
      RelationalPropagationDepthToDomain
        C RDom O Ω v n₁)
    (h₂ :
      RelationalPropagationDepthToDomain
        C RDom O Ω v n₂) :

    n₁ = n₂ := by

  rcases h₁.1 with
    ⟨w₁, hw₁Domain, hw₁Depth⟩

  rcases h₂.1 with
    ⟨w₂, hw₂Domain, hw₂Depth⟩

  apply Nat.le_antisymm

  · exact h₁.2 w₂ n₂ hw₂Domain hw₂Depth

  · exact h₂.2 w₁ n₁ hw₁Domain hw₁Depth

/-
Relational shells at distinct depths are disjoint.

If a conjunction v belongs both to ∂ₙ₁ Ω and to ∂ₙ₂ Ω, then the uniqueness
of relational propagation depth to Ω forces

    n₁ = n₂.

Thus two shells with different depth labels cannot share a conjunction.
This is the basic combinatorial separation later used in the no-overtaking
argument.
-/
theorem relationalShell_depth_unique
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (v : LocalRelationalConjunction C O)
    {n₁ n₂ : Nat}
    (h₁ :
      RelationalShell C RDom O Ω n₁ v)
    (h₂ :
      RelationalShell C RDom O Ω n₂ v) :

    n₁ = n₂ := by

  exact
    relationalPropagationDepthToDomain_unique
      C RDom O Ω v h₁ h₂


/-
A finite incidence chain to a conjunction in Ω produces a defined
minimum propagation depth to Ω, bounded by the length of that chain.

This is the existence counterpart to the uniqueness theorem below.
Because chain lengths are natural numbers, any nonempty collection of
admissible chain lengths has a least element.

The proof minimizes globally over all chains from v to conjunctions in Ω.
That global minimum is also the pairwise minimum to its witnessing
conjunction: any shorter chain to that same conjunction would contradict
global minimality.
-/
theorem exists_relationalPropagationDepthToDomain_le_of_chain
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (v w : LocalRelationalConjunction C O)
    (m : Nat)
    (hwDomain :
      RDom.ConjunctionInDomain O Ω w)
    (hChain :
      RelationalIncidenceChain C O m v w) :

    ∃ n : Nat,
      RelationalPropagationDepthToDomain
        C RDom O Ω v n
      ∧
      n ≤ m := by

  classical

  let P : Nat → Prop :=
    fun d =>
      ∃ w' : LocalRelationalConjunction C O,
        RDom.ConjunctionInDomain O Ω w' ∧
        RelationalIncidenceChain C O d v w'

  have hExists : ∃ d : Nat, P d := by
    exact ⟨m, w, hwDomain, hChain⟩

  let n : Nat :=
    Nat.find hExists

  have hnP : P n := by
    exact Nat.find_spec hExists

  rcases hnP with
    ⟨w₀, hw₀Domain, hw₀Chain⟩

  have hPairDepth :
      RelationalPropagationDepth C O v w₀ n := by

    constructor

    · exact hw₀Chain

    · intro d hdChain

      exact
        Nat.find_min'
          hExists
          ⟨w₀, hw₀Domain, hdChain⟩

  have hDomainDepth :
      RelationalPropagationDepthToDomain
        C RDom O Ω v n := by

    constructor

    · exact
        ⟨w₀, hw₀Domain, hPairDepth⟩

    · intro w' d hw'Domain hdDepth

      exact
        Nat.find_min'
          hExists
          ⟨w', hw'Domain, hdDepth.1⟩

  refine ⟨n, hDomainDepth, ?_⟩

  exact
    Nat.find_min'
      hExists
      ⟨w, hwDomain, hChain⟩

/-
One locally mediated incidence step increases the depth bound by at most one.

Suppose u lies within relational propagation depth r of Ω and v is
relationally adjacent to u.

Choose a conjunction w in Ω realizing the minimum depth d of u from Ω.
There is therefore an incidence chain of length d from u to w, with d ≤ r.

Since v is adjacent to u, prepending that one incidence step gives a chain
of length d + 1 from v to w.  Hence v has some defined minimum depth from Ω
no greater than d + 1, and therefore no greater than r + 1.

This is the formal local-propagation statement required for the later
no-overtaking induction.
-/
theorem withinRelationalDepth_of_adjacent
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (r : Nat)
    {u v : LocalRelationalConjunction C O}
    (hWithin :
      WithinRelationalDepth
        C RDom O Ω r u)
    (hAdjacent :
      RelationallyAdjacent C O u v) :

    WithinRelationalDepth
      C RDom O Ω (r + 1) v := by

  rcases hWithin with
    ⟨d, hdDomain, hd_le_r⟩

  rcases hdDomain.1 with
    ⟨w, hwDomain, huwDepth⟩

  have hvwChain :
      RelationalIncidenceChain C O (d + 1) v w := by

    exact
      RelationalIncidenceChain.step
        (relationallyAdjacent_symm C O hAdjacent)
        huwDepth.1

  rcases
      exists_relationalPropagationDepthToDomain_le_of_chain
        C RDom O Ω v w (d + 1)
        hwDomain
        hvwChain with
    ⟨d', hd'Domain, hd'_le⟩

  refine
    ⟨d', hd'Domain, ?_⟩

  exact
    le_trans
      hd'_le
      (Nat.add_le_add_right hd_le_r 1)

/-
Monotonicity of bounded relational depth.

If v lies within relational depth r of Ω and r ≤ s, then v also lies
within relational depth s.

This is bookkeeping for the propagation induction: a conjunction already
present at one stage remains inside the enlarged depth bound at the next
stage even when no new incidence step is taken.
-/
theorem withinRelationalDepth_mono
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    {r s : Nat}
    {v : LocalRelationalConjunction C O}
    (hrs : r ≤ s)
    (hWithin :
      WithinRelationalDepth
        C RDom O Ω r v) :

    WithinRelationalDepth
      C RDom O Ω s v := by

  rcases hWithin with
    ⟨d, hdDepth, hd_le_r⟩

  exact
    ⟨d, hdDepth, le_trans hd_le_r hrs⟩

/-
Locally mediated reconstruction cannot advance by more than one
relational shell per propagation stage.

If reconstruction support begins within depth

    n - k

of Ω, and each subsequent stage can only retain already reached
conjunctions or add conjunctions adjacent to the preceding support, then
after m stages every reached conjunction lies within depth

    (n - k) + m.

This is the formal counterpart of the manuscript bound

    Q_m ⊆ { v : d(v, Ω) ≤ n - k + m }.

The proof is by induction on m:

  • at m = 0 the result is exactly `initial_bound`;

  • an already present conjunction remains inside the enlarged bound;

  • a newly reached adjacent conjunction increases the bound by at most
    one, by `withinRelationalDepth_of_adjacent`.
-/
theorem LocallyMediatedReconstructionPropagation.support_within_bound
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (n k : Nat)
    (P :
      LocallyMediatedReconstructionPropagation
        C RDom O Ω n k) :

    ∀ (m : Nat)
      (v : LocalRelationalConjunction C O),
      P.support m v →
      WithinRelationalDepth
        C RDom O Ω ((n - k) + m) v := by

  intro m

  induction m with

  | zero =>

      intro v hv

      simpa using
        P.initial_bound v hv

  | succ m ih =>

      intro v hv

      have hStep :
          P.support m v ∨
          ∃ u : LocalRelationalConjunction C O,
            P.support m u ∧
            RelationallyAdjacent C O u v := by

        exact
          P.step_local m v
            (by
              simpa [Nat.succ_eq_add_one] using hv)

      rcases hStep with hOld | ⟨u, hu, hAdjacent⟩

      ·
        have hWithin :
            WithinRelationalDepth
              C RDom O Ω ((n - k) + m) v :=
          ih v hOld

        exact
          withinRelationalDepth_mono
            C RDom O Ω
            (Nat.add_le_add_left
              (Nat.le_succ m)
              (n - k))
            hWithin

      ·
        have huWithin :
            WithinRelationalDepth
              C RDom O Ω ((n - k) + m) u :=
          ih u hu

        have hvWithin :
            WithinRelationalDepth
              C RDom O Ω (((n - k) + m) + 1) v :=
          withinRelationalDepth_of_adjacent
            C RDom O Ω
            ((n - k) + m)
            huWithin
            hAdjacent

        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hvWithin

/-
A positive reconstruction lag is preserved under equal-rate propagation.

Suppose the limiting front is initially at relational depth n and the
reconstruction support begins k stages behind it, with

    0 < k
    and
    k ≤ n.

Then after any equal number m of further locally mediated propagation
stages,

    (n - k) + m < n + m.

This is the arithmetic core of the no-overtaking argument: propagation at
the same maximal relational rate cannot eliminate a pre-existing positive
depth lag.
-/
theorem reconstruction_lag_remains_strict
    (n k m : Nat)
    (hkPos : 0 < k)
    (hk_le_n : k ≤ n) :

    (n - k) + m < n + m := by

  have hnPos : 0 < n :=
    lt_of_lt_of_le hkPos hk_le_n

  have hSub :
      n - k < n :=
    Nat.sub_lt hnPos hkPos

  exact
    Nat.add_lt_add_right hSub m

/-
A bounded reconstruction support cannot intersect a strictly deeper shell.

Suppose v lies within relational depth r of Ω, while the shell under
consideration has exact depth s with

    r < s.

If v also belonged to ∂ₛ Ω, then v would have both

    d(v, Ω) = d   with d ≤ r

and

    d(v, Ω) = s.

Uniqueness of propagation depth forces d = s, giving s ≤ r, which
contradicts r < s.

This is the set-theoretic separation needed in the no-overtaking proof.
-/
theorem withinRelationalDepth_not_shell_of_lt
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    {r s : Nat}
    {v : LocalRelationalConjunction C O}
    (hrs : r < s)
    (hWithin :
      WithinRelationalDepth
        C RDom O Ω r v) :

    ¬ RelationalShell
        C RDom O Ω s v := by

  intro hShell

  rcases hWithin with
    ⟨d, hdDepth, hd_le_r⟩

  have hEq :
      d = s :=
    relationalPropagationDepthToDomain_unique
      C RDom O Ω v
      hdDepth
      hShell

  have hs_le_r :
      s ≤ r := by
    simpa [hEq] using hd_le_r

  exact
    (Nat.not_le_of_gt hrs) hs_le_r

/-
Theorem — No overtaking of a limiting propagation front.

Suppose a reconstruction influence begins k > 0 relational propagation
stages behind a limiting front initially at depth n, and both can propagate
only through successive locally mediated relational incidences.

After any further number m of propagation stages:

  • reconstruction support is confined to depth at most

        (n - k) + m;

  • the limiting front lies exactly on shell

        ∂_(n + m) Ω.

Because the positive lag remains strict,

    (n - k) + m < n + m,

no conjunction can belong simultaneously to the reconstruction support
and to the limiting front.

This is the formal no-overtaking result.  It uses no background spatial
velocity or external time parameter: the comparison is entirely in
relational propagation depth.
-/
theorem LocallyMediatedReconstructionPropagation.cannot_overtake_limiting_front
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (n k : Nat)
    (P :
      LocallyMediatedReconstructionPropagation
        C RDom O Ω n k)
    (hkPos : 0 < k)
    (m : Nat)
    (F : LocalRelationalConjunction C O → Prop)
    (hFront :
      LimitingPropagationFront
        C RDom O Ω (n + m) F) :

    ∀ v : LocalRelationalConjunction C O,
      P.support m v →
      F v →
      False := by

  intro v hSupport hFrontAtV

  have hWithin :
      WithinRelationalDepth
        C RDom O Ω ((n - k) + m) v :=
    LocallyMediatedReconstructionPropagation.support_within_bound
      C RDom O Ω n k P m v hSupport

  have hLag :
      (n - k) + m < n + m :=
    reconstruction_lag_remains_strict
      n k m hkPos P.lag_within_front

  have hNotShell :
      ¬ RelationalShell
          C RDom O Ω (n + m) v :=
    withinRelationalDepth_not_shell_of_lt
      C RDom O Ω hLag hWithin

  exact
    hNotShell
      (hFront v hFrontAtV)

/-
Propagation of a persistence-critical relational dependency.

The record-formation theorem assumes that the interaction produces a
persistence-critical relational dependency whose leading support propagates
along a limiting relational chain.

`LimitingDependencyPropagation` represents that propagating dependency by a
family of relational fronts indexed by propagation stage.

At stage m,

    front m

is required to lie on the relational shell

    ∂_(n + m) Ω,

where n is the initial front depth.

The stage index counts successive locally mediated propagation steps only.
It is not a background temporal parameter.
-/
structure LimitingDependencyPropagation
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (n : Nat) where

  front :
    Nat →
    LocalRelationalConjunction C O →
    Prop

  limiting :
    ∀ m : Nat,
      LimitingPropagationFront
        C RDom O Ω (n + m) (front m)

/-
Reconstruction support remains disjoint from a limiting dependency front
at every propagation stage.

This packages the pointwise no-overtaking theorem together with
`LimitingDependencyPropagation`.  At every stage m, the reconstruction
support and the persistence-critical dependency front have empty
intersection.
-/
theorem LocallyMediatedReconstructionPropagation.disjoint_from_limiting_dependency
    {M : SBI}
    (C : NetworkRealizationContext M)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (n k : Nat)
    (P :
      LocallyMediatedReconstructionPropagation
        C RDom O Ω n k)
    (L :
      LimitingDependencyPropagation
        C RDom O Ω n)
    (hkPos : 0 < k) :

    ∀ (m : Nat)
      (v : LocalRelationalConjunction C O),
      P.support m v →
      ¬ L.front m v := by

  intro m v hSupport hFront

  exact
    LocallyMediatedReconstructionPropagation.cannot_overtake_limiting_front
      C RDom O Ω n k P hkPos
      m
      (L.front m)
      (L.limiting m)
      v
      hSupport
      hFront

/-
Physical condition — dependency-mediated outward recovery.

The local obstruction proves only that reconstruction cannot be completed
inside Ω while preserving the persistence-relevant support of R. It does
not determine which outside relational structures a successful
reconstruction must reorganize.

For the class of record-forming interactions considered here we therefore
state one additional physical condition: whenever successful reconstruction
requires nonlocal resolution in the above sense, that outward recovery must
encounter the persistence-critical dependency generated by the interaction.

Operationally, encountering that dependency means that at some propagation
stage the reconstruction support intersects the corresponding dependency
front.

This condition is intentionally conditional. It does not assert that every
interaction has this property, and it introduces no new propagation law.
-/
structure DependencyMediatedOutwardRecovery
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (S : LocalRecordFormationSemantics K)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (R : C.Distinction)
    (Ω : Domain M)
    (n k : Nat)
    (P :
      LocallyMediatedReconstructionPropagation
        C RDom O Ω n k)
    (L :
      LimitingDependencyPropagation
        C RDom O Ω n)
    (X Y : Configuration K O) where

  recovery_required :
    ReconstructionRequiresNonlocalResolution
        S O R Ω X Y →
    OperationallyReconstructible D A O X Y →
    ∃ (m : Nat)
      (v : LocalRelationalConjunction C O),
      P.support m v ∧
      L.front m v

/-
Reconstruction requires recovery of the persistence-critical dependency.

This structure is the interface consumed by the no-overtaking theorem: any
successful reconstruction must, at some propagation stage, bring
reconstruction support into contact with the corresponding dependency front.

In the main persistent-record construction below this object is no longer
an independent physical premise. It is derived from the local obstruction
together with dependency-mediated outward recovery.
-/
structure ReconstructionRequiresDependencyRecovery
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (n k : Nat)
    (P :
      LocallyMediatedReconstructionPropagation
        C RDom O Ω n k)
    (L :
      LimitingDependencyPropagation
        C RDom O Ω n)
    (X Y : Configuration K O) where

  recovery_required :
    OperationallyReconstructible D A O X Y →
    ∃ (m : Nat)
      (v : LocalRelationalConjunction C O),
      P.support m v ∧
      L.front m v


/-
Derived dependency-recovery requirement.

Combining the derived local reconstruction obstruction with the physical
condition of dependency-mediated outward recovery yields the exact
configuration-level statement required by the no-overtaking argument.
-/
theorem reconstructionRequiresDependencyRecovery_of_local_obstruction
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (S : LocalRecordFormationSemantics K)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (R : C.Distinction)
    (Ω : Domain M)
    (n k : Nat)
    (P :
      LocallyMediatedReconstructionPropagation
        C RDom O Ω n k)
    (L :
      LimitingDependencyPropagation
        C RDom O Ω n)
    (X Y : Configuration K O)
    (hSupport :
      S.SupportContainedIn O R Ω)
    (hIncompatible :
      LocalReconstructionPersistenceIncompatible
        S O R Ω X Y)
    (HOutward :
      DependencyMediatedOutwardRecovery
        D A S RDom O R Ω n k P L X Y) :

    ReconstructionRequiresDependencyRecovery
      D A RDom O Ω n k P L X Y := by

  refine
    { recovery_required := ?_ }

  intro hReconstructible

  exact
    HOutward.recovery_required
      (reconstruction_requires_nonlocal_resolution
        S O R Ω X Y hSupport hIncompatible)
      hReconstructible

/-
Successful reconstruction is impossible when recovery of the
persistence-critical dependency is required.

Any operational reconstruction of X from Y would, by
`ReconstructionRequiresDependencyRecovery`, force reconstruction support
to meet the limiting dependency front at some stage.

But `disjoint_from_limiting_dependency` proves that such an intersection
is impossible whenever the reconstruction begins with a positive lag.

Therefore X is not operationally reconstructible from Y.
-/
theorem ReconstructionRequiresDependencyRecovery.not_operationally_reconstructible
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (n k : Nat)
    (P :
      LocallyMediatedReconstructionPropagation
        C RDom O Ω n k)
    (L :
      LimitingDependencyPropagation
        C RDom O Ω n)
    (X Y : Configuration K O)
    (H :
      ReconstructionRequiresDependencyRecovery
        D A RDom O Ω n k P L X Y)
    (hkPos : 0 < k) :

    ¬ OperationallyReconstructible D A O X Y := by

  intro hReconstructible

  rcases H.recovery_required hReconstructible with
    ⟨m, v, hSupport, hFront⟩

  exact
    (LocallyMediatedReconstructionPropagation.disjoint_from_limiting_dependency
      C RDom O Ω n k P L hkPos
      m v hSupport)
      hFront

/-
A limiting persistence-critical dependency produces a persistent record
once the remaining record conditions are satisfied.

The reconstruction logic is now explicit. Local reconstruction-persistence
incompatibility first implies that reconstruction cannot be completed inside
Ω while preserving the persistence-relevant support of R. The physical
condition DependencyMediatedOutwardRecovery then states that, for the class
of interactions considered, such nonlocal reconstruction must encounter the
persistence-critical dependency. This derives
ReconstructionRequiresDependencyRecovery.

The no-overtaking argument makes that required encounter impossible when
the reconstruction begins with a positive lag, yielding operational
non-reconstructibility.

To obtain a PersistentRecord, we additionally supply the properties that
belong to the definition of the record itself:

  • the interaction X →* Y actually occurred operationally;
  • the record feature R is present in Y;
  • R distinguishes Y from X;
  • eliminating R together with its relevant dependencies requires
    operational reconstruction of X.

Thus the final theorem no longer assumes the broad dependency-recovery
statement independently: it derives it from the local obstruction plus the
more specific physical condition governing outward recovery.
-/
theorem persistentRecord_of_limiting_dependency
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (F : RecordFeatureSemantics K)
    (S : LocalRecordFormationSemantics K)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (n k : Nat)
    (P :
      LocallyMediatedReconstructionPropagation
        C RDom O Ω n k)
    (L :
      LimitingDependencyPropagation
        C RDom O Ω n)
    (X Y : Configuration K O)
    (R : C.Distinction)
    (hForward :
      OperationalReachability D A O X Y)
    (hPresent :
      F.PresentIn O Y R)
    (hDistinguishes :
      F.Distinguishes O X Y R)
    (hElimination :
      ∀ Z : Configuration K O,
        F.EliminatedWithDependencies O X Y R Z →
        OperationalReachability D A O Z X)
    (hSupport :
      S.SupportContainedIn O R Ω)
    (hIncompatible :
      LocalReconstructionPersistenceIncompatible
        S O R Ω X Y)
    (HOutward :
      DependencyMediatedOutwardRecovery
        D A S RDom O R Ω n k P L X Y)
    (hkPos : 0 < k) :

    PersistentRecord D A F O X Y R := by

  have HRecovery :
      ReconstructionRequiresDependencyRecovery
        D A RDom O Ω n k P L X Y :=
    reconstructionRequiresDependencyRecovery_of_local_obstruction
      D A S RDom O R Ω n k P L X Y
      hSupport hIncompatible HOutward

  refine
    { forward_reachable := hForward
      present_in_post := hPresent
      distinguishes_post_from_pre := hDistinguishes
      elimination_requires_reconstruction := hElimination
      reconstruction_inaccessible := ?_ }

  exact
    ReconstructionRequiresDependencyRecovery.not_operationally_reconstructible
      D A RDom O Ω n k P L X Y HRecovery hkPos


/-
Bundle theorem — persistent-record consequences.

This theorem collects the principal consequences of the record-formation
branch into one manuscript-facing result.

Under the same sufficient conditions used by the persistent-record theorem,
the interaction X →* Y:

  1. produces a persistent record R;

  2. makes complete elimination of R together with its relevant dependencies
     operationally unreachable from Y;

  3. establishes asymmetric operational reachability from X to Y;

  4. therefore induces irreversible precedence between the corresponding
     reversible equivalence classes.

No additional physical assumption is introduced here. The theorem simply
packages the already proved record-formation theorem and its principal
physical corollaries into one recognizable endpoint for the dependency map.
-/
theorem persistentRecord_consequences
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (F : RecordFeatureSemantics K)
    (S : LocalRecordFormationSemantics K)
    (RDom : RelationalDomainSemantics (C := C))
    (O : Observer M)
    (Ω : Domain M)
    (n k : Nat)
    (P :
      LocallyMediatedReconstructionPropagation
        C RDom O Ω n k)
    (L :
      LimitingDependencyPropagation
        C RDom O Ω n)
    (X Y : Configuration K O)
    (R : C.Distinction)
    (hForward :
      OperationalReachability D A O X Y)
    (hPresent :
      F.PresentIn O Y R)
    (hDistinguishes :
      F.Distinguishes O X Y R)
    (hElimination :
      ∀ Z : Configuration K O,
        F.EliminatedWithDependencies O X Y R Z →
        OperationalReachability D A O Z X)
    (hSupport :
      S.SupportContainedIn O R Ω)
    (hIncompatible :
      LocalReconstructionPersistenceIncompatible
        S O R Ω X Y)
    (HOutward :
      DependencyMediatedOutwardRecovery
        D A S RDom O R Ω n k P L X Y)
    (hkPos : 0 < k) :

    PersistentRecord D A F O X Y R
    ∧
    (∀ {Z : Configuration K O},
      F.EliminatedWithDependencies O X Y R Z →
      ¬ OperationalReachability D A O Y Z)
    ∧
    AsymmetricReachability D A O X Y
    ∧
    IrreversiblePrecedence D A O
      (reversibleClassOf D A O X)
      (reversibleClassOf D A O Y) := by

  have hRecord :
      PersistentRecord D A F O X Y R :=
    persistentRecord_of_limiting_dependency
      D A F S RDom O Ω n k P L X Y R
      hForward hPresent hDistinguishes hElimination
      hSupport hIncompatible HOutward hkPos

  constructor

  · exact hRecord

  constructor

  · intro Z hEliminated
    exact
      hRecord.elimination_not_reachable
        D A F O X Y R hEliminated

  constructor

  · exact
      hRecord.asymmetricReachability
        D A F O X Y R

  · exact
      hRecord.irreversiblePrecedence
        D A F O X Y R

end SBI.Time
