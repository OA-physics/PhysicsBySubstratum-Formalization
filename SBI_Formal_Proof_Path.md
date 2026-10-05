# SBI Formal Proof Path

**Project:** *Consequences of Strict Background Independence*  
**Purpose:** human-readable guide to the formal derivation in Supplementary Discussion S2  
**Detailed audit:** `SBI_Formal_Verification_Traceability_Matrix.md`  
**Machine-level audit:** declaration-level and grouped dependency reports in this repository  
**Lean-source baseline:** commit `7739ff642902dc51f7d9e89d63f49c02298c09c6` (`Initial verified S2 formalization`)  
**S2 source baseline:** `/Physics by Substratum/S2 SBI.tex`, SHA-256 `cb4c4dc588b852a5689d55b86d3146ad16b69e72b3da050913860ad6f72cd244`

## 1. Purpose and scope

This document is the short, human-readable entry point to the Lean formalization of Supplementary Discussion S2. It follows the conceptual argument in the same order as the manuscript and identifies the principal Lean declaration that certifies each major step. It deliberately omits most implementation details.

The formal development separates three different questions that should not be conflated:

1. **Physical justification:** whether A1--A3 are acceptable physical principles.
2. **Semantic fidelity:** whether the mathematical and Lean objects faithfully represent the intended physical concepts.
3. **Deductive correctness:** whether the stated conclusions follow from the encoded assumptions and definitions.

Lean directly checks the third question. The manuscript, code comments, traceability matrix, and dependency audit provide the evidence for the second. The first remains a scientific question addressed by the physical argument itself.

A second distinction is equally important. The formalization contains only three physical axioms, A1--A3, but it also contains explicit **semantic encodings** of phrases such as “an accessible distinction is operationally established” or “a realization of a relational connection forms a mediation chain.” These are not additional physical laws. They state formally what particular operational language in S2 means. Keeping them explicit prevents semantic assumptions from being hidden inside later proofs.

## 2. The proof in one view

The main logical path is:

```text
A1  Relational closure
A2  Local mediation + finite operational resolution
A3  Persistence
 |
 v
Observer-accessible substratum
    Theorem 1: one observer-accessible relational organization
 |
 +-----------------------------+
 |                             |
 v                             v
Operational accessibility     A2 finite local resolution
 |                             |
 +-------------+---------------+
               v
      Proposition 2: FOA
               |
               v
Operationally resolved relational connection
               |
               v
Lemma 2: finite observer-local mediation
               |
               v
Theorem 3: relational network representation
               |
               v
Proposition 4: operational local finiteness
               |
      +--------+---------+
      |                  |
      v                  v
Persistent identity      finite local alternatives
and finite support       for local realization
      |                  |
      +--------+---------+
               v
Local persistence requirements
               |
               v
Structural frustration
               |
               v
Lemma 8: reorganization is required
               |
               v
A2: realized reorganization is locally mediated
               |
               v
Theorem 5: continual reorganization under recurrent frustration
               |
               v
Admissible / persistence-preserving deformation
               |
               v
Theorem 6: realization independence
               |
               v
Theorem 7: persistent relational defects
```

The arrows show the conceptual proof path, not every internal Lean dependency. The detailed traceability matrix and generated dependency reports provide that lower-level information.

## 3. Starting point: A1--A3

The formal theory begins with three physical inputs in `Axioms.lean`.

**A1 -- Relational closure** says that physically meaningful descriptions are invariant under relational equivalence and that physically meaningful relations possess relational support. The Lean package is `RelationalClosureAxiom`, exposed downstream through `SBI.A1_invariance` and `SBI.A1_relational_support`.

**A2 -- Local mediation at fixed operational resolution** says two things needed later. First, direct mediation between elementary interactions proceeds through shared operationally distinguished relational participation. Second, one elementary interaction resolves only finitely many participations and alternatives at the operational resolution under consideration. This finiteness is deliberately not imposed on the unrestricted substratum. The Lean package is `LocalMediationAxiom`; the main public interfaces are `SBI.A2_local_mediation`, `SBI.sigmaOp_finite`, and `SBI.alternative_finite`.

**A3 -- Persistence** introduces persistent identity, its equivalence structure, and the existence of at least one persistent identity with relationally inequivalent realizations. The Lean package is `PersistenceAxiom`, with `SBI.Persist` and `SBI.A3_nontrivial` as principal interfaces.

These are the only physical axioms in the formalization.

## 4. From relational closure to one observer-accessible substratum

S2 first defines relational connectivity operationally: two relational domains are connected when relational organization involving both has a relational witness. In Lean this is `RelConnected` in `Substratum.lean`.

For an embedded observer, co-accessibility of two domains is itself treated as a physically meaningful relational statement. A1 then supplies relational support. The Lean theorem

`one_substratum`

therefore proves that any two domains accessible to the same embedded observer are relationally connected.

The observer-accessible substratum `S_O` is then defined extensionally as exactly the family of domains accessible to the observer. The manuscript's **Theorem 1 -- Substratum Theorem** is represented by

`substratum_theorem`.

It establishes two points simultaneously: membership in `S_O` is equivalent to accessibility by the observer, and every pair of domains in `S_O` is relationally connected. No A2, A3, FOA, network structure, geometry, or dynamics is needed for this step.

The result is intentionally observer-accessible rather than globally ontological. Structures inaccessible to the observer are not ruled out; they simply do not belong to that observer's accessible substratum.

## 5. Finite operational accessibility and local mediation

The next step introduces operational establishment. In S2, an accessible distinction is one that can actually be established by a completed operational realization. Lean represents this by `NetworkContext.AccessibleDistinction`, `NetworkContext.Establishes`, and the semantic clause `accessible_has_establishment` in `NetworkCore.lean`.

This clause is not a fourth physical axiom. It specifies what is meant by an *established observer-accessible distinction*. A finite Lean `List` represents the completed operational witness.

Combining that operational meaning with A2 gives **Proposition 2 -- Finite Operational Accessibility (FOA)**:

`finite_operational_accessibility : FOA C`.

FOA therefore has two sources only: finite operational establishment of an accessible distinction, and finite operational resolution supplied by A2 for each elementary interaction in that witness. It does not assert microscopic discreteness or global finiteness.

A further semantic bridge states what it means for an accessible distinction specifically to establish a relational connection. Its operational witness must form a mediation chain, and the shared mediation links must themselves be observer-accessible. These conditions are represented by `OperationalConnectionSemantics` and related structures in `NetworkOperational.lean`.

With the Substratum Theorem, FOA, the operational connection semantics, and A2 in place, **Lemma 2 -- Finite local mediation** is certified by

`finite_observer_local_mediation`.

The conclusion is that an observer-accessible relational connection has a finite operational realization whose successive interactions are locally linked through shared operationally distinguished relational participation.

## 6. From local mediation to a network representation

The manuscript next introduces three representational definitions: direct relations, local relational conjunctions, and an incidence network. They are represented in `NetworkObjects.lean` by `DirectRelation`, `LocalRelationalConjunction`, and `ObserverNetwork`.

The crucial point is that this is an **incidence representation**, not an assumed geometry. No metric, embedding, fixed valence, or pairwise fundamental interaction is inserted at this stage.

The resulting **Theorem 3 -- Relational Network Representation Theorem** is certified by

`network_representation_theorem`.

It shows that the observer-accessible relational organization admits the network representation used in the rest of S2 and that observer-accessible connections have finite network realizations. The network is thus obtained from the previously established operational-relational structure rather than postulated as a background lattice.

## 7. Operational local finiteness

Once the relational network is available, S2 introduces local configurations. For a local conjunction `v`, the incident relational set is `I(v)`, the operational local configuration space is `C(I(v))`, and the admissible subset is `A(I(v))`. Lean packages these notions in `OperationalContext` in `Operational.lean`.

Two independent finiteness results are then established for conjunctions that actually occur in a finite operational witness:

- `operationalConjunction_incidentSet_is_finite` proves that `I(v)` is finite;
- `operationalConjunction_localConfigurationSpace_is_finite` proves that `C(I(v))` is finite.

The latter uses the explicit semantic statement `LocalConfigurationsRepresentedByAlternatives`: the operational alternatives distinguished by a realizing interaction map surjectively onto the local configuration space. A2 makes the operational alternative set finite, so the represented local configuration space is finite as well.

These results are combined in **Proposition 4 -- Operational local finiteness**:

`operational_domain_is_locallyFinite`.

Again, the statement is local and operational. It does not claim that the substratum is globally finite, discrete, or geometrically lattice-like.

## 8. Persistence becomes a local structural constraint

A3 provides persistent identity, but S2 now asks how such identity is represented operationally. `PersistentStructuresPresent` records which persistence classes occur in a configuration, while `OperationallyReidentified` formalizes the operational re-identification of the same persistent identity in different realizations.

Because the re-identification distinction is observer-accessible, FOA supplies it with finite operational support. **Lemma 5 -- Finite operational support** is represented by

`operationallyReidentified_has_finiteNetworkSupport`.

Thus persistent identity, when operationally re-identifiable, is supported by finite relational structure at the operational resolution of the formalization.

The next key object is the persistence-preserving local set

`U_P(v;Y)`,

represented by `PersistencePreservingLocal`. It collects admissible local configurations at `v` that preserve operational re-identification of persistent identity `P` in relational context `Y`.

A **relational adaptation** is then a change between two such persistence-preserving local realizations, represented by `RelationalAdaptation`. No temporal ordering is introduced. If adaptation at one conjunction operationally induces adaptation at another, **Lemma 6** is certified by `localPropagation_of_relationalAdaptation`: the induced relation is finitely and locally mediated. Lean in fact proves a slightly stronger intermediate result than the manuscript requires, because nonincidence is unnecessary for the finite-mediation conclusion itself.

## 9. Structural frustration forces reorganization

A local persistence requirement specifies a persistent identity together with the context in which it must remain re-identifiable. A finite family of such requirements is **structurally frustrated** when no admissible local configuration satisfies them all. In Lean these notions are `LocalPersistenceRequirement` and `FiniteLocalStructuralFrustration` in `Frustration.lean`.

S2 does **not** assume that every finite family is frustrated, nor does it assume a universal compatibility principle. Frustration is a conditional structural circumstance.

The complete requirement family at a conjunction need not itself be finite. However, operational local finiteness is enough to show that full local incompatibility has a finite witness. **Lemma 7 -- Finite realization of local incompatibility** is certified by

`fullIncompatibility_has_finiteWitness`.

The manuscript derives finite admissible capacity from the finite local configuration space and `A(I(v)) ⊆ C(I(v))`. Lean proves the same conclusion using an exhaustive finite representation of the entire local configuration space, which is a slightly stronger available finiteness fact and introduces no additional physical assumption.

A local persistence situation consists of an admissible local configuration together with the finite requirements under consideration. If the initial family is frustrated, a later situation that preserves the relevant persistence requirements cannot remain structurally identical. **Lemma 8 -- Frustration requires relational reorganization** is represented by

`frustration_requires_reorganization`.

An operational realization of such a reorganization is then required, by definition of realization, to proceed through a finite mediation sequence. A2 converts that mediation sequence into shared operational relational participation. **Lemma 9 -- Local mediation of realized reorganization** is represented by

`reorganizationRealization_is_locallyMediated`.

Finally, S2 considers recurrent structural frustration. The natural-number index labels repeated episodes; it is not a physical time coordinate. **Theorem 5 -- Continual Reorganization Theorem** is certified by

`recurrentFrustration_requires_continualReorganization`.

The checked implication is that recurrent frustrated persistence situations require recurrent relational reorganization, and operational realizations of those reorganizations are locally mediated. The Lean implementation packages an already-realized reorganization in the recurrent-episode structure, but the core implication from frustration plus continued persistence to required reorganization is separately proved by `frustration_persistence_requires_localReorganization`.

## 10. Deformation and realization-independent structure

The final part of S2 moves from repeated reorganization to the structural meaning of persistence.

An **admissible deformation** is a finite reflexive-transitive chain of admissible configuration changes. In Lean it is `AdmissibleDeformation` in `Deformation.lean`. The zero-step case is included, and no duration or physical time parameter is introduced.

A `PersistencePreservingDeformation` is explicitly a refinement of an admissible deformation: the same persistent identity is operationally re-identified across every successive step. This distinction is important because persistence-preserving reachability is not introduced as an unrelated second dynamics.

S2 defines a property as essential to operational re-identification when re-identification of the same persistent identity requires equality of that property. Lean represents this by `EssentialToReidentification`.

From these definitions, **Theorem 6 -- Realization Independence Theorem** is certified by

`realization_independence`.

The proof is structurally simple: essentiality gives equality of the property across every persistence-preserving step, and equality composes across the finite deformation. Therefore an essential identifying property is invariant under persistence-preserving admissible deformation.

S2 then distinguishes a **context-preserving local deformation** from a persistence-preserving deformation. The former is confined to a relational domain and leaves the relevant surrounding relational context unchanged; it need not preserve the persistent identity. This is represented by `ContextPreservingLocalDeformation`.

A property-value is **locally non-eliminable** when every such context-preserving local deformation retains it. Together with operational re-identifiability and essentiality, this defines a `PersistentRelationalDefect`.

The final **Theorem 7 -- Structural characterization of persistent relational defects** is certified by

`persistentRelationalDefect_characterization`

in `Defects.lean`. It gives the same three conclusions as S2:

1. the defect has finite operational/network support;
2. its identifying property is invariant under persistence-preserving admissible deformation;
3. its identifying property-value cannot be eliminated by context-preserving local deformation.

No topological structure is assumed in this theorem. Conventional topological defects are therefore possible realizations of the more general deformation obstruction, not premises of the derivation.

## 11. What is machine checked

The Lean source is built as a complete project rather than as isolated code fragments. GitHub Actions checks out the repository on a fresh Linux runner and runs the Lean build workflow. The source baseline used for the formal audit has compiled successfully in this independent CI environment, and the workflow is run again on subsequent repository pushes.

The detailed traceability audit currently accounts for every substantive numbered S2 statement: 25 definitions, 9 lemmas, 2 propositions, 5 theorems, and 3 remarks. The reverse audit also checks the retained Lean logical spine for semantic or physical assumptions without a conceptual source in S2/S1. No additional physical axiom beyond A1--A3 has been identified.

This does **not** mean that Lean proves the physical framework true. The machine-checked claim is narrower and more precise: given the formalized physical inputs, definitions, and explicitly documented semantic encodings, the encoded conclusions follow without an unverified deductive step.

## 12. Documentation layers

Readers can inspect the formalization at three levels, depending on how much detail they need:

1. **This proof path** -- the conceptual argument and its principal Lean certificates.
2. **`SBI_Formal_Verification_Traceability_Matrix.md`** -- statement-by-statement manuscript/Lean correspondence, verification method, fidelity notes, and completeness audit.
3. **Generated dependency reports and Lean source** -- declaration-level checked dependencies, grouped proof structure, and the complete kernel-checked formal development.

The intended reading order is therefore from physical argument, to formal traceability, to implementation detail -- not the reverse.
