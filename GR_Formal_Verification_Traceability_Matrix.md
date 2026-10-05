# GR Formal Verification Traceability Matrix

**Project:** *The Structure of Spacetime — An Axiomatic Approach*  
**Formalization repository:** `OA-physics/SBILeanProject`  
**Lean-source baseline reviewed:** commit `9bbabb999a5c1cb2680b199a7337980b0eb488a8` (`Color refined GR grouped proof map`)  
**Authoritative conceptual source reviewed:** current project source `main GR(1).tex`  
**Authoritative conceptual source SHA-256:** `05c2f725d36f6ff0a5e5e576dfdc5b403c8d9128f10d7785fc6f241b65740670`  
**Imported formal foundations:** `SBILeanProject/SBI/` and `SBILeanProject/Time/`, documented by `SBI_Formal_Verification_Traceability_Matrix.md` and `Time_Formal_Verification_Traceability_Matrix.md`  
**Status:** Initial complete main-text-to-Lean verification/traceability baseline for the GR formalization. The formalized deductive core and the manuscript-facing proof architecture are aligned at this baseline. Section 4 contains additional physical interpretations and domain-of-applicability claims that are deliberately recorded as scope items rather than silently promoted to Lean theorems.

## 1. Purpose

This matrix provides bidirectional traceability between the principal conceptual statements in the GR manuscript and their manuscript-facing Lean interfaces.

Each row separates four questions:

1. **Identification:** Is the manuscript claim uniquely identified and sourced?
2. **Formal representation:** Is there a specific Lean declaration whose statement or type represents the claim?
3. **Semantic fidelity:** Does the Lean declaration express the same claim, or is the relation conditional on an explicit physical/effective bridge, representational choice, or imported theorem?
4. **Formal verification:** Does the claimed deductive consequence follow in Lean from the stated formal inputs, with the checked project building successfully?

Lean certifies deductive correctness of encoded statements. It does not establish the physical truth of the SBI axioms, the physical adequacy of a coarse-grained bridge, the applicability of the Lorentz or Lovelock classification hypotheses to nature, or the physical interpretation of a limiting reachability configuration as a gravitational horizon. Those logical-status distinctions are therefore retained explicitly.

## 2. NASA-style tailoring

This matrix follows the tailored Requirements Verification Matrix method used for the SBI and Time formalizations. The NASA-style functions retained here are: unique identifiers, definitive source statements, explicit success criteria, stated verification methods, bidirectional traceability, and recorded verification evidence/results.

Hardware-specific fields are replaced by scientific-formalization fields: Lean interface, source file, direct conceptual inputs, semantic-fidelity criterion, verification method, and evidence/result.

### Verification-method codes

- **I — Inspection:** direct comparison of manuscript wording with the Lean declaration, comments, and type.
- **A — Analysis:** examination of the Lean proof, dependency structure, logical reduction, or machine-generated dependency graph.
- **T — Test:** successful clean `lake build` / elaboration of the checked Lean project.
- **D — Demonstration:** reserved for executable demonstrations if introduced later.

Most theorem rows use **I+A+T**. Pure definitions and explicit semantic contracts normally use **I+T**.

### Result/status codes

- **PASS** — manuscript claim and manuscript-facing Lean interface agree at the level relevant to the derivation.
- **PASS+** — Lean establishes the manuscript claim and additionally proves a stronger or more explicit result; the strengthening is documented.
- **ENCODING** — explicit semantic/representational contract or physical bridge; deductive use is checked, while physical adequacy remains a scientific judgment.
- **EXTERNAL** — established mathematics is represented by an explicit imported theorem interface; Lean checks its use but does not re-prove the external theorem.
- **SCOPE** — manuscript interpretation or physical consequence deliberately outside the present Lean theorem layer.
- **EXPLANATORY** — scope clarification for which no dedicated theorem is required.
- **UPDATE** — Lean is internally coherent but manuscript wording or dependency statements require alignment.

## 3. Traceability and verification matrix

The manuscript currently formalizes the principal deductive chain directly from the main text rather than through a separate numbered formal supplement. Trace IDs therefore use manuscript-section prefixes rather than attempting to reproduce independent theorem counters.

| Trace ID | Class | Conceptual source / statement | Manuscript-facing Lean interface / formal statement | Lean source | Direct conceptual inputs | Success criterion | Method | Result / evidence and fidelity note |
|---|---|---|---|---|---|---|---|---|
| GR-IMP01 | Imported verified foundation | Relational closure, local mediation, persistence, observer-accessible relational structure, local configurations, persistence requirements, frustration, and relational reorganization are imported from the SBI companion development. | Imported `SBILeanProject.SBI.*` declarations; principal GR uses include `A1_invariance`, `A1_relational_support`, persistence and frustration interfaces. | `SBI/` via GR imports | Verified SBI formalization. | GR reuses the checked SBI structures rather than silently re-postulating a second relational foundation. | I+A+T | **PASS.** The generated upstream-boundary/dependency reports expose the imported interface. |
| GR-IMP02 | Imported verified foundation | Reversible paths, path length, positive local duration calibration, and accumulated reversible duration are imported from the Time companion development. | `Time.ReversibleRearrangementPath`, `Time.LocalDurationScale`, accumulated-duration results. | `Time/Duration.lean` and dependencies | Verified Time formalization. | Positive duration enters GR only through the explicit Time duration construction; A2 alone is not treated as a duration theorem. | I+A+T | **PASS.** `CausalPropagation.lean` documents and enforces this boundary explicitly. |
| GR2-SEM01 | Physical/effective bridge | A causal propagation process of relational depth `n` is represented by a reversible duration-bearing path containing at least `n` resolved local advances. | `CausalPropagationProcess`, especially field `depth_le_pathLength`. | `GR/CausalPropagation.lean` | GR-IMP02 plus GR causal interpretation. | The bridge is explicit and introduces no spatial metric, coordinate speed, or Lorentz transformation. | I+T | **ENCODING / PASS.** This is the causal-depth-to-duration representation assumption, not a theorem of A2 alone. |
| GR2-P01 | Proposition / derived result | **Finite causal propagation rate.** In the homogeneous represented regime, causal propagation has a finite bound in relational depth per operational duration. | `CausalPropagationProcess.accumulatedDuration_pos_of_depth_pos`; `depth_times_stepDuration_le_duration`; `HasFiniteRelationalDepthRateBound`; `hasFiniteRelationalDepthRateBound`. | `GR/CausalPropagation.lean` | GR2-SEM01; positive `LocalDurationScale` from Time. | Lean proves `n*delta_tau_loc <= Delta_tau` and hence the finite depth-rate bound without introducing an effective spatial length. | I+A+T | **PASS.** The manuscript conversion to `c_adm = ell_loc/delta_tau_loc` is a later coarse-grained representation step and is not falsely encoded here. |
| GR2-SEM02 | Semantic interface | A physically meaningful change in propagation character is represented abstractly before coordinates or velocity are introduced. | `PropagationChangeSemantics`. | `GR/InertialPersistence.lean` | SBI A1 physical-meaningfulness interface. | Propagation change remains pre-geometric; no velocity, derivative, force, or metric is smuggled into the definition. | I+T | **ENCODING / PASS.** |
| GR2-L01 | Lemma / derived result | **Persistence of unconstrained propagation.** A persistent structure cannot acquire a physically meaningful change in propagation character without relational support; this supplies the structural content of Newton I. | `propagationChange_requires_relationalSupport`; `noRelationalSupport_noPropagationChange`; `UnconstrainedPersistentContinuation`; `NewtonFirstLawStructural`; `unconstrainedPersistentContinuation_implies_NewtonFirstLawStructural`. | `GR/InertialPersistence.lean` | SBI A1 relational support; A3 persistence relation; GR2-SEM02. | Lean derives unchanged propagation character under the stated no-support condition; coordinate equation `dv/dtau=0` is not claimed as a primitive theorem. | I+A+T | **PASS.** A2 is correctly absent from the negative no-support implication itself. |
| GR2-SEM03 | Physical/effective bridge | Operationally equivalent inertial descriptions correspond to relationally equivalent descriptions for the inertial regime under consideration. | `InertialEquivalenceSemantics`, field `relEq_of_equivalent`. | `GR/InertialSymmetry.lean` | SBI A1 relational equivalence/invariance. | The operational inertial criterion is explicit and is not generalized to arbitrary physical states. | I+T | **ENCODING / PASS.** Homogeneity/isotropy remain regime conditions, not consequences of A1. |
| GR2-L02 | Lemma / derived result | **No operationally accessible absolute inertial state.** No physically meaningful descriptor distinguishes operationally equivalent inertial realizations. | `inertialEquivalent_descriptors_agree`; `NoAbsoluteInertialMarker`; `inertialEquivalence_excludes_absoluteMarker`. | `GR/InertialSymmetry.lean` | GR2-SEM03; SBI `A1_invariance`. | Lean quantifies over physically meaningful descriptors and proves equality on operationally equivalent inertial realizations. | I+A+T | **PASS.** |
| GR2-SEM04 | Semantic interface | Causal accessibility is physically meaningful and inertial redescription maps each state to an operationally equivalent realization. | `CausalAccessibilitySemantics`; `OperationalInertialRedescription`; `OperationalInertialRedescription.toInertialRedescription`; `PreservesCausalStructure`. | `GR/InertialSymmetry.lean` | GR2-SEM03; SBI A1. | Causal invariance is derived through the same operational inertial-equivalence relation used in the no-absolute-state result. | I+T | **ENCODING / PASS.** |
| GR2-L03 | Lemma / derived result | **Invariance of the causal boundary / causal accessibility.** Equivalent inertial redescriptions preserve the causal-accessibility relation. | `causalAccessibility_eq_of_relEq`; `operationalInertialRedescription_preservesCausalStructure`; `PreLorentzInertialSymmetry`; `operationalInertialRedescription_has_preLorentzSymmetry`. | `GR/InertialSymmetry.lean` | GR2-SEM03; GR2-SEM04; SBI A1. | Lean proves full two-endpoint causal-relation invariance under the operational inertial redescription. | I+A+T | **PASS.** The numerical invariant speed identification remains a coarse-grained manuscript step. |
| GR2-EXT01 | External mathematics | Standard homogeneous/isotropic inertial-kinematics classification: homogeneity + isotropy + relativity + finite invariant causal speed imply the Lorentz branch for admissible inertial transformations. | `StandardLorentzClassification`; `LorentzClassificationInput`; field `classify`. | `GR/LorentzClassification.lean` | Established inertial-kinematics classification. | External theorem and its hypotheses are visible as a separate interface rather than encoded as consequences of A1–A3. | I+T | **EXTERNAL / PASS.** Lean checks use of the imported theorem but does not re-prove the classification. |
| GR2-T01 | Theorem / imported-classification application | **Lorentz symmetry of admissible inertial transformations.** Once the standard classification hypotheses are supplied, admissible transformations are Lorentz. | `lorentz_of_standardClassification`. | `GR/LorentzClassification.lean` | GR2-EXT01; `LorentzClassificationInput`; admissible transformation. | Lean passes all four classification hypotheses explicitly to the imported theorem interface. | I+A+T | **PASS with EXTERNAL premise.** |
| GR2-B01 | Manuscript-facing bundle | Section-2 spacetime kinematics consists jointly of structural Newton I, no absolute inertial marker, finite causal-rate bound, pre-Lorentz causal symmetry, and Lorentz classification. | `SpacetimeKinematicsResult`; `spacetimeKinematics_characterization`. | `GR/KinematicsSynthesis.lean` | GR2-L01; GR2-P01; GR2-L02; GR2-L03; GR2-T01. | Bundle contains no new physical premise and simply collects already established results. | I+A+T | **PASS.** Structural Newton I is a Section-2 conclusion but is not treated downstream as a premise of the manifold construction. |
| GR3-SEM01 | Coarse-graining / representation bridge | In a regime with smoothly varying, compatible overlapping local descriptions, the relational organization admits an effective differentiable-manifold representation. Smooth coordinate redundancy corresponds to relational equivalence. | `EffectiveGeometricRepresentation`, including `HasEffectiveDifferentiableManifold`, `hasEffectiveDifferentiableManifold`, `SmoothlyEquivalent`, and `smoothlyEquivalent_relEq`. | `GR/GeometricRepresentation.lean` | Coarse-grained smooth-regime condition; SBI relational equivalence. | Smooth manifold representability is supplied explicitly as a regime condition and is not claimed as a theorem of A1–A3 alone. | I+T | **ENCODING / PASS.** |
| GR3-SEM02 | Physical/effective bridge | A Lorentz result in the selected inertial regime, together with smooth manifold representability, is identified with Lorentzian causal structure of the effective manifold. | `LorentzianGeometryBridge`. | `GR/GeometricRepresentation.lean` | GR2-T01; GR3-SEM01. | The bridge consumes only the Lorentz result actually needed for the geometric step and not unrelated Section-2 conclusions. | I+T | **ENCODING / PASS.** Newton I is correctly a parallel kinematical result, not a premise here. |
| GR3-L01 | Lemma / derived result | **Effective Lorentzian neighborhood structure.** The selected smooth effective representation has Lorentzian causal structure. | `lorentzianCausalStructure_of_lorentzResult`; `lorentzianCausalStructure_of_standardClassification`; `effectiveGeometry_bridge_and_coordinateInvariance`. | `GR/GeometricRepresentation.lean` | GR3-SEM01; GR3-SEM02; GR2-EXT01/GR2-T01. | Lean derives `HasLorentzianCausalStructure` only after the explicit bridge and manifold condition are supplied. | I+A+T | **PASS.** Causal structure fixes Lorentzian causal/conformal character; no metric scale is derived here. |
| GR3-L02 | Lemma / derived result | **Coordinate equivalence from relational closure.** Smoothly equivalent descriptions of the same relational state cannot be distinguished by physically meaningful descriptors. | `coordinateEquivalent_descriptors_agree`; `EffectiveGeometricRepresentation.CoordinateInvariant`; `physicallyMeaningful_descriptor_is_coordinateInvariant`. | `GR/GeometricRepresentation.lean` | GR3-SEM01; SBI `A1_invariance`. | Lean proves coordinate invariance only after smooth-coordinate equivalence is bridged to relational equivalence. | I+A+T | **PASS.** This is the abstract formal counterpart of the manuscript covariance argument. |
| GR3-SEM03 | Physical/mathematical bridge | Irreducibly higher-than-second-order metric dynamics require independent continuation data beyond metric data and their first directed-time rate. | `MetricClosureSemantics`, field `higherOrder_requires_independent`. | `GR/MetricClosure.lean` | Effective initial-data interpretation. | Higher-order-to-independent-data implication is explicit and not attributed to A1–A3 by Lean. | I+T | **ENCODING / PASS.** |
| GR3-D01 | Definition | **Closed local effective state.** Metric data and first rate contain all local continuation information, represented as uniqueness of admissible continuation data for a fixed state. | `ClosedLocalMetricState`; supporting `HasIndependentContinuationData`. | `GR/MetricClosure.lean` | GR3-SEM03. | Closure is an at-most-one continuation-data condition and does not assert existence for every state. | I+T | **PASS.** |
| GR3-L03 | Lemma / derived result | **Second-order closure of metric dynamics.** A closed metric-only state excludes irreducibly higher-order dynamics in the stated sense. | `closedLocalMetricState_no_independentContinuation`; `closedMetricState_excludes_irreducibleHigherOrder`; `irreducibleHigherOrder_not_metricOnlyClosed`. | `GR/MetricClosure.lean` | GR3-SEM03; GR3-D01. | Lean proves the incompatibility without invoking Ostrogradsky instability or excluding higher derivatives caused by eliminating additional state variables. | I+A+T | **PASS.** The manuscript qualification about reducible higher derivatives is preserved. |
| GR3-SEM04 | Coarse-graining bridge | Changes of a coarse-grained quantity satisfy a local balance relation: change = boundary transport + local source. | `CoarseGrainedLocalBalance`, field `balance`. | `GR/LocalConservation.lean` | Local mediation/persistence motivation plus continuum coarse graining. | Continuum balance is explicit and not silently presented as a theorem directly derived from A2/A3. | I+T | **ENCODING / PASS.** |
| GR3-SEM05 | Physical/effective bridge | A quantity preserved by underlying admissible rearrangements has zero coarse-grained local source. | `PreservedQuantityBridge`, field `preserved_source_free`. | `GR/LocalConservation.lean` | GR3-SEM04; microscopic preservation interpretation. | Preservation-to-source-free identification is separate from the algebraic balance theorem. | I+T | **ENCODING / PASS.** |
| GR3-L04 | Lemma / derived result | **Local conservation structure.** Source-free local balance implies local conservation; preserved quantities are locally conserved. | `sourceFreeQuantity_is_locallyConserved`; `preservedQuantity_is_locallyConserved`; `HasLocalConservationStructure`; `localBalance_has_conservationStructure`. | `GR/LocalConservation.lean` | GR3-SEM04; GR3-SEM05. | Lean derives the source-free balance consequence exactly. | I+A+T | **PASS.** The covariant tensor equation is not claimed at this layer. |
| GR3-SEM06 | Effective-field representation bridge | A selected conserved coarse-grained quantity is represented by a tensorial, symmetric source tensor, and integral local conservation maps to covariant conservation. | `EffectiveSourceTensorBridge`. | `GR/StressEnergyBridge.lean` | GR3-L04; continuum tensor representation. | Tensoriality, symmetry, and local-to-covariant conservation are explicit bridge fields rather than consequences of the scalar/integral balance law. | I+T | **ENCODING / PASS.** |
| GR3-L05 | Derived effective-source result | A preserved quantity has a tensorial, symmetric, covariantly conserved effective source representation. | `preservedQuantity_has_effectiveConservedSource`; `HasAdmissibleEffectiveSource`; `preservedQuantity_has_admissibleEffectiveSource`. | `GR/StressEnergyBridge.lean` | GR3-SEM05; GR3-L04; GR3-SEM06. | Lean combines the derived local conservation result with the explicit tensor representation bridge. | I+A+T | **PASS.** Identification with physical `T_{mu nu}` remains an effective representation choice. |
| GR3-SEM07 | Physical/effective bridge | The selected effective GR regime possesses the structural premises later associated with Lovelock: four-dimensionality, local metric construction, covariance, symmetry, divergence freedom, and at-most-second-order dependence. | `EffectiveLovelockRegimeBridge`. | `GR/EinsteinSynthesis.lean` | GR3-SEM01; GR3-L01; GR3-L03 plus explicit regime inputs. | GR-side physical premises exist independently of the external Lovelock interface. | I+T | **ENCODING / PASS.** Four-dimensionality, local metric construction, geometric symmetry, and divergence freedom are not falsely derived from the external theorem. |
| GR3-R01 | Derived premise bundle | The effective Lorentzian geometry plus closed metric state establish the GR-side Lovelock premise bundle. | `EffectiveLovelockPremises`; `effectiveLovelockPremises_of_closedEffectiveRegime`. | `GR/EinsteinSynthesis.lean` | GR3-SEM07; GR3-L01; GR3-L03. | Lean derives the premise record before any external Lovelock theorem is applied. | I+A+T | **PASS.** This separation was introduced specifically to prevent circular-looking dependency structure. |
| GR3-EXT01 | External mathematics | Four-dimensional Lovelock classification of local symmetric divergence-free metric tensors through at most second derivatives. | `StandardLovelockClassification`, field `classify`; `LovelockClassificationInput`. | `GR/LovelockClassification.lean` | Established Lovelock theorem. | External theorem and all formal predicates are explicit. | I+T | **EXTERNAL / PASS.** Lean checks application but does not re-prove Lovelock. |
| GR3-SEM08 | Identification bridge | The GR-side structural predicates are identified with the corresponding predicates of one selected `StandardLovelockClassification`. | `LovelockRegimeBridge`; `lovelockInput_of_effectivePremises`. | `GR/EinsteinSynthesis.lean` | GR3-R01; GR3-EXT01. | Identification occurs after GR-side premises are established and before the external theorem is invoked. | I+A+T | **ENCODING / PASS.** This prevents the imported theorem from appearing to establish its own physical hypotheses. |
| GR3-R02 | External-classification result | The selected geometric tensor lies in the Einstein-plus-cosmological family. | `einsteinPlusCosmological_of_standardLovelock`. | `GR/LovelockClassification.lean` | GR3-EXT01; completed `LovelockClassificationInput`. | Lean passes the complete input bundle to the imported classification theorem. | I+A+T | **PASS with EXTERNAL premise.** |
| GR3-SEM09 | Effective coupling bridge | Classified Einstein-plus-cosmological geometry is coupled to an admissible effective source with coupling constant `kappa`. | `EffectiveEinsteinCoupling`. | `GR/EinsteinSynthesis.lean` | GR3-R02; GR3-L05. | Source coupling and `kappa` are explicit inputs, not outputs of Lovelock classification. | I+T | **ENCODING / PASS.** The numerical value `8 pi G/c^4` is outside the structural theorem. |
| GR3-T02 | Theorem / synthesis | **Admissible coarse-grained geometry.** Under the explicit effective-regime, Lovelock-identification, source, and coupling inputs, the local field equation has Einstein form. | `admissibleCoarseGrainedGeometry_has_EinsteinForm`. | `GR/EinsteinSynthesis.lean` | GR3-R01; GR3-SEM08; GR3-R02; GR3-L05; GR3-SEM09. | Lean follows the staged chain: effective premises -> Lovelock input -> imported classification -> source coupling. | I+A+T | **PASS.** No empirical value of `kappa` is derived. |
| GR3-B02 | Manuscript-facing bundle | The effective-GR characterization jointly returns Lorentzian causal structure, coordinate invariance, absence of irreducible higher-order metric dynamics, an admissible effective source, and the Einstein-form equation. | `effectiveGR_characterization`. | `GR/Conclusions.lean` | GR3-L01; GR3-L02; GR3-L03; GR3-L05; GR3-T02. | The bundle adds no new physical premise and preserves the staged dependency structure. | I+A+T | **PASS.** It intentionally does not consume structural Newton I as a premise of the geometric branch. |
| GR4-D01 | Definition / imported-structure repackaging | The local compatible-configuration family `C(Gamma)` consists of local configurations satisfying all persistence requirements; strengthening the family is semantic inclusion of requirements. | `CompatibleConfiguration`; `RequirementFamilyIncluded`. | `GR/ConstraintCapacity.lean` | SBI local persistence/frustration formalization. | Definitions reuse SBI semantics and do not introduce energy, geometry, gravity, or time. | I+T | **PASS.** |
| GR4-R01 | Derived structural result | Strengthening persistence requirements cannot increase reconfiguration capacity; strict reduction requires an actual exclusion; structural frustration exhausts the compatible family and continued persistence requires reorganization. | `NoGreaterReconfigurationCapacity`; `includedRequirements_noGreaterReconfigurationCapacity`; `StrictlyLowerReconfigurationCapacity`; `ReconfigurationCapacityExhausted`; `structuralFrustration_exhaustsReconfigurationCapacity`; `structuralFrustration_capacityExhausted_and_reorganizationRequired`. | `GR/ConstraintCapacity.lean` | GR4-D01; verified SBI frustration results. | Lean proves antitonicity and the stated frustration consequences without introducing a scalar capacity measure. | I+A+T | **PASS.** “Reconfiguration capacity” is an ordering/inclusion concept here, not a derived numerical field. |
| GR4-SEM01 | Physical bridge | Additional persistence constraints may remove admissible local transitions but cannot create transitions that were previously forbidden. | `ConstraintReachabilitySemantics`, field `step_antitone`. | `GR/ReachabilityBoundary.lean` | GR4-D01; physical monotonicity interpretation. | The transition-antitonicity assumption is explicit and distinct from compatible-configuration antitonicity. | I+T | **ENCODING / PASS.** This is the genuine GR dynamical bridge in the reachability branch. |
| GR4-R02 | Derived structural result | Constraint strengthening cannot enlarge finite reachability and cannot restore continuation once terminality is reached. | `ConstrainedReachability`; `constrainedReachability_of_includedRequirements`; `NoGreaterReachabilityDomain`; `includedRequirements_noGreaterReachabilityDomain`; `TerminalUnderConstraints`; `terminal_preserved_by_constraintStrengthening`; bundle `constraintStrengthening_characterization`. | `GR/ReachabilityBoundary.lean`; `GR/Conclusions.lean` | GR4-SEM01; GR4-D01. | Lean proves reachability antitonicity and preservation of terminality by induction/contradiction from `step_antitone`. | I+A+T | **PASS.** |
| GR4-D02 | Definition | A limiting reachability configuration remains compatible with the operative persistence requirements but has no admissible outgoing step. | `LimitingReachabilityConfiguration`. | `GR/ReachabilityBoundary.lean` | GR4-D01; GR4-SEM01. | Definition contains compatibility plus terminality only; it does not contain “horizon”, metric, black-hole, or temporal terminology. | I+T | **PASS.** |
| GR4-R03 | Derived structural result | A terminal/limiting configuration has no reachable distinct continuation. | `terminal_reachability_eq_self`; `terminal_no_distinct_reachable`; `limitingConfiguration_no_distinct_continuation`; bundle `limitingReachability_characterization`. | `GR/ReachabilityBoundary.lean`; `GR/Conclusions.lean` | GR4-D02; constrained finite reachability. | Lean proves that every reachable state from a terminal configuration is the same configuration. | I+A+T | **PASS.** This is the formal endpoint of the reachability branch. |
| GR4-S01 | Domain-of-validity interpretation | Smooth manifold applicability requires sufficiently rich overlapping coarse-grained reachability domains. Loss of the required overlap invalidates the selected atlas/manifold representation. | No dedicated theorem in the current GR Lean layer. The formal reachability results provide supporting structure only. | Manuscript Section 4; related GR reachability modules | GR4-R01; GR4-R02; GR3-SEM01. | The manuscript must present this as a physical/effective interpretation, not as a direct theorem already certified by Lean. | I | **SCOPE / EXPLANATORY.** Deliberately outside the current theorem layer. |
| GR4-S02 | Domain-of-validity interpretation using Time | Continued directed temporal succession requires accessible record-forming transitions; if none remain locally, the effective directed-time continuation does not extend there. | Record/precedence mechanisms are formalized upstream in `Time/`; the specific GR restriction-to-record-forming-family argument is not a dedicated GR theorem. | Manuscript Section 4; `Time/` foundation | Verified Time record/precedence results plus GR reachability interpretation. | No claim that reversible duration itself becomes negative or universally ceases. | I+A | **SCOPE / PASS.** Upstream temporal structure is formalized; the GR applicability interpretation remains prose-level. |
| GR4-S03 | Physical interpretation | A physically realized limiting reachability configuration may have the operational character of a horizon. | No theorem identifying `LimitingReachabilityConfiguration` with a GR/black-hole horizon. | Manuscript Section 4 | GR4-R03 plus physical identification. | Horizon terminology must remain interpretive and conditional. | I | **SCOPE.** The Lean code explicitly avoids making this identification. |
| GR4-S04 | Physical interpretation | An analytic GR continuation beyond a reachability horizon may extrapolate the effective metric beyond the substratum states for which the geometry was derived; the continued interior/singularity need not correspond to physical substratum states. | No dedicated theorem. | Manuscript Section 4 | GR4-S03; effective-theory interpretation. | The conclusion is stated as a framework-dependent interpretation, not as a theorem excluding mathematical GR extensions. | I | **SCOPE.** |
| GR4-S05 | Low-density applicability interpretation | In a sufficiently dilute regime, local reversible evolution may persist while connected record networks become too sparse to support one extended directed temporal order. | Underlying record/precedence distinction is formalized in `Time/`; cosmological fragmentation interpretation is not a GR Lean theorem. | Manuscript Section 4 | Verified Time temporal-order structure plus cosmological applicability interpretation. | No total temporal order is inferred without physical record connectivity. | I+A | **SCOPE / PASS.** |
| GR4-S06 | Explicit conjecture | Effective localized energy-momentum may correspond to suppression of reconfiguration capacity, potentially linking constraint loading to strong curvature. | No Lean theorem; intentionally absent from GR formalization. | Manuscript Section 4 | Future microscopic theory/model-selection layer. | Manuscript must state that the energy/reconfiguration correspondence has not been quantitatively derived and is not required for the reachability result. | I | **SCOPE / CONJECTURAL.** |
| GR4-S07 | Continuum-scope statement | The smooth description may also fail when relational variation approaches the intrinsic coarse-graining/resolution scale, independently of reachability saturation. | No dedicated theorem. | Manuscript Section 4 | GR3-SEM01 continuum-regime assumption. | This limitation is kept distinct from the constraint/reachability branch. | I | **SCOPE / EXPLANATORY.** |
| GR-CQG01 | Consequence / outlook | If the metric is an emergent effective variable, quantizing the metric variables need not by itself identify the microscopic degrees of freedom from which they emerge. | No Lean theorem required. | Conclusions | GR3 effective-geometry architecture; GR4 domain-of-applicability discussion. | Statement remains conditional and does not claim that quantized effective geometry is useless or inconsistent. | I | **SCOPE / EXPLANATORY.** |

## 4. Forward traceability audit: manuscript -> Lean

The formalized core of Sections 2 and 3 has a manuscript-facing Lean counterpart for every principal deductive step:

- causal depth is connected to positive reversible duration only through the explicit `CausalPropagationProcess` bridge;
- structural Newton I is proved pre-geometrically from persistence plus absence of relational support for change;
- operational inertial equivalence is bridged to A1 relational equivalence before no-absolute-marker and causal-invariance results are obtained;
- the Lorentz classification is visibly imported as external mathematics;
- smooth manifold representability and the Lorentz-to-Lorentzian passage are explicit coarse-graining/representation bridges;
- coordinate invariance is derived from A1 only after smooth coordinate redundancy is identified with relational equivalence;
- second-order closure depends on the explicit higher-order/continuation-data bridge;
- continuum balance, preservation-to-source-free conversion, and tensorial stress-energy representation are distinct interfaces;
- GR-side Lovelock premises are established before they are identified with the external Lovelock predicates;
- the imported Lovelock theorem classifies the geometric side only;
- source coupling and the numerical coupling parameter are separate from the Lovelock theorem; and
- the final GR bundle contains only results reachable through this staged dependency chain.

The formalized part of Section 4 ends at constraint-strengthened/limiting reachability. Horizon language, black-hole continuation, dilute-limit cosmology, energy/reconfiguration identification, and continuum-resolution breakdown remain explicitly outside the current GR theorem layer.

## 5. Reverse traceability audit: Lean -> manuscript

The refined grouped GR report contains 19 conceptual groups. Every group has a conceptual home in this matrix:

1. persistence constraints and reconfiguration capacity -> GR4-D01 / GR4-R01;
2. constraint-dependent reachability -> GR4-SEM01 / GR4-R02 / GR4-D02 / GR4-R03;
3. constraint-strengthened and limiting reachability -> GR4-R02 / GR4-R03;
4. persistent inertial propagation (Newton I) -> GR2-SEM02 / GR2-L01;
5. finite causal propagation from Time duration -> GR-IMP02 / GR2-SEM01 / GR2-P01;
6. operational inertial equivalence and causal symmetry -> GR2-SEM03 / GR2-L02 / GR2-SEM04 / GR2-L03;
7. imported Lorentz classification -> GR2-EXT01 / GR2-T01;
8. spacetime kinematics -> GR2-B01;
9. smooth effective manifold and coordinate invariance -> GR3-SEM01 / GR3-L02;
10. Lorentz result to Lorentzian effective geometry -> GR3-SEM02 / GR3-L01;
11. closed metric state and second-order closure -> GR3-SEM03 / GR3-D01 / GR3-L03;
12. coarse-grained local conservation -> GR3-SEM04 / GR3-SEM05 / GR3-L04;
13. effective conserved source tensor -> GR3-SEM06 / GR3-L05;
14. GR structural premises for Lovelock -> GR3-SEM07 / GR3-R01;
15. imported Lovelock theorem interface -> GR3-EXT01;
16. identification with Lovelock hypotheses -> GR3-SEM08;
17. Lovelock geometric classification result -> GR3-R02;
18. Einstein-form geometry/source coupling -> GR3-SEM09 / GR3-T02;
19. effective GR characterization -> GR3-B02.

No conceptual group is left without a manuscript role, and the grouped report does not create edges by hand: group-to-group edges are generated from checked declaration dependencies.

The two principal graph components are intentionally retained. The effective-GR derivation is one conditional proof chain; the constraint/reachability branch proves monotonicity and terminality results that support the manuscript's separate domain-of-applicability interpretation. An artificial edge is not added merely to make the graph visually connected.

## 6. Logical-status audit

Several distinctions are especially important for interpreting verification claims:

- **Axiomatic/imported structure:** SBI and Time results are imported verified foundations, not re-proved in GR.
- **Physical/effective bridges:** causal depth-to-duration representation, operational inertial equivalence, smooth manifold representability, Lorentz-to-Lorentzian identification, continuum balance, source-tensor representation, GR-side Lovelock premises, predicate identification, and geometry/source coupling are explicit contracts.
- **External mathematics:** the Lorentz and Lovelock classification theorems are represented as imported theorem interfaces.
- **Derived Lean results:** once the relevant bridges and imported theorem interfaces are supplied, the stated logical consequences are machine checked.
- **Interpretation/outlook:** reachability-horizon identification, analytic-interior interpretation, cosmological dilution, energy/reconfiguration correspondence, continuum-resolution breakdown, and quantum-gravity implications are not promoted to formal theorems without additional structure.

This status separation is the central scientific-assurance purpose of the GR formalization. A clean Lean build verifies implications inside the encoded model; it does not erase the distinction between an axiom, a bridge assumption, an external theorem, a derived consequence, and a conjectural interpretation.

## 7. Alignment status against the current GR manuscript

At the baseline identified above, no open deductive mismatch was identified in the formalized core after the September 30 dependency-architecture audit. Three corrections are reflected in the present Lean baseline:

1. structural Newton I remains a Section-2 kinematical conclusion but is no longer treated as a premise of the Lorentzian-manifold construction;
2. GR-side Lovelock premises, their identification with the external theorem predicates, the imported classification, and the final source coupling are represented as distinct stages; and
3. the reachability theorem group is labelled only by what Lean proves (`Constraint-strengthened and limiting reachability`) rather than by the broader manuscript interpretation “domain of validity”.

The manuscript introduction and conclusion are under active editorial alignment with this stabilized architecture. A future release baseline should update the conceptual-source hash after those prose edits are frozen.

## 8. Verification evidence and configuration control

The Lean-source baseline identified above was reported by the author to build cleanly after the refined grouped-map changes. The following commands form the present verification sequence:

```text
lake build SBILeanProject.GR
lake build SBILeanProject.GR.DependencyReport
lake build SBILeanProject.GR.ColoredDependencyReport
```

The dependency-report layer generates the declaration-level forensic report, the manuscript-facing declaration map, the refined conceptual grouped map, and the imported SBI/Time boundary information used for audit.

For a submission/release baseline, freeze together under one Git tag and archival release:

1. the exact GR manuscript source identified by cryptographic hash;
2. this verification/traceability matrix;
3. `GR_Main_Lean_Traceability_v1.txt`;
4. the complete GR Lean source tree and imported SBI/Time baseline commits;
5. `lean-toolchain` and `lake-manifest.json`;
6. a clean build from that exact checkout;
7. the declaration-level dependency report;
8. the manuscript-facing declaration map;
9. the refined grouped map used for the manuscript figure; and
10. the upstream-boundary report identifying imported formal interfaces.

The release tag/commit SHA then becomes the configuration identifier for the verified GR baseline.

## 9. Interpretation of verification claims

A **PASS** result means that, for the reviewed source version, the identified Lean declaration is an adequate formal counterpart of the conceptual statement and the deductive claim is represented in the checked formal development.

Five distinct questions remain separate:

- **Imported physical foundation:** whether the SBI and Time assumptions/results are physically justified.
- **Effective-regime adequacy:** whether the considered physical regime satisfies the explicit coarse-graining and representation bridges.
- **External mathematics:** whether the standard Lorentz/Lovelock theorem interfaces faithfully represent the established classifications being invoked.
- **Semantic fidelity:** whether the Lean structures faithfully encode the intended relational, causal, geometric, and conservation meanings.
- **Deductive correctness:** whether the conclusions follow from the encoded inputs.

Lean directly certifies the fifth. Source comparison, comments, this matrix, and machine-generated dependency reports provide the audit evidence for the fourth and for correct use of the third. The first two remain scientific questions argued in the manuscripts and, ultimately, tested against physical applicability.