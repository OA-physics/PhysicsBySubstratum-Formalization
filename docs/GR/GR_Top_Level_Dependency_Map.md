# GR top-level dependency architecture

**Manuscript:** *The Structure of Spacetime — An Axiomatic Approach*  
**Purpose:** human-readable interpretation of the machine-generated grouped Lean dependency map and source documentation for the manuscript dependency figure  
**Formal entry point:** `SBILeanProject/GR.lean`

## 1. Authoritative graph source

The GR manuscript figure should use the grouped graph generated from the Lean
dependency structure. A second hand-maintained graph is intentionally avoided.

The relevant generators are:

- `SBILeanProject/GR/DependencyReport.lean` — forensic declaration-level audit
  and manuscript spine;
- `SBILeanProject/GR/RefinedGroupedReport.lean` — manuscript-facing conceptual
  groups with group-to-group edges generated from checked Lean dependencies;
- `SBILeanProject/GR/ColoredDependencyReport.lean` — presentation-only color
  styling of the refined GraphML output.

Reproduce the current checked map with:

```text
lake build SBILeanProject.GR
lake build SBILeanProject.GR.DependencyReport
lake build SBILeanProject.GR.ColoredDependencyReport
```

The principal human-facing artifact is:

`gr-grouped-map.graphml`

The declaration-level manuscript map remains useful for forensic inspection:

`gr-manuscript-map.graphml`

The grouped map is a compression of checked declaration dependencies. Human
judgment chooses which declarations belong to a conceptual manuscript stage;
it does not choose the edges between stages.

## 2. Visual conventions

### Fill color

- **Orange** — interfaces imported from the companion SBI/Time formal
  developments and repackaged for the GR argument.
- **Yellow** — definitions, effective-regime inputs, and explicit external
  theorem interfaces supplied to the GR derivation.
- **Lavender** — remaining semantic bridges, intermediate definitions, and
  intermediate derived structure.
- **Green** — principal section-level or manuscript-level structural
  conclusions.

### Node shape

- **Rounded rectangle** — derived result.
- **Hexagon** — physical/effective semantic bridge.
- **Ellipse** — imported external mathematics.

Color and shape are deliberately independent. For example, a green hexagon is
a principal manuscript-level conclusion whose final step still contains an
explicit effective coupling bridge; a yellow rounded rectangle can represent a
checked structural input/result that is supplied to a later stage.

## 3. Conceptual groups

| Stable group ID | Visible label | Logical status / shape | Figure role | Principal Lean anchors |
|---|---|---|---|---|
| `constraint-capacity` | Persistence constraints and reconfiguration capacity | Derived / rounded rectangle | Imported SBI-based structural capacity ordering | `CompatibleConfiguration`; `includedRequirements_noGreaterReconfigurationCapacity`; `structuralFrustration_capacityExhausted_and_reorganizationRequired` |
| `constraint-reachability` | Constraint-dependent reachability | Bridge / hexagon | Explicit antitone transition semantics and finite constrained reachability | `ConstraintReachabilitySemantics`; `includedRequirements_noGreaterReachabilityDomain`; `terminal_preserved_by_constraintStrengthening`; `limitingConfiguration_no_distinct_continuation` |
| `reachability-domain` | Constraint-strengthened and limiting reachability | Derived / rounded rectangle | Formal endpoint of the Section-4 reachability branch | `constraintStrengthening_characterization`; `limitingReachability_characterization` |
| `inertial-persistence` | Persistent inertial propagation (Newton I) | Derived / rounded rectangle | Pre-geometric structural Newton I | `unconstrainedPersistentContinuation_implies_NewtonFirstLawStructural` |
| `causal-duration` | Finite causal propagation from Time duration | Bridge / hexagon | Explicit use of Time duration to bound relational propagation depth | `CausalPropagationProcess`; `hasFiniteRelationalDepthRateBound` |
| `inertial-symmetry` | Operational inertial equivalence and causal symmetry | Bridge / hexagon | No absolute inertial marker and preservation of causal accessibility | `inertialEquivalence_excludes_absoluteMarker`; `operationalInertialRedescription_has_preLorentzSymmetry` |
| `lorentz-classification` | Imported Lorentz classification | External / ellipse | Standard inertial-kinematics classification | `StandardLorentzClassification`; `lorentz_of_standardClassification` |
| `kinematics-conclusion` | Spacetime kinematics | Derived / rounded rectangle | Section-2 synthesis | `SpacetimeKinematicsResult`; `spacetimeKinematics_characterization` |
| `effective-manifold` | Smooth effective manifold and coordinate invariance | Bridge / hexagon | Smooth coarse-grained representation and A1 coordinate redundancy | `EffectiveGeometricRepresentation`; `physicallyMeaningful_descriptor_is_coordinateInvariant` |
| `lorentzian-geometry` | Lorentz result to Lorentzian effective geometry | Bridge / hexagon | Explicit local Lorentz-to-Lorentzian representation bridge | `LorentzianGeometryBridge`; `lorentzianCausalStructure_of_standardClassification`; `effectiveGeometry_bridge_and_coordinateInvariance` |
| `metric-closure` | Closed metric state and second-order closure | Derived / rounded rectangle | Closed-state argument excluding irreducible higher-order metric dynamics | `MetricClosureSemantics`; `ClosedLocalMetricState`; `closedMetricState_excludes_irreducibleHigherOrder` |
| `local-conservation` | Coarse-grained local conservation | Bridge / hexagon | Local balance plus preservation-to-source-free bridge | `CoarseGrainedLocalBalance`; `PreservedQuantityBridge`; `localBalance_has_conservationStructure` |
| `effective-source` | Effective conserved source tensor | Bridge / hexagon | Tensorial/symmetric/covariantly conserved source representation | `EffectiveSourceTensorBridge`; `preservedQuantity_has_admissibleEffectiveSource` |
| `lovelock-premises` | GR structural premises for Lovelock | Bridge / hexagon | Establish GR-side premises before external theorem invocation | `EffectiveLovelockRegimeBridge`; `EffectiveLovelockPremises`; `effectiveLovelockPremises_of_closedEffectiveRegime` |
| `lovelock-interface` | Imported Lovelock theorem interface | External / ellipse | Standard four-dimensional Lovelock classification interface | `StandardLovelockClassification` |
| `lovelock-input` | Identification with Lovelock hypotheses | Bridge / hexagon | Explicit mapping from GR-side predicates to theorem predicates | `LovelockRegimeBridge`; `lovelockInput_of_effectivePremises` |
| `lovelock-result` | Lovelock geometric classification result | Derived / rounded rectangle | Einstein-plus-cosmological geometric form from imported theorem | `einsteinPlusCosmological_of_standardLovelock` |
| `einstein-synthesis` | Einstein-form geometry/source coupling | Bridge / hexagon | Couple classified geometry to admissible effective source | `EffectiveEinsteinCoupling`; `admissibleCoarseGrainedGeometry_has_EinsteinForm` |
| `effective-gr-conclusion` | Effective GR characterization | Derived / rounded rectangle | Final manuscript-facing GR bundle | `effectiveGR_characterization` |

## 4. Two intentionally separate proof components

The grouped architecture retains two components rather than adding an
interpretive edge for visual convenience.

### Effective-GR derivation

The principal branch contains the kinematical, geometric, closure,
conservation, external-classification, and Einstein-form stages. It represents
the conditional derivation of the effective GR structure once the explicit
regime and representation bridges are supplied.

### Constraint/reachability branch

The second branch contains:

`Persistence constraints and reconfiguration capacity`

-> `Constraint-dependent reachability`

-> `Constraint-strengthened and limiting reachability`.

This branch proves monotonicity and terminality statements. The manuscript
uses them to motivate a broader discussion of domain of applicability,
reachability horizons, and breakdown of the effective manifold. Those physical
interpretations are not inserted as artificial graph edges because the present
Lean development does not prove them as consequences of the effective-GR
bundle.

## 5. Important dependency-audit results

The refined map was introduced after a manuscript/formalization comparison and
preserves three corrections that should remain stable unless the proof
architecture itself changes.

### Newton I is not a premise of Lorentzian geometry

Structural Newton I is a genuine Section-2 result and belongs in the
`Spacetime kinematics` synthesis. The Section-3 manifold construction,
however, consumes the Lorentz classification result actually needed for the
Lorentzian causal-geometry bridge. The graph therefore does not route Newton I
through the manifold derivation.

### Lovelock premises precede the imported classification

The map separates:

1. GR-side structural premises;
2. identification of those premises with the external theorem predicates;
3. the imported Lovelock theorem interface;
4. the resulting Einstein-plus-cosmological geometric classification; and
5. coupling of that geometry to the effective source.

This prevents the graph from visually suggesting that the external Lovelock
theorem establishes the physical premises required to apply itself.

### Reachability is labelled only by what is proved

The formal endpoint is `Constraint-strengthened and limiting reachability`, not
`Domain of validity`. The latter is a manuscript-level physical interpretation
built from the formal reachability results plus additional statements about
smooth overlap, record-forming temporal continuation, and effective-theory
applicability.

## 6. Relation to the verification matrix

Every conceptual group above is mapped to one or more trace IDs in
`GR_Formal_Verification_Traceability_Matrix.md`. The compact
`GR_Main_Lean_Traceability_v1.txt` registry gives the corresponding
manuscript-facing Lean declarations.

The graph answers **what depends on what** inside the checked formal
architecture. The verification matrix answers the separate question **what
logical status each dependency has**: imported physical foundation, semantic
bridge, external mathematics, derived theorem, or manuscript-level scope
interpretation.

Both layers are required for a scientifically meaningful formal-verification
claim.