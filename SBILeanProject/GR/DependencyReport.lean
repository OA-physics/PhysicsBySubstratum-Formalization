import SBILeanProject.GR
import Lean
import Lean.Elab.Command
import Lean.Util.FoldConsts

set_option autoImplicit false

open Lean Elab Command

namespace GRDependencyReport

/-!
GR dependency and manuscript-traceability report.

The report has three distinct purposes and therefore deliberately emits
several views rather than forcing one graph to do every job.

1. `gr-dependencies.*` is the forensic declaration-level audit.  It retains
   checked project declarations but suppresses obvious automatically generated
   eliminator/no-confusion/size boilerplate that carries no manuscript-level
   information.

2. `gr-manuscript-map.*` is the declaration-level manuscript spine.  Helper
   implementation declarations are collapsed, but every edge is still derived
   from checked Lean dependencies.

3. `gr-grouped-map.*` is the principal human-facing proof architecture.
   Human-supplied groups identify manuscript proof steps; edges between those
   groups are still computed from checked declaration dependencies.

4. `gr-upstream-boundary.*` records direct checked dependencies from retained
   GR declarations into the companion SBI and Time formalizations.

The grouped graph distinguishes derived proof blocks, physical/effective
bridges and imported external mathematics by node shape.  These status labels
are traceability annotations only; they never create dependency edges.
-/

/-- All imported GR modules below this prefix belong to the GR project. -/
def projectModulePrefix : Name := `SBILeanProject.GR

/-- Imported formal layers immediately below GR. -/
def upstreamModulePrefixes : List Name := [
  `SBILeanProject.SBI,
  `SBILeanProject.Time
]

/-- Suppress kernel-generated constructors, recursors and quotient machinery. -/
def keepKind : ConstantKind → Bool
  | .ctor     => false
  | .recursor => false
  | .quot     => false
  | _         => true

/--
Suffixes used by Lean's automatically generated structure/eliminator support.
These declarations are useful to the kernel but make a human audit graph much
harder to inspect without adding physical or mathematical content.
-/
def generatedNoiseSuffixes : List String := [
  ".casesOn",
  ".recOn",
  ".noConfusion",
  ".noConfusionType",
  ".sizeOf_spec",
  ".mk.inj",
  ".mk.injEq"
]

/-- True when a declaration name is recognizable generated support noise. -/
def isGeneratedNoiseName (n : Name) : Bool :=
  let s := toString n
  generatedNoiseSuffixes.any fun suffix => s.endsWith suffix

/-- True for a user-facing declaration retained by the audit layer. -/
def isReportableDecl (env : Environment) (n : Name) : Bool :=
  if n.isInternal || isGeneratedNoiseName n then
    false
  else
    match env.find? n with
    | none    => false
    | some ci => keepKind (ConstantKind.ofConstantInfo ci)

/-- Collect declarations belonging to imported modules below a module prefix. -/
def declSetBelowPrefix (env : Environment) (pfx : Name) : NameSet := Id.run do
  let mut out : NameSet := {}
  for modName in env.header.moduleNames do
    if pfx.isPrefixOf modName then
      if let some idx := env.getModuleIdx? modName then
        let i := idx.toNat
        if h : i < env.header.moduleData.size then
          let modData := env.header.moduleData[i]'h
          for n in modData.constNames do
            out := out.insert n
  return out

/-- User-facing GR declarations only. -/
def reportableProjectDeclSet (env : Environment) : NameSet :=
  (declSetBelowPrefix env projectModulePrefix).filter (isReportableDecl env)

/-- User-facing declarations in imported SBI and Time modules. -/
def reportableUpstreamDeclSet (env : Environment) : NameSet := Id.run do
  let mut out : NameSet := {}
  for pfx in upstreamModulePrefixes do
    for n in (declSetBelowPrefix env pfx).toList do
      if isReportableDecl env n then
        out := out.insert n
  return out

/-- Constants used by a declaration, including structure constructor signatures. -/
def usedConstantsIncludingConstructors
    (env : Environment)
    (n : Name) : NameSet :=
  match env.find? n with
  | none => {}
  | some ci =>
      let own := ci.getUsedConstantsAsSet
      match ci with
      | .inductInfo info =>
          info.ctors.foldl
            (fun acc ctorName =>
              match env.find? ctorName with
              | none => acc
              | some ctorInfo =>
                  ctorInfo.getUsedConstantsAsSet.toList.foldl
                    (fun s d => s.insert d)
                    acc)
            own
      | _ => own

/-- Direct dependencies of `n`, restricted to a supplied declaration set. -/
def directDeps
    (env : Environment)
    (allowed : NameSet)
    (n : Name) : NameSet :=
  (usedConstantsIncludingConstructors env n).filter fun d =>
    (!(d == n)) && allowed.contains d

/-- DFS used for transitive dependency closure. -/
partial def transitiveLoop
    (env : Environment)
    (allowed : NameSet)
    (todo : List Name)
    (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
      if seen.contains n then
        transitiveLoop env allowed rest seen
      else
        let seen' := seen.insert n
        transitiveLoop env allowed
          ((directDeps env allowed n).toList ++ rest) seen'

/-- All allowed declarations on which `n` depends transitively. -/
def transitiveDeps
    (env : Environment)
    (allowed : NameSet)
    (n : Name) : NameSet :=
  let closure :=
    transitiveLoop env allowed (directDeps env allowed n).toList {}
  closure.filter fun d => !(d == n)

/-- Module containing a declaration, when available. -/
def moduleNameOf? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let i := idx.toNat
  if h : i < env.header.moduleNames.size then
    some (env.header.moduleNames[i]'h)
  else
    none

/-- Human-readable kernel declaration kind. -/
def kindString (ci : ConstantInfo) : String :=
  match ConstantKind.ofConstantInfo ci with
  | .axiom    => "axiom"
  | .defn     => "definition"
  | .thm      => "theorem"
  | .opaque   => "opaque"
  | .induct   => "inductive/structure"
  | .ctor     => "constructor"
  | .recursor => "recursor"
  | .quot     => "quotient"

/-- Quote one CSV field. -/
def csv (s : String) : String :=
  "\"" ++ s.replace "\"" "\"\"" ++ "\""

/-- Render a NameSet as a semicolon-separated list. -/
def renderNames (s : NameSet) : String :=
  String.intercalate "; " (s.toList.map toString)

/-- Escape a Graphviz quoted string. -/
def dotQuote (s : String) : String :=
  "\"" ++ ((s.replace "\\" "\\\\").replace "\"" "\\\"") ++ "\""

/-- Escape XML/GraphML text. -/
def xmlEscape (s : String) : String :=
  ((((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;").replace "\"" "&quot;").replace "'" "&apos;"

/-- Compact visible declaration label. -/
def shortNameString : Name → String
  | .anonymous => "<anonymous>"
  | .str _ s   => s
  | .num _ i   => toString i

/-- Position of a declaration name in a list. -/
def nameIndexAux (target : Name) : List Name → Nat → Option Nat
  | [], _ => none
  | n :: ns, i =>
      if n == target then some i else nameIndexAux target ns (i + 1)

/-- Stable GraphML node id. -/
def graphmlNodeId? (names : List Name) (n : Name) : Option String := do
  let i ← nameIndexAux n names 0
  return "n" ++ toString i

/-!
===============================================================================
MANUSCRIPT LOGICAL SPINE
===============================================================================
-/

/--
Fully qualified declarations retained in the manuscript-level audit.

The list is intentionally more selective than the full declaration audit but
still fine-grained enough that the grouped map can be independently checked
against recognizable Lean interfaces.
-/
def spineNames : List String := [
  "SBI.GR.CompatibleConfiguration",
  "SBI.GR.RequirementFamilyIncluded",
  "SBI.GR.NoGreaterReconfigurationCapacity",
  "SBI.GR.includedRequirements_noGreaterReconfigurationCapacity",
  "SBI.GR.StrictlyLowerReconfigurationCapacity",
  "SBI.GR.ReconfigurationCapacityExhausted",
  "SBI.GR.structuralFrustration_capacityExhausted_and_reorganizationRequired",

  "SBI.GR.ConstraintReachabilitySemantics",
  "SBI.GR.ConstrainedReachability",
  "SBI.GR.NoGreaterReachabilityDomain",
  "SBI.GR.includedRequirements_noGreaterReachabilityDomain",
  "SBI.GR.TerminalUnderConstraints",
  "SBI.GR.terminal_preserved_by_constraintStrengthening",
  "SBI.GR.LimitingReachabilityConfiguration",
  "SBI.GR.limitingConfiguration_no_distinct_continuation",

  "SBI.GR.MetricClosureSemantics",
  "SBI.GR.ClosedLocalMetricState",
  "SBI.GR.HasIndependentContinuationData",
  "SBI.GR.closedLocalMetricState_no_independentContinuation",
  "SBI.GR.closedMetricState_excludes_irreducibleHigherOrder",
  "SBI.GR.irreducibleHigherOrder_not_metricOnlyClosed",

  "SBI.GR.PropagationChangeSemantics",
  "SBI.GR.propagationChange_requires_relationalSupport",
  "SBI.GR.noRelationalSupport_noPropagationChange",
  "SBI.GR.UnconstrainedPersistentContinuation",
  "SBI.GR.NewtonFirstLawStructural",
  "SBI.GR.unconstrainedPersistentContinuation_implies_NewtonFirstLawStructural",

  "SBI.GR.CausalPropagationProcess",
  "SBI.GR.CausalPropagationProcess.accumulatedDuration_pos_of_depth_pos",
  "SBI.GR.CausalPropagationProcess.depth_times_stepDuration_le_duration",
  "SBI.GR.HasFiniteRelationalDepthRateBound",
  "SBI.GR.CausalPropagationProcess.hasFiniteRelationalDepthRateBound",

  "SBI.GR.InertialEquivalenceSemantics",
  "SBI.GR.inertialEquivalent_descriptors_agree",
  "SBI.GR.NoAbsoluteInertialMarker",
  "SBI.GR.inertialEquivalence_excludes_absoluteMarker",
  "SBI.GR.CausalAccessibilitySemantics",
  "SBI.GR.causalAccessibility_eq_of_relEq",
  "SBI.GR.OperationalInertialRedescription",
  "SBI.GR.OperationalInertialRedescription.toInertialRedescription",
  "SBI.GR.PreservesCausalStructure",
  "SBI.GR.operationalInertialRedescription_preservesCausalStructure",
  "SBI.GR.PreLorentzInertialSymmetry",
  "SBI.GR.operationalInertialRedescription_has_preLorentzSymmetry",

  "SBI.GR.StandardLorentzClassification",
  "SBI.GR.LorentzClassificationInput",
  "SBI.GR.lorentz_of_standardClassification",

  "SBI.GR.SpacetimeKinematicsResult",
  "SBI.GR.spacetimeKinematics_characterization",

  "SBI.GR.EffectiveGeometricRepresentation",
  "SBI.GR.EffectiveGeometricRepresentation.CoordinateInvariant",
  "SBI.GR.coordinateEquivalent_descriptors_agree",
  "SBI.GR.physicallyMeaningful_descriptor_is_coordinateInvariant",
  "SBI.GR.LorentzianGeometryBridge",
  "SBI.GR.lorentzianCausalStructure_of_lorentzResult",
  "SBI.GR.lorentzianCausalStructure_of_spacetimeKinematics",
  "SBI.GR.effectiveGeometry_bridge_and_coordinateInvariance",

  "SBI.GR.CoarseGrainedLocalBalance",
  "SBI.GR.SourceFreeQuantity",
  "SBI.GR.LocallyConservedQuantity",
  "SBI.GR.PreservedQuantityBridge",
  "SBI.GR.preservedQuantity_is_locallyConserved",
  "SBI.GR.HasLocalConservationStructure",
  "SBI.GR.localBalance_has_conservationStructure",

  "SBI.GR.EffectiveSourceTensorBridge",
  "SBI.GR.HasAdmissibleEffectiveSource",
  "SBI.GR.preservedQuantity_has_admissibleEffectiveSource",

  "SBI.GR.StandardLovelockClassification",
  "SBI.GR.LovelockClassificationInput",
  "SBI.GR.einsteinPlusCosmological_of_standardLovelock",

  "SBI.GR.LovelockRegimeBridge",
  "SBI.GR.lovelockInput_of_closedEffectiveRegime",

  "SBI.GR.EffectiveEinsteinCoupling",
  "SBI.GR.admissibleCoarseGrainedGeometry_has_EinsteinForm",

  "SBI.GR.constraintStrengthening_characterization",
  "SBI.GR.limitingReachability_characterization",
  "SBI.GR.effectiveGR_characterization"
]

/-- Retained declarations in the current checked environment. -/
def spineDeclSet (allowed : NameSet) : NameSet :=
  allowed.filter fun n => spineNames.contains (toString n)

/-- Explicit physical or coarse-graining bridges. -/
def bridgeNames : List String := [
  "SBI.GR.ConstraintReachabilitySemantics",
  "SBI.GR.PropagationChangeSemantics",
  "SBI.GR.CausalPropagationProcess",
  "SBI.GR.InertialEquivalenceSemantics",
  "SBI.GR.CausalAccessibilitySemantics",
  "SBI.GR.OperationalInertialRedescription",
  "SBI.GR.EffectiveGeometricRepresentation",
  "SBI.GR.LorentzianGeometryBridge",
  "SBI.GR.MetricClosureSemantics",
  "SBI.GR.CoarseGrainedLocalBalance",
  "SBI.GR.PreservedQuantityBridge",
  "SBI.GR.EffectiveSourceTensorBridge",
  "SBI.GR.LovelockRegimeBridge",
  "SBI.GR.EffectiveEinsteinCoupling"
]

/-- Interfaces whose substantive theorem is imported standard mathematics. -/
def externalMathNames : List String := [
  "SBI.GR.StandardLorentzClassification",
  "SBI.GR.LorentzClassificationInput",
  "SBI.GR.StandardLovelockClassification",
  "SBI.GR.LovelockClassificationInput"
]

/-- Manuscript-facing logical status of a retained declaration. -/
def logicalStatus (env : Environment) (n : Name) : String :=
  let s := toString n
  if externalMathNames.contains s then
    "External mathematics"
  else if bridgeNames.contains s then
    "Physical/effective bridge"
  else
    match env.find? n with
    | some ci =>
        match ConstantKind.ofConstantInfo ci with
        | .thm => "Derived result"
        | _    => "Definition"
    | none => "Definition"

/-- yEd shape associated with declaration-level logical status. -/
def logicalShape (env : Environment) (n : Name) : String :=
  match logicalStatus env n with
  | "Derived result"            => "roundrectangle"
  | "Physical/effective bridge" => "hexagon"
  | "External mathematics"      => "ellipse"
  | _                           => "rectangle"

/-- Traverse omitted nodes until the nearest retained dependency is reached. -/
partial def collapsedFrontierLoop
    (env : Environment)
    (allowed retained : NameSet)
    (todo : List Name)
    (seen out : NameSet) : NameSet :=
  match todo with
  | [] => out
  | n :: rest =>
      if seen.contains n then
        collapsedFrontierLoop env allowed retained rest seen out
      else
        let seen' := seen.insert n
        if retained.contains n then
          collapsedFrontierLoop env allowed retained rest seen' (out.insert n)
        else
          collapsedFrontierLoop env allowed retained
            ((directDeps env allowed n).toList ++ rest) seen' out

/-- Nearest retained dependencies after implementation details are collapsed. -/
def collapsedFrontierDeps
    (env : Environment)
    (allowed retained : NameSet)
    (n : Name) : NameSet :=
  let out := collapsedFrontierLoop env allowed retained
    (directDeps env allowed n).toList {} {}
  out.filter fun d => !(d == n)

/-- Reachability in the retained dependency graph. -/
partial def spineReachableLoop
    (env : Environment)
    (allowed retained : NameSet)
    (target : Name)
    (todo : List Name)
    (seen : NameSet) : Bool :=
  match todo with
  | [] => false
  | n :: rest =>
      if n == target then true
      else if seen.contains n then
        spineReachableLoop env allowed retained target rest seen
      else
        let seen' := seen.insert n
        spineReachableLoop env allowed retained target
          ((collapsedFrontierDeps env allowed retained n).toList ++ rest)
          seen'

/-- Reachability predicate for transitive reduction. -/
def spineReachable
    (env : Environment)
    (allowed retained : NameSet)
    (start target : Name) : Bool :=
  spineReachableLoop env allowed retained target [start] {}

/-- Transitively reduced dependencies in the retained manuscript spine. -/
def transitiveReducedSpineDeps
    (env : Environment)
    (allowed retained : NameSet)
    (n : Name) : NameSet :=
  let deps := collapsedFrontierDeps env allowed retained n
  deps.filter fun d =>
    !(deps.toList.any fun alt =>
      (!(alt == d)) && spineReachable env allowed retained alt d)

/-- Count edges generated by a dependency function on retained names. -/
def countRetainedEdges
    (names : List Name)
    (depsOf : Name → NameSet) : Nat :=
  names.foldl (fun total n => total + (depsOf n).toList.length) 0


/-!
===============================================================================
GROUPED MANUSCRIPT MAP
===============================================================================

Groups are human-supplied manuscript traceability.  Group-to-group edges are
not supplied by hand: dependency traversal starts at each group's interface
declarations and follows the checked declaration graph until another group is
reached.
-/

structure ManuscriptGroup where
  id : String
  label : String
  members : List String
  interfaces : List String

/-- Conceptual proof groups for the human-facing GR architecture. -/
def manuscriptGroups : List ManuscriptGroup := [
  {
    id := "constraint-capacity"
    label := "Persistence constraints and reconfiguration capacity"
    members := [
      "SBI.GR.CompatibleConfiguration",
      "SBI.GR.RequirementFamilyIncluded",
      "SBI.GR.NoGreaterReconfigurationCapacity",
      "SBI.GR.includedRequirements_noGreaterReconfigurationCapacity",
      "SBI.GR.StrictlyLowerReconfigurationCapacity",
      "SBI.GR.ReconfigurationCapacityExhausted",
      "SBI.GR.structuralFrustration_capacityExhausted_and_reorganizationRequired"
    ]
    interfaces := [
      "SBI.GR.includedRequirements_noGreaterReconfigurationCapacity",
      "SBI.GR.structuralFrustration_capacityExhausted_and_reorganizationRequired"
    ]
  },
  {
    id := "constraint-reachability"
    label := "Constraint-dependent reachability"
    members := [
      "SBI.GR.ConstraintReachabilitySemantics",
      "SBI.GR.ConstrainedReachability",
      "SBI.GR.NoGreaterReachabilityDomain",
      "SBI.GR.includedRequirements_noGreaterReachabilityDomain",
      "SBI.GR.TerminalUnderConstraints",
      "SBI.GR.terminal_preserved_by_constraintStrengthening",
      "SBI.GR.LimitingReachabilityConfiguration",
      "SBI.GR.limitingConfiguration_no_distinct_continuation"
    ]
    interfaces := [
      "SBI.GR.includedRequirements_noGreaterReachabilityDomain",
      "SBI.GR.terminal_preserved_by_constraintStrengthening",
      "SBI.GR.limitingConfiguration_no_distinct_continuation"
    ]
  },
  {
    id := "reachability-domain"
    label := "Reachability limits and domain of validity"
    members := [
      "SBI.GR.constraintStrengthening_characterization",
      "SBI.GR.limitingReachability_characterization"
    ]
    interfaces := [
      "SBI.GR.constraintStrengthening_characterization",
      "SBI.GR.limitingReachability_characterization"
    ]
  },
  {
    id := "inertial-persistence"
    label := "Persistent inertial propagation (Newton I)"
    members := [
      "SBI.GR.PropagationChangeSemantics",
      "SBI.GR.propagationChange_requires_relationalSupport",
      "SBI.GR.noRelationalSupport_noPropagationChange",
      "SBI.GR.UnconstrainedPersistentContinuation",
      "SBI.GR.NewtonFirstLawStructural",
      "SBI.GR.unconstrainedPersistentContinuation_implies_NewtonFirstLawStructural"
    ]
    interfaces := [
      "SBI.GR.unconstrainedPersistentContinuation_implies_NewtonFirstLawStructural"
    ]
  },
  {
    id := "causal-duration"
    label := "Finite causal propagation from Time duration"
    members := [
      "SBI.GR.CausalPropagationProcess",
      "SBI.GR.CausalPropagationProcess.accumulatedDuration_pos_of_depth_pos",
      "SBI.GR.CausalPropagationProcess.depth_times_stepDuration_le_duration",
      "SBI.GR.HasFiniteRelationalDepthRateBound",
      "SBI.GR.CausalPropagationProcess.hasFiniteRelationalDepthRateBound"
    ]
    interfaces := [
      "SBI.GR.CausalPropagationProcess.hasFiniteRelationalDepthRateBound"
    ]
  },
  {
    id := "inertial-symmetry"
    label := "Operational inertial equivalence and causal symmetry"
    members := [
      "SBI.GR.InertialEquivalenceSemantics",
      "SBI.GR.inertialEquivalent_descriptors_agree",
      "SBI.GR.NoAbsoluteInertialMarker",
      "SBI.GR.inertialEquivalence_excludes_absoluteMarker",
      "SBI.GR.CausalAccessibilitySemantics",
      "SBI.GR.causalAccessibility_eq_of_relEq",
      "SBI.GR.OperationalInertialRedescription",
      "SBI.GR.OperationalInertialRedescription.toInertialRedescription",
      "SBI.GR.PreservesCausalStructure",
      "SBI.GR.operationalInertialRedescription_preservesCausalStructure",
      "SBI.GR.PreLorentzInertialSymmetry",
      "SBI.GR.operationalInertialRedescription_has_preLorentzSymmetry"
    ]
    interfaces := [
      "SBI.GR.inertialEquivalence_excludes_absoluteMarker",
      "SBI.GR.operationalInertialRedescription_has_preLorentzSymmetry"
    ]
  },
  {
    id := "lorentz-classification"
    label := "Imported Lorentz classification"
    members := [
      "SBI.GR.StandardLorentzClassification",
      "SBI.GR.LorentzClassificationInput",
      "SBI.GR.lorentz_of_standardClassification"
    ]
    interfaces := ["SBI.GR.lorentz_of_standardClassification"]
  },
  {
    id := "kinematics-conclusion"
    label := "Spacetime kinematics"
    members := [
      "SBI.GR.SpacetimeKinematicsResult",
      "SBI.GR.spacetimeKinematics_characterization"
    ]
    interfaces := ["SBI.GR.spacetimeKinematics_characterization"]
  },
  {
    id := "effective-manifold"
    label := "Smooth effective manifold and coordinate invariance"
    members := [
      "SBI.GR.EffectiveGeometricRepresentation",
      "SBI.GR.EffectiveGeometricRepresentation.CoordinateInvariant",
      "SBI.GR.coordinateEquivalent_descriptors_agree",
      "SBI.GR.physicallyMeaningful_descriptor_is_coordinateInvariant"
    ]
    interfaces := ["SBI.GR.physicallyMeaningful_descriptor_is_coordinateInvariant"]
  },
  {
    id := "lorentzian-geometry"
    label := "Kinematics to Lorentzian effective geometry"
    members := [
      "SBI.GR.LorentzianGeometryBridge",
      "SBI.GR.lorentzianCausalStructure_of_lorentzResult",
      "SBI.GR.lorentzianCausalStructure_of_spacetimeKinematics",
      "SBI.GR.effectiveGeometry_bridge_and_coordinateInvariance"
    ]
    interfaces := [
      "SBI.GR.lorentzianCausalStructure_of_spacetimeKinematics",
      "SBI.GR.effectiveGeometry_bridge_and_coordinateInvariance"
    ]
  },
  {
    id := "metric-closure"
    label := "Closed metric state and second-order closure"
    members := [
      "SBI.GR.MetricClosureSemantics",
      "SBI.GR.ClosedLocalMetricState",
      "SBI.GR.HasIndependentContinuationData",
      "SBI.GR.closedLocalMetricState_no_independentContinuation",
      "SBI.GR.closedMetricState_excludes_irreducibleHigherOrder",
      "SBI.GR.irreducibleHigherOrder_not_metricOnlyClosed"
    ]
    interfaces := ["SBI.GR.closedMetricState_excludes_irreducibleHigherOrder"]
  },
  {
    id := "local-conservation"
    label := "Coarse-grained local conservation"
    members := [
      "SBI.GR.CoarseGrainedLocalBalance",
      "SBI.GR.SourceFreeQuantity",
      "SBI.GR.LocallyConservedQuantity",
      "SBI.GR.PreservedQuantityBridge",
      "SBI.GR.preservedQuantity_is_locallyConserved",
      "SBI.GR.HasLocalConservationStructure",
      "SBI.GR.localBalance_has_conservationStructure"
    ]
    interfaces := ["SBI.GR.localBalance_has_conservationStructure"]
  },
  {
    id := "effective-source"
    label := "Effective conserved source tensor"
    members := [
      "SBI.GR.EffectiveSourceTensorBridge",
      "SBI.GR.HasAdmissibleEffectiveSource",
      "SBI.GR.preservedQuantity_has_admissibleEffectiveSource"
    ]
    interfaces := ["SBI.GR.preservedQuantity_has_admissibleEffectiveSource"]
  },
  {
    id := "lovelock-applicability"
    label := "Effective geometry satisfies Lovelock hypotheses"
    members := [
      "SBI.GR.LovelockRegimeBridge",
      "SBI.GR.lovelockInput_of_closedEffectiveRegime"
    ]
    interfaces := ["SBI.GR.lovelockInput_of_closedEffectiveRegime"]
  },
  {
    id := "lovelock-classification"
    label := "Imported Lovelock classification"
    members := [
      "SBI.GR.StandardLovelockClassification",
      "SBI.GR.LovelockClassificationInput",
      "SBI.GR.einsteinPlusCosmological_of_standardLovelock"
    ]
    interfaces := ["SBI.GR.einsteinPlusCosmological_of_standardLovelock"]
  },
  {
    id := "einstein-synthesis"
    label := "Einstein-form geometry/source coupling"
    members := [
      "SBI.GR.EffectiveEinsteinCoupling",
      "SBI.GR.admissibleCoarseGrainedGeometry_has_EinsteinForm"
    ]
    interfaces := ["SBI.GR.admissibleCoarseGrainedGeometry_has_EinsteinForm"]
  },
  {
    id := "effective-gr-conclusion"
    label := "Effective GR characterization"
    members := ["SBI.GR.effectiveGR_characterization"]
    interfaces := ["SBI.GR.effectiveGR_characterization"]
  }
]

/-- Group ids representing imported standard mathematics. -/
def externalGroupIds : List String := [
  "lorentz-classification",
  "lovelock-classification"
]

/-- Group ids dominated by an explicit physical/effective bridge. -/
def bridgeGroupIds : List String := [
  "constraint-reachability",
  "causal-duration",
  "inertial-symmetry",
  "effective-manifold",
  "lorentzian-geometry",
  "local-conservation",
  "effective-source",
  "lovelock-applicability",
  "einstein-synthesis"
]

/-- Human-facing logical status of one conceptual proof group. -/
def groupLogicalStatus (g : ManuscriptGroup) : String :=
  if externalGroupIds.contains g.id then
    "External mathematics"
  else if bridgeGroupIds.contains g.id then
    "Physical/effective bridge"
  else
    "Derived result"

/-- yEd shape for one conceptual proof group. -/
def groupShape (g : ManuscriptGroup) : String :=
  match groupLogicalStatus g with
  | "External mathematics"      => "ellipse"
  | "Physical/effective bridge" => "hexagon"
  | _                           => "roundrectangle"

/-- Does group `g` contain declaration `n`? -/
def groupContains (g : ManuscriptGroup) (n : Name) : Bool :=
  g.members.contains (toString n)

/-- Find the conceptual group containing a declaration. -/
def groupOf? (n : Name) : Option ManuscriptGroup :=
  manuscriptGroups.find? fun g => groupContains g n

/-- Number of conceptual groups containing a declaration. -/
def groupMembershipCount (n : Name) : Nat :=
  manuscriptGroups.foldl
    (fun total g => if groupContains g n then total + 1 else total) 0

/-- Retained declarations assigned to a conceptual group. -/
def retainedMembersOfGroup
    (retained : NameSet)
    (g : ManuscriptGroup) : List Name :=
  retained.toList.filter fun n => groupContains g n

/-- Retained interface declarations assigned to a conceptual group. -/
def retainedInterfacesOfGroup
    (retained : NameSet)
    (g : ManuscriptGroup) : List Name :=
  (retainedMembersOfGroup retained g).filter fun n =>
    g.interfaces.contains (toString n)

/-- Conceptual groups present in the current checked spine. -/
def presentGroups (retained : NameSet) : List ManuscriptGroup :=
  manuscriptGroups.filter fun g =>
    !(retainedMembersOfGroup retained g).isEmpty

/-- Append a group id only once. -/
def appendUniqueString (xs : List String) (s : String) : List String :=
  if xs.contains s then xs else xs ++ [s]

/--
Traverse checked dependencies from one group interface until another
conceptual group is reached.
-/
partial def groupFrontierLoop
    (env : Environment)
    (allowed retained : NameSet)
    (currentGroupId : String)
    (todo : List Name)
    (seen : NameSet)
    (out : List String) : List String :=
  match todo with
  | [] => out
  | n :: rest =>
      if seen.contains n then
        groupFrontierLoop env allowed retained currentGroupId rest seen out
      else
        let seen' := seen.insert n
        match groupOf? n with
        | none =>
            groupFrontierLoop env allowed retained currentGroupId
              ((collapsedFrontierDeps env allowed retained n).toList ++ rest)
              seen' out
        | some dg =>
            if dg.id == currentGroupId then
              groupFrontierLoop env allowed retained currentGroupId
                ((collapsedFrontierDeps env allowed retained n).toList ++ rest)
                seen' out
            else
              groupFrontierLoop env allowed retained currentGroupId rest seen'
                (appendUniqueString out dg.id)

/-- Direct checked dependencies between conceptual groups. -/
def groupDirectDeps
    (env : Environment)
    (allowed retained : NameSet)
    (g : ManuscriptGroup) : List String := Id.run do
  let mut start : List Name := []
  for n in retainedInterfacesOfGroup retained g do
    start := (collapsedFrontierDeps env allowed retained n).toList ++ start
  return groupFrontierLoop env allowed retained g.id start {} []

/-- Find one conceptual group by stable id. -/
def groupById? (id : String) : Option ManuscriptGroup :=
  manuscriptGroups.find? fun g => g.id == id

/-- Reachability in the conceptual-group dependency graph. -/
partial def groupReachableLoop
    (env : Environment)
    (allowed retained : NameSet)
    (target : String)
    (todo seen : List String) : Bool :=
  match todo with
  | [] => false
  | current :: rest =>
      if current == target then true
      else if seen.contains current then
        groupReachableLoop env allowed retained target rest seen
      else
        let seen' := current :: seen
        match groupById? current with
        | none =>
            groupReachableLoop env allowed retained target rest seen'
        | some g =>
            groupReachableLoop env allowed retained target
              (groupDirectDeps env allowed retained g ++ rest) seen'

/-- Conceptual-group reachability predicate. -/
def groupReachable
    (env : Environment)
    (allowed retained : NameSet)
    (start target : String) : Bool :=
  groupReachableLoop env allowed retained target [start] []

/-- Transitive reduction of the conceptual-group dependency relation. -/
def transitiveReducedGroupDeps
    (env : Environment)
    (allowed retained : NameSet)
    (g : ManuscriptGroup) : List String :=
  let deps := groupDirectDeps env allowed retained g
  deps.filter fun d =>
    !(deps.any fun alt =>
      (!(alt == d)) && groupReachable env allowed retained alt d)

/-- Zero-based position of a group id. -/
def groupIndexAux
    (target : String) : List ManuscriptGroup → Nat → Option Nat
  | [], _ => none
  | g :: gs, i =>
      if g.id == target then some i else groupIndexAux target gs (i + 1)

/-- Stable GraphML node id for a conceptual group. -/
def groupNodeId?
    (groups : List ManuscriptGroup)
    (id : String) : Option String := do
  let i ← groupIndexAux id groups 0
  return "g" ++ toString i


/-!
===============================================================================
REPORT GENERATORS
===============================================================================
-/

def generateAuditReports
    (env : Environment) : String × String × String × String := Id.run do
  let allowed := reportableProjectDeclSet env
  let names := allowed.toList

  let mut csvLines : Array String := #[
    "declaration,module,kind,direct_gr_dependencies,transitive_gr_dependencies"
  ]

  let mut mdLines : Array String := #[
    "# GR Lean dependency report",
    "",
    "Forensic declaration-level audit. Obvious automatically generated eliminator/no-confusion/size boilerplate is suppressed, but checked GR declarations and their project-local dependencies remain visible.",
    "",
    "| Declaration | Module | Kind | Direct GR dependencies | Transitive GR dependencies |",
    "|---|---|---|---|---|"
  ]

  let mut dotLines : Array String := #[
    "digraph GR_Dependencies {",
    "  rankdir=LR;",
    "  node [shape=box];"
  ]

  let mut graphmlLines : Array String := #[
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
    "<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:y=\"http://www.yworks.com/xml/graphml\">",
    "  <key id=\"d0\" for=\"node\" attr.name=\"declaration\" attr.type=\"string\"/>",
    "  <key id=\"d1\" for=\"node\" attr.name=\"module\" attr.type=\"string\"/>",
    "  <key id=\"d2\" for=\"node\" attr.name=\"kind\" attr.type=\"string\"/>",
    "  <key id=\"d3\" for=\"node\" yfiles.type=\"nodegraphics\"/>",
    "  <key id=\"d4\" for=\"edge\" yfiles.type=\"edgegraphics\"/>",
    "  <graph id=\"G\" edgedefault=\"directed\">"
  ]

  let mut nodeIndex : Nat := 0

  for n in names do
    if let some ci := env.find? n then
      let direct := directDeps env allowed n
      let trans := transitiveDeps env allowed n
      let modName :=
        match moduleNameOf? env n with
        | some m => toString m
        | none => "<unknown>"
      let k := kindString ci
      let nS := toString n

      csvLines := csvLines.push <|
        String.intercalate "," [
          csv nS, csv modName, csv k,
          csv (renderNames direct), csv (renderNames trans)
        ]

      mdLines := mdLines.push <|
        "| `" ++ nS ++ "` | `" ++ modName ++ "` | " ++ k ++
        " | " ++ renderNames direct ++ " | " ++ renderNames trans ++ " |"

      dotLines := dotLines.push <| "  " ++ dotQuote nS ++ ";"
      for d in direct.toList do
        dotLines := dotLines.push <|
          "  " ++ dotQuote nS ++ " -> " ++ dotQuote (toString d) ++ ";"

      let nodeId := "n" ++ toString nodeIndex
      graphmlLines := graphmlLines.push <|
        "    <node id=\"" ++ nodeId ++ "\"><data key=\"d0\">" ++
        xmlEscape nS ++ "</data><data key=\"d1\">" ++
        xmlEscape modName ++ "</data><data key=\"d2\">" ++
        xmlEscape k ++ "</data><data key=\"d3\"><y:ShapeNode><y:NodeLabel>" ++
        xmlEscape (shortNameString n) ++
        "</y:NodeLabel><y:Shape type=\"rectangle\"/></y:ShapeNode></data></node>"

      nodeIndex := nodeIndex + 1

  dotLines := dotLines.push "}"

  let mut edgeIndex : Nat := 0
  for n in names do
    if let some sourceId := graphmlNodeId? names n then
      for d in (directDeps env allowed n).toList do
        if let some targetId := graphmlNodeId? names d then
          graphmlLines := graphmlLines.push <|
            "    <edge id=\"e" ++ toString edgeIndex ++
            "\" source=\"" ++ sourceId ++ "\" target=\"" ++ targetId ++
            "\"><data key=\"d4\"><y:PolyLineEdge><y:Arrows source=\"none\" target=\"standard\"/></y:PolyLineEdge></data></edge>"
          edgeIndex := edgeIndex + 1

  graphmlLines := graphmlLines.push "  </graph>"
  graphmlLines := graphmlLines.push "</graphml>"

  return (String.intercalate "\n" csvLines.toList ++ "\n",
          String.intercalate "\n" mdLines.toList ++ "\n",
          String.intercalate "\n" dotLines.toList ++ "\n",
          String.intercalate "\n" graphmlLines.toList ++ "\n")


def generateManuscriptMapReports
    (env : Environment) : String × String × String := Id.run do
  let allowed := reportableProjectDeclSet env
  let retained := spineDeclSet allowed
  let names := retained.toList

  let mut csvLines : Array String := #[
    "declaration,module,kind,logical_status,principal_dependencies,reduced_dependencies"
  ]

  let mut mdLines : Array String := #[
    "# GR manuscript logical map",
    "",
    "Implementation declarations are collapsed. All dependency edges are derived from checked Lean dependencies.",
    "",
    "| Declaration | Module | Kind | Logical status | Principal dependencies | Reduced dependencies |",
    "|---|---|---|---|---|---|"
  ]

  let mut graphmlLines : Array String := #[
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
    "<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:y=\"http://www.yworks.com/xml/graphml\">",
    "  <key id=\"d0\" for=\"node\" attr.name=\"declaration\" attr.type=\"string\"/>",
    "  <key id=\"d1\" for=\"node\" attr.name=\"logical_status\" attr.type=\"string\"/>",
    "  <key id=\"d2\" for=\"node\" yfiles.type=\"nodegraphics\"/>",
    "  <key id=\"d3\" for=\"edge\" yfiles.type=\"edgegraphics\"/>",
    "  <graph id=\"G\" edgedefault=\"directed\">"
  ]

  let mut nodeIndex : Nat := 0
  for n in names do
    if let some ci := env.find? n then
      let principal := collapsedFrontierDeps env allowed retained n
      let reduced := transitiveReducedSpineDeps env allowed retained n
      let modName :=
        match moduleNameOf? env n with
        | some m => toString m
        | none => "<unknown>"
      let status := logicalStatus env n
      let k := kindString ci
      let nS := toString n

      csvLines := csvLines.push <|
        String.intercalate "," [
          csv nS, csv modName, csv k, csv status,
          csv (renderNames principal), csv (renderNames reduced)
        ]

      mdLines := mdLines.push <|
        "| `" ++ nS ++ "` | `" ++ modName ++ "` | " ++ k ++
        " | " ++ status ++ " | " ++ renderNames principal ++
        " | " ++ renderNames reduced ++ " |"

      let nodeId := "n" ++ toString nodeIndex
      graphmlLines := graphmlLines.push <|
        "    <node id=\"" ++ nodeId ++ "\"><data key=\"d0\">" ++
        xmlEscape nS ++ "</data><data key=\"d1\">" ++
        xmlEscape status ++ "</data><data key=\"d2\"><y:ShapeNode><y:NodeLabel>" ++
        xmlEscape (shortNameString n) ++ "</y:NodeLabel><y:Shape type=\"" ++
        logicalShape env n ++ "\"/></y:ShapeNode></data></node>"

      nodeIndex := nodeIndex + 1

  let mut edgeIndex : Nat := 0
  for dependent in names do
    if let some dependentId := graphmlNodeId? names dependent then
      for dependency in
          (transitiveReducedSpineDeps env allowed retained dependent).toList do
        if let some dependencyId := graphmlNodeId? names dependency then
          graphmlLines := graphmlLines.push <|
            "    <edge id=\"e" ++ toString edgeIndex ++
            "\" source=\"" ++ dependencyId ++ "\" target=\"" ++ dependentId ++
            "\"><data key=\"d3\"><y:PolyLineEdge><y:Arrows source=\"none\" target=\"standard\"/></y:PolyLineEdge></data></edge>"
          edgeIndex := edgeIndex + 1

  graphmlLines := graphmlLines.push "  </graph>"
  graphmlLines := graphmlLines.push "</graphml>"

  return (String.intercalate "\n" csvLines.toList ++ "\n",
          String.intercalate "\n" mdLines.toList ++ "\n",
          String.intercalate "\n" graphmlLines.toList ++ "\n")


def generateGroupedReports
    (env : Environment) : String × String × String := Id.run do
  let allowed := reportableProjectDeclSet env
  let retained := spineDeclSet allowed
  let groups := presentGroups retained

  let mut csvLines : Array String := #[
    "group_id,label,logical_status,lean_members,interface_declarations,direct_group_dependencies,reduced_group_dependencies"
  ]

  let mut mdLines : Array String := #[
    "# GR grouped manuscript proof map",
    "",
    "This is the principal human-facing proof architecture. Group membership is manuscript traceability; every edge between groups is derived from checked Lean declaration dependencies.",
    "",
    "Node status distinguishes derived proof blocks, explicit physical/effective bridges, and imported standard mathematics.",
    "",
    "| Proof group | Status | Lean declarations | Interface declarations | Direct checked dependencies | Reduced dependencies |",
    "|---|---|---|---|---|---|"
  ]

  let mut graphmlLines : Array String := #[
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
    "<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:y=\"http://www.yworks.com/xml/graphml\">",
    "  <key id=\"d0\" for=\"node\" attr.name=\"group_id\" attr.type=\"string\"/>",
    "  <key id=\"d1\" for=\"node\" attr.name=\"label\" attr.type=\"string\"/>",
    "  <key id=\"d2\" for=\"node\" attr.name=\"logical_status\" attr.type=\"string\"/>",
    "  <key id=\"d3\" for=\"node\" attr.name=\"lean_members\" attr.type=\"string\"/>",
    "  <key id=\"d4\" for=\"node\" yfiles.type=\"nodegraphics\"/>",
    "  <key id=\"d5\" for=\"edge\" yfiles.type=\"edgegraphics\"/>",
    "  <graph id=\"G\" edgedefault=\"directed\">"
  ]

  let mut nodeIndex : Nat := 0

  for g in groups do
    let members := retainedMembersOfGroup retained g
    let interfaces := retainedInterfacesOfGroup retained g
    let direct := groupDirectDeps env allowed retained g
    let reduced := transitiveReducedGroupDeps env allowed retained g
    let status := groupLogicalStatus g
    let membersS := String.intercalate "; " (members.map shortNameString)
    let interfacesS := String.intercalate "; " (interfaces.map shortNameString)
    let directS := String.intercalate "; " direct
    let reducedS := String.intercalate "; " reduced

    csvLines := csvLines.push <|
      String.intercalate "," [
        csv g.id, csv g.label, csv status, csv membersS, csv interfacesS,
        csv directS, csv reducedS
      ]

    mdLines := mdLines.push <|
      "| **" ++ g.label ++ "** | " ++ status ++ " | " ++ membersS ++
      " | " ++ interfacesS ++ " | " ++ directS ++ " | " ++ reducedS ++ " |"

    let nodeId := "g" ++ toString nodeIndex
    graphmlLines := graphmlLines.push <|
      "    <node id=\"" ++ nodeId ++ "\"><data key=\"d0\">" ++
      xmlEscape g.id ++ "</data><data key=\"d1\">" ++
      xmlEscape g.label ++ "</data><data key=\"d2\">" ++
      xmlEscape status ++ "</data><data key=\"d3\">" ++
      xmlEscape membersS ++ "</data><data key=\"d4\"><y:ShapeNode><y:NodeLabel>" ++
      xmlEscape g.label ++ "</y:NodeLabel><y:Shape type=\"" ++
      groupShape g ++ "\"/></y:ShapeNode></data></node>"

    nodeIndex := nodeIndex + 1

  let mut edgeIndex : Nat := 0
  for dependentGroup in groups do
    if let some dependentId := groupNodeId? groups dependentGroup.id then
      for dependencyString in
          transitiveReducedGroupDeps env allowed retained dependentGroup do
        if let some dependencyId := groupNodeId? groups dependencyString then
          graphmlLines := graphmlLines.push <|
            "    <edge id=\"ge" ++ toString edgeIndex ++
            "\" source=\"" ++ dependencyId ++ "\" target=\"" ++ dependentId ++
            "\"><data key=\"d5\"><y:PolyLineEdge><y:Arrows source=\"none\" target=\"standard\"/></y:PolyLineEdge></data></edge>"
          edgeIndex := edgeIndex + 1

  graphmlLines := graphmlLines.push "  </graph>"
  graphmlLines := graphmlLines.push "</graphml>"

  return (String.intercalate "\n" csvLines.toList ++ "\n",
          String.intercalate "\n" mdLines.toList ++ "\n",
          String.intercalate "\n" graphmlLines.toList ++ "\n")


def generateUpstreamBoundaryReports
    (env : Environment) : String × String := Id.run do
  let grAllowed := reportableProjectDeclSet env
  let retained := spineDeclSet grAllowed
  let upstream := reportableUpstreamDeclSet env

  let mut csvLines : Array String := #[
    "gr_declaration,direct_upstream_declaration,upstream_module,upstream_kind"
  ]

  let mut mdLines : Array String := #[
    "# GR / SBI-Time direct formal boundary",
    "",
    "Each row records a direct checked dependency from a retained GR manuscript-spine declaration to a user-facing declaration in the imported SBI or Time formalization.",
    "",
    "No transitive axiom ancestry is inferred in this first boundary view.",
    "",
    "| GR declaration | Direct upstream declaration | Upstream module | Kind |",
    "|---|---|---|---|"
  ]

  for g in retained.toList do
    let deps := directDeps env upstream g
    for u in deps.toList do
      let modName :=
        match moduleNameOf? env u with
        | some m => toString m
        | none => "<unknown>"
      let k :=
        match env.find? u with
        | some ci => kindString ci
        | none => "<unknown>"

      csvLines := csvLines.push <|
        String.intercalate "," [
          csv (toString g), csv (toString u), csv modName, csv k
        ]

      mdLines := mdLines.push <|
        "| `" ++ toString g ++ "` | `" ++ toString u ++ "` | `" ++
        modName ++ "` | " ++ k ++ " |"

  return (String.intercalate "\n" csvLines.toList ++ "\n",
          String.intercalate "\n" mdLines.toList ++ "\n")


syntax (name := grDependencyReportCmd) "#gr_dependency_report" : command

@[command_elab grDependencyReportCmd]
def elabGRDependencyReport : CommandElab := fun _ => do
  let env ← getEnv

  let (auditCsv, auditMd, auditDot, auditGraphml) :=
    generateAuditReports env
  let (mapCsv, mapMd, mapGraphml) :=
    generateManuscriptMapReports env
  let (groupCsv, groupMd, groupGraphml) :=
    generateGroupedReports env
  let (boundaryCsv, boundaryMd) :=
    generateUpstreamBoundaryReports env

  liftIO <| IO.FS.writeFile "gr-dependencies.csv" auditCsv
  liftIO <| IO.FS.writeFile "gr-dependencies.md" auditMd
  liftIO <| IO.FS.writeFile "gr-dependencies.dot" auditDot
  liftIO <| IO.FS.writeFile "gr-dependencies.graphml" auditGraphml

  liftIO <| IO.FS.writeFile "gr-manuscript-map.csv" mapCsv
  liftIO <| IO.FS.writeFile "gr-manuscript-map.md" mapMd
  liftIO <| IO.FS.writeFile "gr-manuscript-map.graphml" mapGraphml

  liftIO <| IO.FS.writeFile "gr-grouped-map.csv" groupCsv
  liftIO <| IO.FS.writeFile "gr-grouped-map.md" groupMd
  liftIO <| IO.FS.writeFile "gr-grouped-map.graphml" groupGraphml

  liftIO <| IO.FS.writeFile "gr-upstream-boundary.csv" boundaryCsv
  liftIO <| IO.FS.writeFile "gr-upstream-boundary.md" boundaryMd

  let allowed := reportableProjectDeclSet env
  let retained := spineDeclSet allowed
  let names := retained.toList
  let nAudit := allowed.toList.length
  let nSpine := names.length
  let nPrincipalEdges :=
    countRetainedEdges names fun n =>
      collapsedFrontierDeps env allowed retained n
  let nReducedEdges :=
    countRetainedEdges names fun n =>
      transitiveReducedSpineDeps env allowed retained n
  let groups := presentGroups retained
  let nGroupEdges :=
    groups.foldl
      (fun total g =>
        total + (transitiveReducedGroupDeps env allowed retained g).length)
      0

  -- Prevent silent drift between the checked spine and human grouping.
  for n in names do
    let count := groupMembershipCount n
    if count == 0 then
      logWarning m!"Ungrouped GR manuscript-spine declaration: {n}"
    else if count > 1 then
      logWarning m!"GR declaration belongs to more than one manuscript group: {n}"

  for g in groups do
    if (retainedInterfacesOfGroup retained g).isEmpty then
      logWarning m!"GR manuscript group has no retained interface declaration: {g.label}"

  -- Quotienting a declaration DAG can expose a conceptual grouping cycle.
  -- Such a warning means the grouping does not represent a clean proof-stage
  -- decomposition and should be inspected rather than hidden by layout.
  for g in groups do
    let hasCycle :=
      (groupDirectDeps env allowed retained g).any fun dependencyId =>
        groupReachable env allowed retained dependencyId g.id
    if hasCycle then
      logWarning m!"GR conceptual grouping produces a cycle involving: {g.label}"

  logInfo m!"GR dependency reports written: {nAudit} audit declarations, {nSpine} manuscript-spine declarations, {nPrincipalEdges} collapsed principal edges, {nReducedEdges} reduced manuscript edges, {groups.length} conceptual groups, {nGroupEdges} reduced group edges.\n  gr-dependencies.csv\n  gr-dependencies.md\n  gr-dependencies.dot\n  gr-dependencies.graphml\n  gr-manuscript-map.csv\n  gr-manuscript-map.md\n  gr-manuscript-map.graphml\n  gr-grouped-map.csv\n  gr-grouped-map.md\n  gr-grouped-map.graphml\n  gr-upstream-boundary.csv\n  gr-upstream-boundary.md"

end GRDependencyReport

#gr_dependency_report
