import SBILeanProject.GR.DependencyReport
import Lean.Elab.Command

set_option autoImplicit false

open Lean Elab Command

namespace GRRefinedGroupedReport

open GRDependencyReport

/-!
Refined human-facing grouped proof map for the GR manuscript.

`GR.DependencyReport` remains the forensic/declaration-level audit.  This file
regenerates only `gr-grouped-map.*` with a grouping that follows the manuscript
logic more closely while preserving machine-derived dependency edges.

Three points are enforced here:

  * structural Newton I remains a Section-2 kinematical result but is not a
    premise of the Section-3 Lorentzian-manifold construction;
  * GR-side structural premises for Lovelock are separated from the imported
    Lovelock theorem and from the bridge identifying the two vocabularies;
  * the reachability conclusion is labelled only by what is formally proved,
    leaving its domain-of-validity interpretation to the manuscript prose.
-/

structure RefinedGroup where
  id : String
  label : String
  members : List String
  interfaces : List String
  logicalStatus : String
  shape : String


def refinedGroups : List RefinedGroup := [
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
    logicalStatus := "Derived result"
    shape := "roundrectangle"
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
    logicalStatus := "Physical/effective bridge"
    shape := "hexagon"
  },
  {
    id := "reachability-domain"
    label := "Constraint-strengthened and limiting reachability"
    members := [
      "SBI.GR.constraintStrengthening_characterization",
      "SBI.GR.limitingReachability_characterization"
    ]
    interfaces := [
      "SBI.GR.constraintStrengthening_characterization",
      "SBI.GR.limitingReachability_characterization"
    ]
    logicalStatus := "Derived result"
    shape := "roundrectangle"
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
    logicalStatus := "Derived result"
    shape := "roundrectangle"
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
    logicalStatus := "Physical/effective bridge"
    shape := "hexagon"
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
    logicalStatus := "Physical/effective bridge"
    shape := "hexagon"
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
    logicalStatus := "External mathematics"
    shape := "ellipse"
  },
  {
    id := "kinematics-conclusion"
    label := "Spacetime kinematics"
    members := [
      "SBI.GR.SpacetimeKinematicsResult",
      "SBI.GR.spacetimeKinematics_characterization"
    ]
    interfaces := ["SBI.GR.spacetimeKinematics_characterization"]
    logicalStatus := "Derived result"
    shape := "roundrectangle"
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
    logicalStatus := "Physical/effective bridge"
    shape := "hexagon"
  },
  {
    id := "lorentzian-geometry"
    label := "Lorentz result to Lorentzian effective geometry"
    members := [
      "SBI.GR.LorentzianGeometryBridge",
      "SBI.GR.lorentzianCausalStructure_of_lorentzResult",
      "SBI.GR.lorentzianCausalStructure_of_standardClassification",
      "SBI.GR.effectiveGeometry_bridge_and_coordinateInvariance"
    ]
    interfaces := [
      "SBI.GR.lorentzianCausalStructure_of_standardClassification",
      "SBI.GR.effectiveGeometry_bridge_and_coordinateInvariance"
    ]
    logicalStatus := "Physical/effective bridge"
    shape := "hexagon"
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
    logicalStatus := "Derived result"
    shape := "roundrectangle"
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
    logicalStatus := "Physical/effective bridge"
    shape := "hexagon"
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
    logicalStatus := "Physical/effective bridge"
    shape := "hexagon"
  },
  {
    id := "lovelock-premises"
    label := "GR structural premises for Lovelock"
    members := [
      "SBI.GR.EffectiveLovelockRegimeBridge",
      "SBI.GR.EffectiveLovelockPremises",
      "SBI.GR.effectiveLovelockPremises_of_closedEffectiveRegime"
    ]
    interfaces := [
      "SBI.GR.effectiveLovelockPremises_of_closedEffectiveRegime"
    ]
    logicalStatus := "Physical/effective bridge"
    shape := "hexagon"
  },
  {
    id := "lovelock-interface"
    label := "Imported Lovelock theorem interface"
    members := [
      "SBI.GR.StandardLovelockClassification"
    ]
    interfaces := ["SBI.GR.StandardLovelockClassification"]
    logicalStatus := "External mathematics"
    shape := "ellipse"
  },
  {
    id := "lovelock-input"
    label := "Identification with Lovelock hypotheses"
    members := [
      "SBI.GR.LovelockClassificationInput",
      "SBI.GR.LovelockRegimeBridge",
      "SBI.GR.lovelockInput_of_effectivePremises"
    ]
    interfaces := ["SBI.GR.lovelockInput_of_effectivePremises"]
    logicalStatus := "Physical/effective bridge"
    shape := "hexagon"
  },
  {
    id := "lovelock-result"
    label := "Lovelock geometric classification result"
    members := [
      "SBI.GR.einsteinPlusCosmological_of_standardLovelock"
    ]
    interfaces := ["SBI.GR.einsteinPlusCosmological_of_standardLovelock"]
    logicalStatus := "Derived result"
    shape := "roundrectangle"
  },
  {
    id := "einstein-synthesis"
    label := "Einstein-form geometry/source coupling"
    members := [
      "SBI.GR.EffectiveEinsteinCoupling",
      "SBI.GR.admissibleCoarseGrainedGeometry_has_EinsteinForm"
    ]
    interfaces := ["SBI.GR.admissibleCoarseGrainedGeometry_has_EinsteinForm"]
    logicalStatus := "Physical/effective bridge"
    shape := "hexagon"
  },
  {
    id := "effective-gr-conclusion"
    label := "Effective GR characterization"
    members := ["SBI.GR.effectiveGR_characterization"]
    interfaces := ["SBI.GR.effectiveGR_characterization"]
    logicalStatus := "Derived result"
    shape := "roundrectangle"
  }
]


def groupContains (g : RefinedGroup) (n : Name) : Bool :=
  g.members.contains (toString n)


def groupOf? (n : Name) : Option RefinedGroup :=
  refinedGroups.find? fun g => groupContains g n


def retainedMembersOfGroup
    (allowed : NameSet)
    (g : RefinedGroup) : List Name :=
  allowed.toList.filter fun n => groupContains g n


def retainedInterfacesOfGroup
    (allowed : NameSet)
    (g : RefinedGroup) : List Name :=
  (retainedMembersOfGroup allowed g).filter fun n =>
    g.interfaces.contains (toString n)


def presentGroups (allowed : NameSet) : List RefinedGroup :=
  refinedGroups.filter fun g =>
    !(retainedMembersOfGroup allowed g).isEmpty


def appendUniqueString (xs : List String) (s : String) : List String :=
  if xs.contains s then xs else xs ++ [s]


partial def groupFrontierLoop
    (env : Environment)
    (allowed : NameSet)
    (currentGroupId : String)
    (todo : List Name)
    (seen : NameSet)
    (out : List String) : List String :=
  match todo with
  | [] => out
  | n :: rest =>
      if seen.contains n then
        groupFrontierLoop env allowed currentGroupId rest seen out
      else
        let seen' := seen.insert n
        match groupOf? n with
        | none =>
            groupFrontierLoop env allowed currentGroupId
              ((directDeps env allowed n).toList ++ rest)
              seen' out
        | some dg =>
            if dg.id == currentGroupId then
              groupFrontierLoop env allowed currentGroupId
                ((directDeps env allowed n).toList ++ rest)
                seen' out
            else
              groupFrontierLoop env allowed currentGroupId rest seen'
                (appendUniqueString out dg.id)


def groupDirectDeps
    (env : Environment)
    (allowed : NameSet)
    (g : RefinedGroup) : List String := Id.run do
  let mut start : List Name := []
  for n in retainedInterfacesOfGroup allowed g do
    start := (directDeps env allowed n).toList ++ start
  return groupFrontierLoop env allowed g.id start {} []


def groupById? (id : String) : Option RefinedGroup :=
  refinedGroups.find? fun g => g.id == id


partial def groupReachableLoop
    (env : Environment)
    (allowed : NameSet)
    (target : String)
    (todo seen : List String) : Bool :=
  match todo with
  | [] => false
  | current :: rest =>
      if current == target then true
      else if seen.contains current then
        groupReachableLoop env allowed target rest seen
      else
        let seen' := current :: seen
        match groupById? current with
        | none =>
            groupReachableLoop env allowed target rest seen'
        | some g =>
            groupReachableLoop env allowed target
              (groupDirectDeps env allowed g ++ rest) seen'


def groupReachable
    (env : Environment)
    (allowed : NameSet)
    (start target : String) : Bool :=
  groupReachableLoop env allowed target [start] []


def transitiveReducedGroupDeps
    (env : Environment)
    (allowed : NameSet)
    (g : RefinedGroup) : List String :=
  let deps := groupDirectDeps env allowed g
  deps.filter fun d =>
    !(deps.any fun alt =>
      (!(alt == d)) && groupReachable env allowed alt d)


def groupIndexAux
    (target : String) : List RefinedGroup → Nat → Option Nat
  | [], _ => none
  | g :: gs, i =>
      if g.id == target then some i else groupIndexAux target gs (i + 1)


def groupNodeId?
    (groups : List RefinedGroup)
    (id : String) : Option String := do
  let i ← groupIndexAux id groups 0
  return "g" ++ toString i


def generateRefinedGroupedReports
    (env : Environment) : String × String × String := Id.run do
  let allowed := reportableProjectDeclSet env
  let groups := presentGroups allowed

  let mut csvLines : Array String := #[
    "group_id,label,logical_status,lean_members,interface_declarations,direct_group_dependencies,reduced_group_dependencies"
  ]

  let mut mdLines : Array String := #[
    "# GR grouped manuscript proof map",
    "",
    "Principal human-facing proof architecture. Group membership is manuscript traceability; every edge between groups is derived from checked Lean declaration dependencies.",
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
    let members := retainedMembersOfGroup allowed g
    let interfaces := retainedInterfacesOfGroup allowed g
    let direct := groupDirectDeps env allowed g
    let reduced := transitiveReducedGroupDeps env allowed g
    let membersS := String.intercalate "; " (members.map shortNameString)
    let interfacesS := String.intercalate "; " (interfaces.map shortNameString)
    let directS := String.intercalate "; " direct
    let reducedS := String.intercalate "; " reduced

    csvLines := csvLines.push <|
      String.intercalate "," [
        csv g.id, csv g.label, csv g.logicalStatus, csv membersS,
        csv interfacesS, csv directS, csv reducedS
      ]

    mdLines := mdLines.push <|
      "| **" ++ g.label ++ "** | " ++ g.logicalStatus ++ " | " ++
      membersS ++ " | " ++ interfacesS ++ " | " ++ directS ++ " | " ++
      reducedS ++ " |"

    let nodeId := "g" ++ toString nodeIndex
    graphmlLines := graphmlLines.push <|
      "    <node id=\"" ++ nodeId ++ "\"><data key=\"d0\">" ++
      xmlEscape g.id ++ "</data><data key=\"d1\">" ++
      xmlEscape g.label ++ "</data><data key=\"d2\">" ++
      xmlEscape g.logicalStatus ++ "</data><data key=\"d3\">" ++
      xmlEscape membersS ++ "</data><data key=\"d4\"><y:ShapeNode><y:NodeLabel>" ++
      xmlEscape g.label ++ "</y:NodeLabel><y:Shape type=\"" ++
      g.shape ++ "\"/></y:ShapeNode></data></node>"

    nodeIndex := nodeIndex + 1

  let mut edgeIndex : Nat := 0
  for dependentGroup in groups do
    if let some dependentId := groupNodeId? groups dependentGroup.id then
      for dependencyString in
          transitiveReducedGroupDeps env allowed dependentGroup do
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


syntax (name := refinedGRGroupedReportCmd) "#refined_gr_grouped_report" : command

@[command_elab refinedGRGroupedReportCmd]
def elabRefinedGRGroupedReport : CommandElab := fun _ => do
  let env ← getEnv
  let (groupCsv, groupMd, groupGraphml) := generateRefinedGroupedReports env

  liftIO <| IO.FS.writeFile "gr-grouped-map.csv" groupCsv
  liftIO <| IO.FS.writeFile "gr-grouped-map.md" groupMd
  liftIO <| IO.FS.writeFile "gr-grouped-map.graphml" groupGraphml

  let allowed := reportableProjectDeclSet env
  let groups := presentGroups allowed
  let nGroupEdges :=
    groups.foldl
      (fun total g =>
        total + (transitiveReducedGroupDeps env allowed g).length)
      0

  for g in groups do
    if (retainedInterfacesOfGroup allowed g).isEmpty then
      logWarning m!"Refined GR manuscript group has no retained interface declaration: {g.label}"

  for g in groups do
    let hasCycle :=
      (groupDirectDeps env allowed g).any fun dependencyId =>
        groupReachable env allowed dependencyId g.id
    if hasCycle then
      logWarning m!"Refined GR conceptual grouping produces a cycle involving: {g.label}"

  logInfo m!"Refined GR grouped report written: {groups.length} conceptual groups, {nGroupEdges} reduced group edges."

end GRRefinedGroupedReport

#refined_gr_grouped_report
