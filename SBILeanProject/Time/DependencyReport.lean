import SBILeanProject.Time
import Lean
import Lean.Elab.Command
import Lean.Util.FoldConsts

set_option autoImplicit false

open Lean Elab Command

namespace TimeDependencyReport

/--
All imported modules below this prefix are treated as part of the Time project.
Because `DependencyReport.lean` imports the Time entry module, this picks up
the complete current set of imported Time formalization modules.
-/
def projectModulePrefix : Name := `SBILeanProject.Time

/--
Suppress kernel-generated constructors, recursors and quotient machinery from
report rows. User-facing definitions, theorems, axioms, opaque declarations,
inductive/structure names and structure projections are retained.
-/
def keepKind : ConstantKind → Bool
  | .ctor     => false
  | .recursor => false
  | .quot     => false
  | _         => true

/-- True for a user-facing declaration that should appear in the report. -/
def isReportableDecl (env : Environment) (n : Name) : Bool :=
  if n.isInternal then
    false
  else
    match env.find? n with
    | none    => false
    | some ci => keepKind (ConstantKind.ofConstantInfo ci)

/--
Collect every declaration belonging to imported modules whose module name lies
below `SBILeanProject.Time`.
-/
def projectDeclSet (env : Environment) : NameSet := Id.run do
  let mut out : NameSet := {}

  for modName in env.header.moduleNames do
    if projectModulePrefix.isPrefixOf modName then
      if let some idx := env.getModuleIdx? modName then
        let i := idx.toNat
        if h : i < env.header.moduleData.size then
          let modData := env.header.moduleData[i]'h
          for n in modData.constNames do
            out := out.insert n

  return out

/-- User-facing Time declarations only. -/
def reportableProjectDeclSet (env : Environment) : NameSet :=
  (projectDeclSet env).filter (isReportableDecl env)

/--
Constants used by a declaration, treating constructor signatures as part of
the logical content of an inductive or structure declaration.

This is important for dependency reporting because hypotheses occurring only
in inductive constructors would otherwise disappear when constructor
declarations are suppressed from the user-facing graph.
-/
def usedConstantsIncludingConstructors
    (env : Environment)
    (n : Name) : NameSet :=

  match env.find? n with
  | none =>
      {}

  | some ci =>
      let own := ci.getUsedConstantsAsSet

      match ci with
      | .inductInfo info =>
          info.ctors.foldl
            (fun acc ctorName =>
              match env.find? ctorName with
              | none =>
                  acc
              | some ctorInfo =>
                  ctorInfo.getUsedConstantsAsSet.toList.foldl
                    (fun s d => s.insert d)
                    acc)
            own

      | _ =>
          own
/--
Direct kernel-level dependencies of `n`, restricted to user-facing Time
project declarations. Both the declaration's type and its checked body/proof
are inspected.
-/
/-
Direct kernel-level dependencies of `n`, restricted to user-facing Time
project declarations.

For inductive and structure declarations, constructor signatures are included
as part of the declaration's logical dependency content.
-/
def directDeps
    (env : Environment)
    (allowed : NameSet)
    (n : Name) : NameSet :=

  (usedConstantsIncludingConstructors env n).filter fun d =>
    (!(d == n)) && allowed.contains d

/-- DFS used for the transitive project dependency closure. -/
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
        let more  := (directDeps env allowed n).toList
        transitiveLoop env allowed (more ++ rest) seen'

/-- All project declarations on which `n` depends transitively. -/
def transitiveDeps (env : Environment) (allowed : NameSet) (n : Name) : NameSet :=
  let start := (directDeps env allowed n).toList
  let closure := transitiveLoop env allowed start {}
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

/-- Quote a CSV field. -/
def csv (s : String) : String :=
  "\"" ++ s.replace "\"" "\"\"" ++ "\""

/-- Render a NameSet as a stable semicolon-separated list. -/
def renderNames (s : NameSet) : String :=
  String.intercalate "; " (s.toList.map toString)

/-- Escape a declaration name for use as a Graphviz quoted string. -/
def dotQuote (s : String) : String :=
  "\"" ++ ((s.replace "\\" "\\\\").replace "\"" "\\\"") ++ "\""

/-- Escape text for XML/GraphML element content. -/
def xmlEscape (s : String) : String :=
  ((((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;").replace "\"" "&quot;").replace "'" "&apos;"

/-- Short final component of a Lean declaration name, for compact yEd labels. -/
def shortNameString : Name → String
  | .anonymous => "<anonymous>"
  | .str _ s   => s
  | .num _ i   => toString i

/-- Find the zero-based position of a declaration name in a list. -/
def nameIndexAux (target : Name) : List Name → Nat → Option Nat
  | [], _ => none
  | n :: ns, i =>
      if n == target then
        some i
      else
        nameIndexAux target ns (i + 1)

/-- Stable numeric GraphML node id for a declaration in `names`. -/
def graphmlNodeId? (names : List Name) (n : Name) : Option String := do
  let i ← nameIndexAux n names 0
  return "n" ++ toString i



/--
Names retained in the reduced manuscript-level logical spine.

Unlike the earlier SBI report, the Time report uses fully qualified declaration
names in this list and in conceptual groups.  This avoids collisions between
distinct declarations that share a final component.

The raw audit is intentionally restricted to declarations in
`SBILeanProject.Time.*`.  The already verified SBI development is therefore
an imported formal boundary rather than being duplicated inside this report.

The full report remains exhaustive.  The spine intentionally keeps only
axioms, manuscript-facing definitions/results, and the semantic bridge
declarations that carry logical content between them.

In particular, the reduced spine shows finite operational accessibility
through the theorem `finite_operational_accessibility`, not through the raw
definition `FOA`.  The latter merely names the proposition being proved.

The manuscript map also normalizes the structure projection
`accessible_has_establishment`.  Without this normalization, collapsing through
the omitted `NetworkContext` constructor makes that projection inherit A2 from
sibling fields of the structure.  That would incorrectly make operational
accessibility look derived from A2.

With the normalization, the intended checked structure is visible:
operational accessibility supplies finite establishment, while A2 supplies
finite operational participation and alternatives.  Both enter
`finite_operational_accessibility`.

Declarations used only as internal implementation details are omitted when
they do not clarify the manuscript-level logical structure.

Edit this list if the manuscript vocabulary changes; absent names are simply
ignored.
-/
def spineShortNames : List String := [
  -- Operational accessibility and reachability
  "SBI.Time.OperationalAccessibilitySemantics",
  "SBI.Time.OperationalReachability",
  "SBI.Time.operationalReachability_is_admissibleDeformation",

  -- Reversible equivalence classes and asymmetric reachability
  "SBI.Time.ReversibleEquivalent",
  "SBI.Time.ReversibleClass",
  "SBI.Time.reversibleClassOf",
  "SBI.Time.AsymmetricReachability",
  "SBI.Time.asymmetricReachability_not_reversibleEquivalent",
  "SBI.Time.asymmetricReachability_trans",

  -- Irreversible precedence and ordered histories
  "SBI.Time.IrreversiblePrecedence",
  "SBI.Time.irreversiblePrecedence_irrefl",
  "SBI.Time.irreversiblePrecedence_trans",
  "SBI.Time.irreversiblePrecedence_strictPartialOrder",
  "SBI.Time.OrderedPhysicalHistory",
  "SBI.Time.HistoryAtMostCountable",
  "SBI.Time.HistoryPrecedence",
  "SBI.Time.historyPrecedence_isStrictTotalOrder",
  "SBI.Time.history_orderEmbedsIntoReal",
  "SBI.Time.strictMono_reparametrization_preserves_temporalOrder",
  "SBI.Time.temporalOrder_characterization",

  -- Record semantics
  "SBI.Time.OperationallyReconstructible",
  "SBI.Time.OperationallyIrreversible",
  "SBI.Time.operationallyIrreversible_iff_asymmetricReachability",
  "SBI.Time.RecordFeatureSemantics",
  "SBI.Time.PersistentRecord",
  "SBI.Time.PersistentRecord.operationallyIrreversible",
  "SBI.Time.PersistentRecord.elimination_not_reachable",
  "SBI.Time.PersistentRecord.asymmetricReachability",
  "SBI.Time.PersistentRecord.irreversiblePrecedence",

  -- Local record obstruction and propagation
  "SBI.Time.LocalRecordFormationSemantics",
  "SBI.Time.LocalReconstructionSet",
  "SBI.Time.PersistenceCompatibleSet",
  "SBI.Time.LocalReconstructionPersistenceIncompatible",
  "SBI.Time.local_reconstruction_obstruction",
  "SBI.Time.RelationalDomainSemantics",
  "SBI.Time.RelationallyAdjacent",
  "SBI.Time.RelationalIncidenceChain",
  "SBI.Time.RelationalPropagationDepth",
  "SBI.Time.RelationalPropagationDepthToDomain",
  "SBI.Time.RelationalShell",
  "SBI.Time.LimitingPropagationFront",
  "SBI.Time.WithinRelationalDepth",
  "SBI.Time.LocallyMediatedReconstructionPropagation",
  "SBI.Time.LocallyMediatedReconstructionPropagation.support_within_bound",
  "SBI.Time.reconstruction_lag_remains_strict",
  "SBI.Time.LocallyMediatedReconstructionPropagation.cannot_overtake_limiting_front",
  "SBI.Time.LimitingDependencyPropagation",
  "SBI.Time.LocallyMediatedReconstructionPropagation.disjoint_from_limiting_dependency",
  "SBI.Time.ReconstructionRequiresDependencyRecovery",
  "SBI.Time.ReconstructionRequiresDependencyRecovery.not_operationally_reconstructible",
  "SBI.Time.persistentRecord_of_limiting_dependency",
  "SBI.Time.persistentRecord_consequences",

  -- Reversible exploration and operational duration
  "SBI.Time.AccessibleRearrangementPath",
  "SBI.Time.accessibleRearrangementPath_is_operationalReachability",
  "SBI.Time.ReversibleRearrangementPath",
  "SBI.Time.ReversibleRearrangementPath.pathLength",
  "SBI.Time.ReversibleRearrangementPath.pathLength_append",
  "SBI.Time.ReversibleRearrangementPath.pathLength_reverse",
  "SBI.Time.ReversibleRearrangementPath.is_operationalReachability",
  "SBI.Time.ReversibleRearrangementPath.endpoints_reversibleEquivalent",
  "SBI.Time.ReversibleRearrangementPath.same_reversibleClass",
  "SBI.Time.OperationalDurationParameter",
  "SBI.Time.OperationalClock",
  "SBI.Time.LocalDurationScale",
  "SBI.Time.ReversibleRearrangementPath.accumulatedDuration",
  "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_eq_zero_iff_pathLength_eq_zero",
  "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_append",
  "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_reverse",
  "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_lt_of_pathLength_lt",
  "SBI.Time.reversibleDuration_characterization",
  "SBI.Time.ReversibleCycle",
  "SBI.Time.ReversibleClock",
  "SBI.Time.ReversibleClock.tickDuration",
  "SBI.Time.ReversibleClock.tickDuration_pos",
  "SBI.Time.ReversibleCycle.accumulatedDuration_iterate",
  "SBI.Time.ReversibleClock.durationAfterCycles",
  "SBI.Time.ReversibleClock.durationAfterCycles_strictMono",
  "SBI.Time.ReversibleClock.toOperationalClock",

  -- Nonnegative physical-duration evolution
  "SBI.Time.PhysicalDuration",
  "SBI.Time.ReversibleRearrangementPath.physicalDuration",
  "SBI.Time.physicalDuration_characterization",
  "SBI.Time.AutonomousPhysicalDurationEvolution",
  "SBI.Time.AutonomousPhysicalDurationEvolution.evolve_from_reached_state",
  "SBI.Time.ContinuousAutonomousPhysicalDurationEvolution",
  "SBI.Time.RightDifferentiableAutonomousPhysicalDurationEvolution",
  "SBI.Time.RightDifferentiableAutonomousPhysicalDurationEvolution.hasDerivWithinAt_generator",
  "SBI.Time.RightDifferentiableAutonomousPhysicalDurationEvolution.hasDerivWithinAt_incremented_duration",
  "SBI.Time.RightDifferentiableAutonomousPhysicalDurationEvolution.derivWithin_incremented_duration",
  "SBI.Time.physicalDurationGenerator_characterization",
  "SBI.Time.ReversibleAutonomousPhysicalDurationEvolution",
  "SBI.Time.ReversibleAutonomousPhysicalDurationEvolution.inverse_after_evolve",
  "SBI.Time.ReversibleAutonomousPhysicalDurationEvolution.evolve_after_inverse",
  "SBI.Time.reversiblePhysicalDurationEvolution_characterization",

]

/-- Declarations retained in the reduced logical-spine graph. -/
def spineDeclSet (allowed : NameSet) : NameSet :=
  allowed.filter fun n =>
    spineShortNames.any fun s => s == toString n


/--
Terminal declarations retained in the full logical-spine audit but omitted
from the manuscript-facing presentation map.

These are useful machine-checked support results, but they are not independent
conceptual destinations of the Time argument. Suppression affects only the
presentation-level manuscript map: the declarations remain in the Lean
development, raw dependency report, and logical-spine report.

PersistentRecord.elimination_not_reachable is deliberately NOT suppressed.
Although terminal, it states a physically meaningful consequence of record
persistence rather than merely an implementation check.
-/
def manuscriptMapSuppressedNames : List String := [
  "SBI.Time.operationalReachability_is_admissibleDeformation",
  "SBI.Time.asymmetricReachability_not_reversibleEquivalent",
  "SBI.Time.strictMono_reparametrization_preserves_temporalOrder",
  "SBI.Time.accessibleRearrangementPath_is_operationalReachability",
  "SBI.Time.ReversibleRearrangementPath.same_reversibleClass",
  "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_eq_zero_iff_pathLength_eq_zero",
  "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_lt_of_pathLength_lt",
  "SBI.Time.reconstruction_lag_remains_strict"
]

/-- Declarations shown in the manuscript-facing presentation map. -/
def manuscriptMapNames (retained : NameSet) : List Name :=
  retained.toList.filter fun n =>
    !(manuscriptMapSuppressedNames.contains (toString n))


/-
===============================================================================
MANUSCRIPT LOGICAL STATUS
===============================================================================

The declaration-level manuscript maps distinguish four logical roles used in
the Time text:

  * Definition          -- introduces formal vocabulary or a named structure.
  * Derived result      -- a theorem proved from preceding formal material.
  * Physical condition  -- an additional condition selecting the physical
                           cases to which a later derived result applies.
  * Effective assumption -- an additional coarse-grained dynamical property,
                            such as autonomy, continuity or differentiability.

The classification is a manuscript/traceability annotation, not part of the
Lean proof.  Dependency edges remain entirely machine-derived.

Most declarations can be classified from their Lean kind: theorems are
derived results and non-theorem declarations are definitions.  The explicit
lists below contain the important exceptions where a definition/structure
packages substantive physical or effective conditions rather than merely
introducing vocabulary.
-/

/--
Named conditions that are supplied for a class of physical situations rather
than derived universally from the preceding Time development.

In particular, these nodes do NOT assert that every interaction satisfies the
condition.  They identify the cases to which the corresponding conditional
theorems apply.
-/
def physicalConditionNames : List String := [
  "SBI.Time.HistoryAtMostCountable",
  "SBI.Time.LocalReconstructionPersistenceIncompatible",
  "SBI.Time.LocallyMediatedReconstructionPropagation",
  "SBI.Time.LimitingDependencyPropagation",
  "SBI.Time.ReconstructionRequiresDependencyRecovery",
  "SBI.Time.LocalDurationScale"
]

/--
Coarse-grained dynamical properties introduced only at the effective-theory
level.  These are deliberately not presented as consequences of A1--A3 or of
the discrete operational-duration construction.
-/
def effectiveAssumptionNames : List String := [
  "SBI.Time.AutonomousPhysicalDurationEvolution",
  "SBI.Time.ContinuousAutonomousPhysicalDurationEvolution",
  "SBI.Time.RightDifferentiableAutonomousPhysicalDurationEvolution",
  "SBI.Time.ReversibleAutonomousPhysicalDurationEvolution"
]

/-- Manuscript-facing logical status of one retained Time declaration. -/
def manuscriptLogicalStatus (env : Environment) (n : Name) : String :=
  let nS := toString n
  if physicalConditionNames.contains nS then
    "Physical condition"
  else if effectiveAssumptionNames.contains nS then
    "Effective assumption"
  else
    match env.find? n with
    | some ci =>
        match ConstantKind.ofConstantInfo ci with
        | .thm => "Derived result"
        | _    => "Definition"
    | none =>
        "Definition"

/--
yEd shape associated with the manuscript logical status.

Shape, rather than color, is the primary encoding so the map remains legible
in grayscale and when printed.

  rectangle       Definition
  roundrectangle  Derived result
  hexagon         Physical condition
  ellipse         Effective assumption
-/
def manuscriptLogicalShape (env : Environment) (n : Name) : String :=
  match manuscriptLogicalStatus env n with
  | "Derived result"       => "roundrectangle"
  | "Physical condition"   => "hexagon"
  | "Effective assumption" => "ellipse"
  | _                      => "rectangle"

/--
Traverse dependencies through suppressed implementation nodes until the next
retained logical-spine declaration is reached.  Retained nodes form a frontier:
we stop there rather than adding all deeper ancestors.
-/
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
          let more := (directDeps env allowed n).toList
          collapsedFrontierLoop env allowed retained (more ++ rest) seen' out

/--
Nearest retained dependencies of `n` after collapsing paths whose internal
nodes are omitted from the manuscript-level spine.
-/
def collapsedFrontierDeps
    (env : Environment)
    (allowed retained : NameSet)
    (n : Name) : NameSet :=
  let start := (directDeps env allowed n).toList
  let out := collapsedFrontierLoop env allowed retained start {} {}
  out.filter fun d => !(d == n)


/--
Declarations that act as semantic inputs in the manuscript-level map.

`accessible_has_establishment` is a field of `NetworkContext`.  At kernel
level its projection refers to the enclosing structure.  When that structure
is omitted from the reduced spine, blindly collapsing through the structure
constructor makes the projection appear to inherit dependencies from unrelated
fields of the same structure, including A2.

That is a graph-reduction artefact, not the intended logical statement.
For the manuscript map we therefore stop dependency traversal at this
projection and treat it as the operational-accessibility input that its type
expresses.

No dependency is added by hand here.  This normalization only prevents
dependencies of sibling structure fields from being attributed to the
projection during collapse.
-/
def manuscriptSemanticInputShortNames : List String := []

/-- True for a declaration treated as a semantic input in the reduced map. -/
def isManuscriptSemanticInput (n : Name) : Bool :=
  manuscriptSemanticInputShortNames.any fun s =>
    s == toString n

/--
Collapsed dependencies used by the manuscript-facing logical spine.

For ordinary declarations this is exactly `collapsedFrontierDeps`.  For a
semantic-input structure projection, traversal stops at the projection itself
rather than expanding the omitted parent structure and thereby importing
dependencies of sibling fields.
-/
def manuscriptSpineDeps
    (env : Environment)
    (allowed retained : NameSet)
    (n : Name) : NameSet :=
  if isManuscriptSemanticInput n then
    {}
  else
    collapsedFrontierDeps env allowed retained n

/--
Reachability in the retained logical-spine graph, following the dependency
orientation `dependent -> dependency`.

Only retained declarations are traversed.  Suppressed implementation nodes
have already been collapsed by `collapsedFrontierDeps`.
-/
partial def spineReachableLoop
    (env : Environment)
    (allowed retained : NameSet)
    (target : Name)
    (todo : List Name)
    (seen : NameSet) : Bool :=
  match todo with
  | [] => false
  | n :: rest =>
      if n == target then
        true
      else if seen.contains n then
        spineReachableLoop env allowed retained target rest seen
      else
        let seen' := seen.insert n
        let more := (manuscriptSpineDeps env allowed retained n).toList
        spineReachableLoop env allowed retained target (more ++ rest) seen'

/-- True when `target` is reachable from `start` in the retained spine. -/
def spineReachable
    (env : Environment)
    (allowed retained : NameSet)
    (start target : Name) : Bool :=
  spineReachableLoop env allowed retained target [start] {}

/--
Transitive reduction of the collapsed retained dependency relation.

For a retained declaration `n`, a direct retained dependency `d` is removed
when another direct retained dependency `alt` of `n` already reaches `d`
through the retained graph.  Since Lean declaration dependencies are acyclic,
this is the standard transitive reduction of the retained DAG.
-/
def transitiveReducedSpineDeps
    (env : Environment)
    (allowed retained : NameSet)
    (n : Name) : NameSet :=
  let deps := manuscriptSpineDeps env allowed retained n
  deps.filter fun d =>
    !(deps.toList.any fun alt =>
      (!(alt == d)) && spineReachable env allowed retained alt d)

/-- Count edges in a retained dependency graph supplied by `depsOf`. -/
def countRetainedEdges
    (names : List Name)
    (depsOf : Name → NameSet) : Nat :=
  names.foldl (fun total n => total + (depsOf n).toList.length) 0

/--
Generate four reports:

* CSV: direct and transitive dependencies in machine-friendly form.
* Markdown: the same information as an inspectable table.
* DOT: a direct-dependency graph for Graphviz.
* GraphML: a yEd-ready direct-dependency graph with declaration labels.

Graph edges point from each declaration to each of its direct project-local
kernel dependencies.
-/
def generateReports (env : Environment) : String × String × String × String := Id.run do
  let allowed := reportableProjectDeclSet env
  let names := allowed.toList

  let mut csvLines : Array String := #[
    "declaration,module,kind,direct_project_dependencies,transitive_project_dependencies"
  ]

  let mut mdLines : Array String := #[
    "# Time Lean dependency report",
    "",
    "Direct dependencies are constants occurring in the checked declaration type or body/proof, filtered to user-facing declarations in imported `SBILeanProject.Time.*` modules.",
    "",
    "| Declaration | Module | Kind | Direct Time dependencies | Transitive Time dependencies |",
    "|---|---|---|---|---|"
  ]

  let mut dotLines : Array String := #[
    "digraph Time_Dependencies {",
    "  rankdir=LR;",
    "  node [shape=box];"
  ]

  let mut graphmlLines : Array String := #[
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
    "<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\"",
    "         xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"",
    "         xmlns:y=\"http://www.yworks.com/xml/graphml\"",
    "         xsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns http://www.yworks.com/xml/schema/graphml/1.1/ygraphml.xsd\">",
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
      let trans  := transitiveDeps env allowed n
      let modName :=
        match moduleNameOf? env n with
        | some m => toString m
        | none   => "<unknown>"
      let k := kindString ci
      let directS := renderNames direct
      let transS  := renderNames trans
      let nS := toString n

      csvLines := csvLines.push <|
        String.intercalate "," [
          csv nS,
          csv modName,
          csv k,
          csv directS,
          csv transS
        ]

      mdLines := mdLines.push <|
        "| `" ++ nS ++ "` | `" ++ modName ++ "` | " ++ k ++
        " | " ++ directS ++ " | " ++ transS ++ " |"

      -- Emit a DOT node even when it has no project-local dependencies.
      dotLines := dotLines.push <|
        "  " ++ dotQuote nS ++ ";"

      for d in direct.toList do
        dotLines := dotLines.push <|
          "  " ++ dotQuote nS ++ " -> " ++ dotQuote (toString d) ++ ";"

      -- yEd/GraphML node.  The visible label is compact; full declaration,
      -- module and kernel kind are retained as node data.
      let nodeId := "n" ++ toString nodeIndex
      graphmlLines := graphmlLines.push <| "    <node id=\"" ++ nodeId ++ "\">"
      graphmlLines := graphmlLines.push <| "      <data key=\"d0\">" ++ xmlEscape nS ++ "</data>"
      graphmlLines := graphmlLines.push <| "      <data key=\"d1\">" ++ xmlEscape modName ++ "</data>"
      graphmlLines := graphmlLines.push <| "      <data key=\"d2\">" ++ xmlEscape k ++ "</data>"
      graphmlLines := graphmlLines.push <| "      <data key=\"d3\">"
      graphmlLines := graphmlLines.push <| "        <y:ShapeNode>"
      graphmlLines := graphmlLines.push <| "          <y:NodeLabel>" ++ xmlEscape (shortNameString n) ++ "</y:NodeLabel>"
      graphmlLines := graphmlLines.push <| "          <y:Shape type=\"rectangle\"/>"
      graphmlLines := graphmlLines.push <| "        </y:ShapeNode>"
      graphmlLines := graphmlLines.push <| "      </data>"
      graphmlLines := graphmlLines.push <| "    </node>"

      nodeIndex := nodeIndex + 1

  dotLines := dotLines.push "}"

  -- GraphML edges are emitted after all nodes so that yEd sees a clean node
  -- table first.  Edge direction matches the DOT report: declaration -> dependency.
  let mut edgeIndex : Nat := 0
  for n in names do
    if let some sourceId := graphmlNodeId? names n then
      for d in (directDeps env allowed n).toList do
        if let some targetId := graphmlNodeId? names d then
          graphmlLines := graphmlLines.push <|
            "    <edge id=\"e" ++ toString edgeIndex ++ "\" source=\"" ++
            sourceId ++ "\" target=\"" ++ targetId ++ "\">"
          graphmlLines := graphmlLines.push <| "      <data key=\"d4\">"
          graphmlLines := graphmlLines.push <| "        <y:PolyLineEdge>"
          graphmlLines := graphmlLines.push <| "          <y:Arrows source=\"none\" target=\"standard\"/>"
          graphmlLines := graphmlLines.push <| "        </y:PolyLineEdge>"
          graphmlLines := graphmlLines.push <| "      </data>"
          graphmlLines := graphmlLines.push <| "    </edge>"
          edgeIndex := edgeIndex + 1

  graphmlLines := graphmlLines.push "  </graph>"
  graphmlLines := graphmlLines.push "</graphml>"

  let csvText := String.intercalate "\n" csvLines.toList ++ "\n"
  let mdText  := String.intercalate "\n" mdLines.toList ++ "\n"
  let dotText := String.intercalate "\n" dotLines.toList ++ "\n"
  let graphmlText := String.intercalate "\n" graphmlLines.toList ++ "\n"

  return (csvText, mdText, dotText, graphmlText)


/--
Generate the reduced manuscript-level logical-spine reports.  Edges in the
GraphML are reversed relative to the audit graph so that logical flow runs
from dependency -> dependent theorem/definition.
-/
def generateSpineReports (env : Environment) : String × String × String := Id.run do
  let allowed := reportableProjectDeclSet env
  let retained := spineDeclSet allowed
  let names := retained.toList

  let mut csvLines : Array String := #[
    "declaration,module,kind,logical_status,collapsed_principal_dependencies"
  ]

  let mut mdLines : Array String := #[
    "# Time Lean logical-spine dependency report",
    "",
    "This is a reduced quotient of the checked Lean dependency graph. Suppressed implementation declarations are collapsed; each listed dependency is the nearest retained declaration reached along a project-local dependency path.",
    "",
    "Logical-status shapes in the GraphML: rectangle = Definition; rounded rectangle = Derived result; hexagon = Physical condition; ellipse = Effective assumption.",
    "",
    "| Declaration | Module | Kind | Logical status | Principal Lean-derived dependencies |",
    "|---|---|---|---|---|"
  ]

  let mut graphmlLines : Array String := #[
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
    "<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\"",
    "         xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"",
    "         xmlns:y=\"http://www.yworks.com/xml/graphml\"",
    "         xsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns http://www.yworks.com/xml/schema/graphml/1.1/ygraphml.xsd\">",
    "  <key id=\"d0\" for=\"node\" attr.name=\"declaration\" attr.type=\"string\"/>",
    "  <key id=\"d1\" for=\"node\" attr.name=\"module\" attr.type=\"string\"/>",
    "  <key id=\"d2\" for=\"node\" attr.name=\"kind\" attr.type=\"string\"/>",
    "  <key id=\"d3\" for=\"node\" attr.name=\"logical_status\" attr.type=\"string\"/>",
    "  <key id=\"d4\" for=\"node\" yfiles.type=\"nodegraphics\"/>",
    "  <key id=\"d5\" for=\"edge\" yfiles.type=\"edgegraphics\"/>",
    "  <graph id=\"G\" edgedefault=\"directed\">"
  ]

  let mut nodeIndex : Nat := 0
  for n in names do
    if let some ci := env.find? n then
      let deps := manuscriptSpineDeps env allowed retained n
      let modName :=
        match moduleNameOf? env n with
        | some m => toString m
        | none   => "<unknown>"
      let k := kindString ci
      let status := manuscriptLogicalStatus env n
      let shape := manuscriptLogicalShape env n
      let nS := toString n
      let depsS := renderNames deps

      csvLines := csvLines.push <|
        String.intercalate "," [
          csv nS, csv modName, csv k, csv status, csv depsS
        ]

      mdLines := mdLines.push <|
        "| `" ++ nS ++ "` | `" ++ modName ++ "` | " ++ k ++
        " | " ++ status ++ " | " ++ depsS ++ " |"

      let nodeId := "n" ++ toString nodeIndex
      graphmlLines := graphmlLines.push <| "    <node id=\"" ++ nodeId ++ "\">"
      graphmlLines := graphmlLines.push <| "      <data key=\"d0\">" ++ xmlEscape nS ++ "</data>"
      graphmlLines := graphmlLines.push <| "      <data key=\"d1\">" ++ xmlEscape modName ++ "</data>"
      graphmlLines := graphmlLines.push <| "      <data key=\"d2\">" ++ xmlEscape k ++ "</data>"
      graphmlLines := graphmlLines.push <| "      <data key=\"d3\">" ++ xmlEscape status ++ "</data>"
      graphmlLines := graphmlLines.push <| "      <data key=\"d4\">"
      graphmlLines := graphmlLines.push <| "        <y:ShapeNode>"
      graphmlLines := graphmlLines.push <| "          <y:NodeLabel>" ++ xmlEscape (shortNameString n) ++ "</y:NodeLabel>"
      graphmlLines := graphmlLines.push <| "          <y:Shape type=\"" ++ shape ++ "\"/>"
      graphmlLines := graphmlLines.push <| "        </y:ShapeNode>"
      graphmlLines := graphmlLines.push <| "      </data>"
      graphmlLines := graphmlLines.push <| "    </node>"

      nodeIndex := nodeIndex + 1

  -- Presentation direction: dependency -> dependent.
  let mut edgeIndex : Nat := 0
  for dependent in names do
    if let some dependentId := graphmlNodeId? names dependent then
      for dependency in (manuscriptSpineDeps env allowed retained dependent).toList do
        if let some dependencyId := graphmlNodeId? names dependency then
          graphmlLines := graphmlLines.push <|
            "    <edge id=\"e" ++ toString edgeIndex ++ "\" source=\"" ++
            dependencyId ++ "\" target=\"" ++ dependentId ++ "\">"
          graphmlLines := graphmlLines.push <| "      <data key=\"d5\">"
          graphmlLines := graphmlLines.push <| "        <y:PolyLineEdge>"
          graphmlLines := graphmlLines.push <| "          <y:Arrows source=\"none\" target=\"standard\"/>"
          graphmlLines := graphmlLines.push <| "        </y:PolyLineEdge>"
          graphmlLines := graphmlLines.push <| "      </data>"
          graphmlLines := graphmlLines.push <| "    </edge>"
          edgeIndex := edgeIndex + 1

  graphmlLines := graphmlLines.push "  </graph>"
  graphmlLines := graphmlLines.push "</graphml>"

  let csvText := String.intercalate "\n" csvLines.toList ++ "\n"
  let mdText := String.intercalate "\n" mdLines.toList ++ "\n"
  let graphmlText := String.intercalate "\n" graphmlLines.toList ++ "\n"

  return (csvText, mdText, graphmlText)



/--
Generate the manuscript-facing dependency map by applying a transitive
reduction to the collapsed logical-spine graph.

The retained node set is identical to `generateSpineReports`; only redundant
edges are removed.  GraphML presentation direction is dependency -> dependent.
-/
def generateManuscriptMapReports (env : Environment) : String × String × String := Id.run do
  let allowed := reportableProjectDeclSet env
  let retained := spineDeclSet allowed
  let names := manuscriptMapNames retained

  let mut csvLines : Array String := #[
    "declaration,module,kind,logical_status,transitively_reduced_principal_dependencies"
  ]

  let mut mdLines : Array String := #[
    "# Time manuscript dependency map",
    "",
    "This map is derived from the checked Lean dependency graph in two steps: suppressed implementation declarations are first collapsed, and then transitively redundant edges are removed from the retained DAG.",
    "",
    "A small set of terminal verification-support declarations is omitted only from this presentation map; they remain in the full logical-spine audit. Physically meaningful terminal conclusions, including PersistentRecord.elimination_not_reachable, remain visible.",
    "",
    "If `A -> B`, `B -> C`, and `A -> C` are all present in logical-flow direction, the direct `A -> C` edge is omitted because its dependency is already represented through `B`.",
    "",
    "Logical-status shapes in the GraphML: rectangle = Definition; rounded rectangle = Derived result; hexagon = Physical condition; ellipse = Effective assumption.",
    "",
    "| Declaration | Module | Kind | Logical status | Transitively reduced principal dependencies |",
    "|---|---|---|---|---|"
  ]

  let mut graphmlLines : Array String := #[
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
    "<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\"",
    "         xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"",
    "         xmlns:y=\"http://www.yworks.com/xml/graphml\"",
    "         xsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns http://www.yworks.com/xml/schema/graphml/1.1/ygraphml.xsd\">",
    "  <key id=\"d0\" for=\"node\" attr.name=\"declaration\" attr.type=\"string\"/>",
    "  <key id=\"d1\" for=\"node\" attr.name=\"module\" attr.type=\"string\"/>",
    "  <key id=\"d2\" for=\"node\" attr.name=\"kind\" attr.type=\"string\"/>",
    "  <key id=\"d3\" for=\"node\" attr.name=\"logical_status\" attr.type=\"string\"/>",
    "  <key id=\"d4\" for=\"node\" yfiles.type=\"nodegraphics\"/>",
    "  <key id=\"d5\" for=\"edge\" yfiles.type=\"edgegraphics\"/>",
    "  <graph id=\"G\" edgedefault=\"directed\">"
  ]

  let mut nodeIndex : Nat := 0
  for n in names do
    if let some ci := env.find? n then
      let deps := transitiveReducedSpineDeps env allowed retained n
      let modName :=
        match moduleNameOf? env n with
        | some m => toString m
        | none   => "<unknown>"
      let k := kindString ci
      let status := manuscriptLogicalStatus env n
      let shape := manuscriptLogicalShape env n
      let nS := toString n
      let depsS := renderNames deps

      csvLines := csvLines.push <|
        String.intercalate "," [
          csv nS, csv modName, csv k, csv status, csv depsS
        ]

      mdLines := mdLines.push <|
        "| `" ++ nS ++ "` | `" ++ modName ++ "` | " ++ k ++
        " | " ++ status ++ " | " ++ depsS ++ " |"

      let nodeId := "n" ++ toString nodeIndex
      graphmlLines := graphmlLines.push <| "    <node id=\"" ++ nodeId ++ "\">"
      graphmlLines := graphmlLines.push <| "      <data key=\"d0\">" ++ xmlEscape nS ++ "</data>"
      graphmlLines := graphmlLines.push <| "      <data key=\"d1\">" ++ xmlEscape modName ++ "</data>"
      graphmlLines := graphmlLines.push <| "      <data key=\"d2\">" ++ xmlEscape k ++ "</data>"
      graphmlLines := graphmlLines.push <| "      <data key=\"d3\">" ++ xmlEscape status ++ "</data>"
      graphmlLines := graphmlLines.push <| "      <data key=\"d4\">"
      graphmlLines := graphmlLines.push <| "        <y:ShapeNode>"
      graphmlLines := graphmlLines.push <| "          <y:NodeLabel>" ++ xmlEscape (shortNameString n) ++ "</y:NodeLabel>"
      graphmlLines := graphmlLines.push <| "          <y:Shape type=\"" ++ shape ++ "\"/>"
      graphmlLines := graphmlLines.push <| "        </y:ShapeNode>"
      graphmlLines := graphmlLines.push <| "      </data>"
      graphmlLines := graphmlLines.push <| "    </node>"

      nodeIndex := nodeIndex + 1

  -- Presentation direction: dependency -> dependent.
  let mut edgeIndex : Nat := 0
  for dependent in names do
    if let some dependentId := graphmlNodeId? names dependent then
      for dependency in (transitiveReducedSpineDeps env allowed retained dependent).toList do
        if let some dependencyId := graphmlNodeId? names dependency then
          graphmlLines := graphmlLines.push <|
            "    <edge id=\"e" ++ toString edgeIndex ++ "\" source=\"" ++
            dependencyId ++ "\" target=\"" ++ dependentId ++ "\">"
          graphmlLines := graphmlLines.push <| "      <data key=\"d5\">"
          graphmlLines := graphmlLines.push <| "        <y:PolyLineEdge>"
          graphmlLines := graphmlLines.push <| "          <y:Arrows source=\"none\" target=\"standard\"/>"
          graphmlLines := graphmlLines.push <| "        </y:PolyLineEdge>"
          graphmlLines := graphmlLines.push <| "      </data>"
          graphmlLines := graphmlLines.push <| "    </edge>"
          edgeIndex := edgeIndex + 1

  graphmlLines := graphmlLines.push "  </graph>"
  graphmlLines := graphmlLines.push "</graphml>"

  let csvText := String.intercalate "\n" csvLines.toList ++ "\n"
  let mdText := String.intercalate "\n" mdLines.toList ++ "\n"
  let graphmlText := String.intercalate "\n" graphmlLines.toList ++ "\n"

  return (csvText, mdText, graphmlText)


/-
===============================================================================
GROUPED MANUSCRIPT MAP
===============================================================================

The declaration-level manuscript map is deliberately retained as an audit
layer.  The grouped map below adds a second, coarser representation whose
nodes correspond to recognizable proof steps in the Time manuscript.

Grouping is human-supplied: it records the intended correspondence between
Lean declarations and conceptual manuscript steps.  Each group also names one
or more manuscript-facing interface declarations: the checked outputs by which
that proof block is represented.

Group-to-group edges are NOT supplied by hand.  Starting from those interface
declarations, dependency traversal passes through declarations internal to the
same group and stops at the first declaration belonging to another group.
Thus the grouped map is still derived from the checked declaration-level
dependency graph after the same manuscript normalization used above.

This gives two complementary checks:

  1. the declaration-level graph shows exactly what Lean depends on;
  2. the grouped graph shows whether those checked dependencies compose into
     the conceptual proof architecture stated in the manuscript.

The raw and declaration-level graphs should therefore remain available even
when the grouped map is used for presentation.
-/

/-- One conceptual proof group in the manuscript-facing map. -/
structure ManuscriptGroup where
  /-- Stable machine-readable identifier used in CSV/GraphML output. -/
  id : String
  /-- Human-readable proof-step label. -/
  label : String
  /--
  Short Lean declaration names assigned to this proof step.

  Membership is deliberately explicit rather than inferred from module names:
  a single Lean module may contain several conceptual proof steps, while one
  conceptual step may span several implementation declarations.
  -/
  members : List String
  /--
  Manuscript-facing output declarations for this proof step.

  Group dependencies are traced from these declarations only.  If an interface
  depends on another declaration in the same group, dependency traversal
  continues through that internal declaration until the first declaration in
  another conceptual group is reached.

  This is the crucial distinction between a conceptual proof block and a bag
  of declarations: helper definitions inside a block do not independently
  create group-level dependencies unless they lie on a checked dependency path
  from one of the block's stated outputs.
  -/
  interfaces : List String

/--
Conceptual proof groups aligned with the present structure of Supplementary
Discussion S2.

Every declaration retained in `spineShortNames` is assigned to exactly one
group in this version.  A group may additionally list non-retained Lean
declarations when they are internal support for the corresponding manuscript
step.  Such declarations remain available in the raw audit graph but do not
appear as separate nodes in the reduced manuscript declaration graph.

The grouping is not itself a logical assumption; it is a traceability layer
between manuscript prose and checked Lean declarations.
-/
def manuscriptGroups : List ManuscriptGroup := [
  {
    id := "sbi-boundary-interfaces"
    label := "SBI boundary interfaces"
    members := [
      "SBI.Time.OperationalAccessibilitySemantics",
      "SBI.Time.RecordFeatureSemantics",
      "SBI.Time.LocalRecordFormationSemantics",
      "SBI.Time.RelationalDomainSemantics",
      "SBI.Time.RelationallyAdjacent"
    ]
    interfaces := [
      "SBI.Time.OperationalAccessibilitySemantics",
      "SBI.Time.RecordFeatureSemantics",
      "SBI.Time.LocalRecordFormationSemantics",
      "SBI.Time.RelationalDomainSemantics",
      "SBI.Time.RelationallyAdjacent"
    ]
  },
  {
    id := "operational-duration-inputs"
    label := "Operational-duration definitions and calibration"
    members := [
      "SBI.Time.OperationalDurationParameter",
      "SBI.Time.LocalDurationScale"
    ]
    interfaces := [
      "SBI.Time.OperationalDurationParameter",
      "SBI.Time.LocalDurationScale"
    ]
  },
  {
    id := "physical-duration-domain"
    label := "Nonnegative physical-duration domain"
    members := ["SBI.Time.PhysicalDuration"]
    interfaces := ["SBI.Time.PhysicalDuration"]
  },
  {
    id := "operational-reachability"
    label := "Operational accessibility and reachability"
    members := [
      "SBI.Time.OperationalReachability",
      "SBI.Time.operationalReachability_is_admissibleDeformation"
    ]
    interfaces := [
      "SBI.Time.OperationalReachability",
      "SBI.Time.operationalReachability_is_admissibleDeformation"
    ]
  },
  {
    id := "reversible-classes"
    label := "Reversible equivalence classes"
    members := [
      "SBI.Time.ReversibleEquivalent",
      "SBI.Time.ReversibleClass",
      "SBI.Time.reversibleClassOf"
    ]
    interfaces := [
      "SBI.Time.ReversibleClass",
      "SBI.Time.reversibleClassOf"
    ]
  },
  {
    id := "asymmetric-reachability"
    label := "Asymmetric reachability"
    members := [
      "SBI.Time.AsymmetricReachability",
      "SBI.Time.asymmetricReachability_not_reversibleEquivalent",
      "SBI.Time.asymmetricReachability_trans"
    ]
    interfaces := [
      "SBI.Time.asymmetricReachability_not_reversibleEquivalent",
      "SBI.Time.asymmetricReachability_trans"
    ]
  },
  {
    id := "irreversible-precedence"
    label := "Irreversible precedence"
    members := [
      "SBI.Time.IrreversiblePrecedence",
      "SBI.Time.irreversiblePrecedence_irrefl",
      "SBI.Time.irreversiblePrecedence_trans",
      "SBI.Time.irreversiblePrecedence_strictPartialOrder"
    ]
    interfaces := ["SBI.Time.irreversiblePrecedence_strictPartialOrder"]
  },
  {
    id := "ordered-history"
    label := "Ordered physical history and real representation"
    members := [
      "SBI.Time.OrderedPhysicalHistory",
      "SBI.Time.HistoryAtMostCountable",
      "SBI.Time.HistoryPrecedence",
      "SBI.Time.historyPrecedence_isStrictTotalOrder",
      "SBI.Time.history_orderEmbedsIntoReal",
      "SBI.Time.strictMono_reparametrization_preserves_temporalOrder"
    ]
    interfaces := [
      "SBI.Time.history_orderEmbedsIntoReal",
      "SBI.Time.strictMono_reparametrization_preserves_temporalOrder"
    ]
  },
  {
    id := "temporal-order-conclusion"
    label := "Temporal-order characterization"
    members := ["SBI.Time.temporalOrder_characterization"]
    interfaces := ["SBI.Time.temporalOrder_characterization"]
  },
  {
    id := "record-semantics"
    label := "Persistent-record semantics"
    members := [
      "SBI.Time.OperationallyReconstructible",
      "SBI.Time.OperationallyIrreversible",
      "SBI.Time.operationallyIrreversible_iff_asymmetricReachability",
      "SBI.Time.PersistentRecord",
      "SBI.Time.PersistentRecord.operationallyIrreversible",
      "SBI.Time.PersistentRecord.elimination_not_reachable",
      "SBI.Time.PersistentRecord.asymmetricReachability",
      "SBI.Time.PersistentRecord.irreversiblePrecedence"
    ]
    interfaces := [
      "SBI.Time.PersistentRecord.elimination_not_reachable",
      "SBI.Time.PersistentRecord.irreversiblePrecedence"
    ]
  },
  {
    id := "local-record-obstruction"
    label := "Local reconstruction obstruction"
    members := [
      "SBI.Time.LocalReconstructionSet",
      "SBI.Time.PersistenceCompatibleSet",
      "SBI.Time.LocalReconstructionPersistenceIncompatible",
      "SBI.Time.local_reconstruction_obstruction"
    ]
    interfaces := ["SBI.Time.local_reconstruction_obstruction"]
  },
  {
    id := "propagation-structure"
    label := "Relational propagation structure"
    members := [
      "SBI.Time.RelationalIncidenceChain",
      "SBI.Time.RelationalPropagationDepth",
      "SBI.Time.RelationalPropagationDepthToDomain",
      "SBI.Time.RelationalShell",
      "SBI.Time.LimitingPropagationFront",
      "SBI.Time.WithinRelationalDepth"
    ]
    interfaces := [
      "SBI.Time.LimitingPropagationFront",
      "SBI.Time.WithinRelationalDepth"
    ]
  },
  {
    id := "no-overtaking"
    label := "Locally mediated no-overtaking"
    members := [
      "SBI.Time.LocallyMediatedReconstructionPropagation",
      "SBI.Time.LocallyMediatedReconstructionPropagation.support_within_bound",
      "SBI.Time.reconstruction_lag_remains_strict",
      "SBI.Time.LocallyMediatedReconstructionPropagation.cannot_overtake_limiting_front",
      "SBI.Time.LimitingDependencyPropagation",
      "SBI.Time.LocallyMediatedReconstructionPropagation.disjoint_from_limiting_dependency"
    ]
    interfaces := [
      "SBI.Time.LocallyMediatedReconstructionPropagation.cannot_overtake_limiting_front",
      "SBI.Time.LocallyMediatedReconstructionPropagation.disjoint_from_limiting_dependency"
    ]
  },
  {
    id := "dependency-recovery"
    label := "Dependency recovery requirement"
    members := [
      "SBI.Time.ReconstructionRequiresDependencyRecovery",
      "SBI.Time.ReconstructionRequiresDependencyRecovery.not_operationally_reconstructible"
    ]
    interfaces := [
      "SBI.Time.ReconstructionRequiresDependencyRecovery.not_operationally_reconstructible"
    ]
  },
  {
    id := "persistent-record-formation"
    label := "Persistent record from limiting dependency"
    members := ["SBI.Time.persistentRecord_of_limiting_dependency"]
    interfaces := ["SBI.Time.persistentRecord_of_limiting_dependency"]
  },
  {
    id := "persistent-record-consequences"
    label := "Persistent-record consequences"
    members := ["SBI.Time.persistentRecord_consequences"]
    interfaces := ["SBI.Time.persistentRecord_consequences"]
  },
  {
    id := "reversible-exploration"
    label := "Represented reversible exploration"
    members := [
      "SBI.Time.AccessibleRearrangementPath",
      "SBI.Time.accessibleRearrangementPath_is_operationalReachability",
      "SBI.Time.ReversibleRearrangementPath",
      "SBI.Time.ReversibleRearrangementPath.pathLength",
      "SBI.Time.ReversibleRearrangementPath.pathLength_append",
      "SBI.Time.ReversibleRearrangementPath.pathLength_reverse",
      "SBI.Time.ReversibleRearrangementPath.is_operationalReachability",
      "SBI.Time.ReversibleRearrangementPath.endpoints_reversibleEquivalent",
      "SBI.Time.ReversibleRearrangementPath.same_reversibleClass"
    ]
    interfaces := [
      "SBI.Time.ReversibleRearrangementPath.pathLength_append",
      "SBI.Time.ReversibleRearrangementPath.pathLength_reverse",
      "SBI.Time.ReversibleRearrangementPath.same_reversibleClass"
    ]
  },
  {
    id := "operational-duration"
    label := "Accumulated operational duration"
    members := [
      "SBI.Time.OperationalClock",
      "SBI.Time.ReversibleRearrangementPath.accumulatedDuration",
      "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_eq_zero_iff_pathLength_eq_zero",
      "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_append",
      "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_reverse",
      "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_lt_of_pathLength_lt"
    ]
    interfaces := [
      "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_eq_zero_iff_pathLength_eq_zero",
      "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_append",
      "SBI.Time.ReversibleRearrangementPath.accumulatedDuration_reverse"
    ]
  },
  {
    id := "reversible-duration-conclusion"
    label := "Reversible-duration characterization"
    members := ["SBI.Time.reversibleDuration_characterization"]
    interfaces := ["SBI.Time.reversibleDuration_characterization"]
  },
  {
    id := "reversible-clocks"
    label := "Reversible clocks"
    members := [
      "SBI.Time.ReversibleCycle",
      "SBI.Time.ReversibleClock",
      "SBI.Time.ReversibleClock.tickDuration",
      "SBI.Time.ReversibleClock.tickDuration_pos",
      "SBI.Time.ReversibleCycle.accumulatedDuration_iterate",
      "SBI.Time.ReversibleClock.durationAfterCycles",
      "SBI.Time.ReversibleClock.durationAfterCycles_strictMono",
      "SBI.Time.ReversibleClock.toOperationalClock"
    ]
    interfaces := [
      "SBI.Time.ReversibleClock.durationAfterCycles_strictMono",
      "SBI.Time.ReversibleClock.toOperationalClock"
    ]
  },
  {
    id := "operational-to-physical-duration"
    label := "Operational-to-physical duration bridge"
    members := ["SBI.Time.ReversibleRearrangementPath.physicalDuration"]
    interfaces := ["SBI.Time.ReversibleRearrangementPath.physicalDuration"]
  },
  {
    id := "physical-duration-conclusion"
    label := "Physical-duration characterization"
    members := ["SBI.Time.physicalDuration_characterization"]
    interfaces := ["SBI.Time.physicalDuration_characterization"]
  },
  {
    id := "physical-duration-semigroup"
    label := "Nonnegative physical-duration evolution"
    members := [
      "SBI.Time.AutonomousPhysicalDurationEvolution",
      "SBI.Time.AutonomousPhysicalDurationEvolution.evolve_from_reached_state"
    ]
    interfaces := [
      "SBI.Time.AutonomousPhysicalDurationEvolution.evolve_from_reached_state"
    ]
  },
  {
    id := "physical-duration-continuity"
    label := "Continuous physical-duration evolution"
    members := ["SBI.Time.ContinuousAutonomousPhysicalDurationEvolution"]
    interfaces := ["SBI.Time.ContinuousAutonomousPhysicalDurationEvolution"]
  },
  {
    id := "physical-duration-generator"
    label := "Right-differentiable physical-duration generator"
    members := [
      "SBI.Time.RightDifferentiableAutonomousPhysicalDurationEvolution",
      "SBI.Time.RightDifferentiableAutonomousPhysicalDurationEvolution.hasDerivWithinAt_generator",
      "SBI.Time.RightDifferentiableAutonomousPhysicalDurationEvolution.hasDerivWithinAt_incremented_duration",
      "SBI.Time.RightDifferentiableAutonomousPhysicalDurationEvolution.derivWithin_incremented_duration"
    ]
    interfaces := [
      "SBI.Time.RightDifferentiableAutonomousPhysicalDurationEvolution.derivWithin_incremented_duration"
    ]
  },
  {
    id := "physical-duration-generator-conclusion"
    label := "Physical-duration generator characterization"
    members := ["SBI.Time.physicalDurationGenerator_characterization"]
    interfaces := ["SBI.Time.physicalDurationGenerator_characterization"]
  },
  {
    id := "reversible-state-maps"
    label := "Invertible state maps without negative duration"
    members := [
      "SBI.Time.ReversibleAutonomousPhysicalDurationEvolution",
      "SBI.Time.ReversibleAutonomousPhysicalDurationEvolution.inverse_after_evolve",
      "SBI.Time.ReversibleAutonomousPhysicalDurationEvolution.evolve_after_inverse"
    ]
    interfaces := [
      "SBI.Time.ReversibleAutonomousPhysicalDurationEvolution.inverse_after_evolve",
      "SBI.Time.ReversibleAutonomousPhysicalDurationEvolution.evolve_after_inverse"
    ]
  },
  {
    id := "reversible-state-maps-conclusion"
    label := "Reversible physical-duration evolution"
    members := ["SBI.Time.reversiblePhysicalDurationEvolution_characterization"]
    interfaces := ["SBI.Time.reversiblePhysicalDurationEvolution_characterization"]
  },

]

/-- True when declaration `n` is assigned to conceptual group `g`. -/
def manuscriptGroupContains (g : ManuscriptGroup) (n : Name) : Bool :=
  g.members.any fun s => s == toString n

/-- Conceptual manuscript group assigned to declaration `n`, if any. -/
def manuscriptGroupOf? (n : Name) : Option ManuscriptGroup :=
  manuscriptGroups.find? fun g => manuscriptGroupContains g n

/--
Number of conceptual groups to which declaration `n` is assigned.

The expected value for every retained manuscript-spine declaration is exactly
one.  The report command emits warnings for missing or duplicate assignments.
-/
def manuscriptGroupMembershipCount (n : Name) : Nat :=
  manuscriptGroups.foldl
    (fun total g =>
      if manuscriptGroupContains g n then total + 1 else total)
    0

/-- Look up a conceptual group by stable group identifier. -/
def manuscriptGroupById? (id : String) : Option ManuscriptGroup :=
  manuscriptGroups.find? fun g => g.id == id

/-- Retained Lean declarations belonging to conceptual group `g`. -/
def retainedMembersOfGroup
    (retained : NameSet)
    (g : ManuscriptGroup) : List Name :=
  retained.toList.filter fun n => manuscriptGroupContains g n

/-- Retained manuscript-facing outputs of conceptual group `g`. -/
def retainedInterfacesOfGroup
    (retained : NameSet)
    (g : ManuscriptGroup) : List Name :=
  retainedMembersOfGroup retained g |>.filter fun n =>
    g.interfaces.any fun s => s == toString n

/-- True when at least one retained declaration belongs to `g`. -/
def manuscriptGroupPresent
    (retained : NameSet)
    (g : ManuscriptGroup) : Bool :=
  (retainedMembersOfGroup retained g).any fun _ => true

/-- Conceptual groups represented in the current retained declaration set. -/
def presentManuscriptGroups (retained : NameSet) : List ManuscriptGroup :=
  manuscriptGroups.filter fun g => manuscriptGroupPresent retained g

/-- Append a String only when it is not already present. -/
def appendUniqueString (xs : List String) (s : String) : List String :=
  if xs.contains s then xs else xs ++ [s]

/--
Traverse checked declaration dependencies from a conceptual group's interface
declarations to the first declarations belonging to other conceptual groups.

Declarations belonging to the current group are treated as internal proof
steps and are traversed rather than emitted as dependencies.  This is the
group-level analogue of `collapsedFrontierDeps`.

The resulting edges therefore mean:

  "a stated output of group G depends, through zero or more internal
   declarations of G, on a declaration belonging to group H."

This avoids two pathologies of the first grouping attempt:

  * low-level helper definitions no longer create unrelated group edges merely
    because they were placed in the same conceptual box;
  * dependencies passing through internal helper declarations are not lost.
-/
partial def manuscriptGroupFrontierLoop
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
        manuscriptGroupFrontierLoop
          env allowed retained currentGroupId rest seen out
      else
        let seen' := seen.insert n
        match manuscriptGroupOf? n with
        | none =>
            let more := (manuscriptSpineDeps env allowed retained n).toList
            manuscriptGroupFrontierLoop
              env allowed retained currentGroupId (more ++ rest) seen' out
        | some dependencyGroup =>
            if dependencyGroup.id == currentGroupId then
              let more := (manuscriptSpineDeps env allowed retained n).toList
              manuscriptGroupFrontierLoop
                env allowed retained currentGroupId (more ++ rest) seen' out
            else
              manuscriptGroupFrontierLoop
                env allowed retained currentGroupId rest seen'
                (appendUniqueString out dependencyGroup.id)

/--
Direct conceptual dependencies of a manuscript group.

Only the group's manuscript-facing interface declarations are used as starting
points.  Checked dependency paths are then followed through declarations
internal to the same group until another conceptual group is reached.

Thus human input specifies group membership and the manuscript-facing outputs;
the group-to-group edges still come entirely from checked Lean dependencies.
-/
def manuscriptGroupDirectDeps
    (env : Environment)
    (allowed retained : NameSet)
    (g : ManuscriptGroup) : List String := Id.run do

  let mut start : List Name := []

  for n in retainedInterfacesOfGroup retained g do
    start := (manuscriptSpineDeps env allowed retained n).toList ++ start

  return manuscriptGroupFrontierLoop
    env allowed retained g.id start {} []


/--
Reachability in the grouped manuscript graph, following the dependency
orientation `dependent group -> dependency group`.
-/
partial def manuscriptGroupReachableLoop
    (env : Environment)
    (allowed retained : NameSet)
    (target : String)
    (todo seen : List String) : Bool :=
  match todo with
  | [] => false
  | current :: rest =>
      if current == target then
        true
      else if seen.contains current then
        manuscriptGroupReachableLoop env allowed retained target rest seen
      else
        let seen' := current :: seen
        match manuscriptGroupById? current with
        | none =>
            manuscriptGroupReachableLoop env allowed retained target rest seen'
        | some g =>
            let more := manuscriptGroupDirectDeps env allowed retained g
            manuscriptGroupReachableLoop
              env allowed retained target (more ++ rest) seen'

/-- True when group `target` is reachable from group `start`. -/
def manuscriptGroupReachable
    (env : Environment)
    (allowed retained : NameSet)
    (start target : String) : Bool :=
  manuscriptGroupReachableLoop env allowed retained target [start] []

/--
Transitive reduction of the grouped dependency relation.

This is performed only after declaration-level dependencies have been
quotiented by conceptual proof group.  Redundant long-range group edges are
removed exactly as in the declaration-level manuscript map.
-/
def transitiveReducedManuscriptGroupDeps
    (env : Environment)
    (allowed retained : NameSet)
    (g : ManuscriptGroup) : List String :=
  let deps := manuscriptGroupDirectDeps env allowed retained g
  deps.filter fun d =>
    !(deps.any fun alt =>
      (!(alt == d)) &&
      manuscriptGroupReachable env allowed retained alt d)

/-- Find the zero-based position of a group id in a list of groups. -/
def manuscriptGroupIndexAux
    (target : String) : List ManuscriptGroup → Nat → Option Nat
  | [], _ => none
  | g :: gs, i =>
      if g.id == target then
        some i
      else
        manuscriptGroupIndexAux target gs (i + 1)

/-- Stable GraphML node id for a conceptual manuscript group. -/
def manuscriptGroupNodeId?
    (groups : List ManuscriptGroup)
    (id : String) : Option String := do
  let i ← manuscriptGroupIndexAux id groups 0
  return "g" ++ toString i

/-- Render present Lean members of a conceptual group. -/
def renderManuscriptGroupMembers
    (retained : NameSet)
    (g : ManuscriptGroup) : String :=
  String.intercalate "; "
    ((retainedMembersOfGroup retained g).map shortNameString)

/-- Render retained manuscript-facing outputs of a conceptual group. -/
def renderManuscriptGroupInterfaces
    (retained : NameSet)
    (g : ManuscriptGroup) : String :=
  String.intercalate "; "
    ((retainedInterfacesOfGroup retained g).map shortNameString)

/--
Generate the conceptual grouped manuscript map.

The output is intentionally additional to, not a replacement for, the raw
dependency graph and declaration-level manuscript map.

CSV/Markdown list each conceptual proof step, the Lean declarations assigned
to it, the direct quotient dependencies, and the transitively reduced quotient
dependencies.  GraphML uses one visible node per proof group and the reduced
group edges in logical-flow direction: dependency group -> dependent group.
-/
def generateGroupedManuscriptMapReports
    (env : Environment) : String × String × String := Id.run do

  let allowed := reportableProjectDeclSet env
  let retained := spineDeclSet allowed
  let groups := presentManuscriptGroups retained

  let mut csvLines : Array String := #[
    "group_id,label,lean_members,interface_declarations,direct_group_dependencies,transitively_reduced_group_dependencies"
  ]

  let mut mdLines : Array String := #[
    "# Time grouped manuscript proof map",
    "",
    "This is a conceptual quotient of the declaration-level manuscript map.",
    "Group membership is supplied explicitly to match the proof structure of the Time manuscript; all edges between groups are derived from checked Lean declaration dependencies.",
    "",
    "The declaration-level maps remain the audit layer. This grouped map is the manuscript-traceability layer.",
    "",
    "| Proof group | Lean declarations | Interface declarations | Direct checked group dependencies | Reduced dependencies |",
    "|---|---|---|---|---|"
  ]

  let mut graphmlLines : Array String := #[
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
    "<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\"",
    "         xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"",
    "         xmlns:y=\"http://www.yworks.com/xml/graphml\"",
    "         xsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns http://www.yworks.com/xml/schema/graphml/1.1/ygraphml.xsd\">",
    "  <key id=\"d0\" for=\"node\" attr.name=\"group_id\" attr.type=\"string\"/>",
    "  <key id=\"d1\" for=\"node\" attr.name=\"label\" attr.type=\"string\"/>",
    "  <key id=\"d2\" for=\"node\" attr.name=\"lean_members\" attr.type=\"string\"/>",
    "  <key id=\"d3\" for=\"node\" yfiles.type=\"nodegraphics\"/>",
    "  <key id=\"d4\" for=\"edge\" yfiles.type=\"edgegraphics\"/>",
    "  <graph id=\"G\" edgedefault=\"directed\">"
  ]

  let mut nodeIndex : Nat := 0

  for g in groups do
    let membersS := renderManuscriptGroupMembers retained g
    let directDeps := manuscriptGroupDirectDeps env allowed retained g
    let reducedDeps :=
      transitiveReducedManuscriptGroupDeps env allowed retained g
    let directS := String.intercalate "; " directDeps
    let reducedS := String.intercalate "; " reducedDeps

    csvLines := csvLines.push <|
      String.intercalate "," [
        csv g.id, csv g.label, csv membersS, csv directS, csv reducedS
      ]

    mdLines := mdLines.push <|
      "| **" ++ g.label ++ "** | " ++ membersS ++
      " | " ++ directS ++ " | " ++ reducedS ++ " |"

    let nodeId := "g" ++ toString nodeIndex
    graphmlLines := graphmlLines.push <| "    <node id=\"" ++ nodeId ++ "\">"
    graphmlLines := graphmlLines.push <|
      "      <data key=\"d0\">" ++ xmlEscape g.id ++ "</data>"
    graphmlLines := graphmlLines.push <|
      "      <data key=\"d1\">" ++ xmlEscape g.label ++ "</data>"
    graphmlLines := graphmlLines.push <|
      "      <data key=\"d2\">" ++ xmlEscape membersS ++ "</data>"
    graphmlLines := graphmlLines.push <| "      <data key=\"d3\">"
    graphmlLines := graphmlLines.push <| "        <y:ShapeNode>"
    graphmlLines := graphmlLines.push <|
      "          <y:NodeLabel>" ++ xmlEscape g.label ++ "</y:NodeLabel>"
    graphmlLines := graphmlLines.push <|
      "          <y:Shape type=\"roundrectangle\"/>"
    graphmlLines := graphmlLines.push <| "        </y:ShapeNode>"
    graphmlLines := graphmlLines.push <| "      </data>"
    graphmlLines := graphmlLines.push <| "    </node>"

    nodeIndex := nodeIndex + 1

  -- Presentation direction: dependency group -> dependent group.
  let mut edgeIndex : Nat := 0

  for dependentGroup in groups do
    if let some dependentId :=
        manuscriptGroupNodeId? groups dependentGroup.id then
      for dependencyIdString in
          transitiveReducedManuscriptGroupDeps
            env allowed retained dependentGroup do
        if let some dependencyId :=
            manuscriptGroupNodeId? groups dependencyIdString then
          graphmlLines := graphmlLines.push <|
            "    <edge id=\"ge" ++ toString edgeIndex ++
            "\" source=\"" ++ dependencyId ++
            "\" target=\"" ++ dependentId ++ "\">"
          graphmlLines := graphmlLines.push <| "      <data key=\"d4\">"
          graphmlLines := graphmlLines.push <| "        <y:PolyLineEdge>"
          graphmlLines := graphmlLines.push <|
            "          <y:Arrows source=\"none\" target=\"standard\"/>"
          graphmlLines := graphmlLines.push <| "        </y:PolyLineEdge>"
          graphmlLines := graphmlLines.push <| "      </data>"
          graphmlLines := graphmlLines.push <| "    </edge>"
          edgeIndex := edgeIndex + 1

  graphmlLines := graphmlLines.push "  </graph>"
  graphmlLines := graphmlLines.push "</graphml>"

  let csvText := String.intercalate "\n" csvLines.toList ++ "\n"
  let mdText := String.intercalate "\n" mdLines.toList ++ "\n"
  let graphmlText := String.intercalate "\n" graphmlLines.toList ++ "\n"

  return (csvText, mdText, graphmlText)



/-
===============================================================================
SBI -> TIME FORMAL BOUNDARY REPORT
===============================================================================

The ordinary Time dependency reports intentionally restrict themselves to
`SBILeanProject.Time.*`.  That keeps the Time proof graph readable, but it
also hides the checked declarations imported from the companion SBI
formalization.

The report below exposes that boundary without inserting any dependency edge
by hand.

For every declaration retained in the Time manuscript spine, we inspect its
checked type and body and collect constants belonging to imported
`SBILeanProject.SBI.*` modules.  These are direct cross-boundary
dependencies.

For each such SBI interface declaration, we then follow checked SBI-local
dependencies and ask whether the exact axiom projections

    SBI.A1
    SBI.A2
    SBI.A3

are reachable.  When an axiom is reachable, one concrete checked dependency
path is recorded as a witness.  The path is machine-discovered; no axiom is
assigned to a Time declaration by hand.

This distinction is important.  Merely carrying an ambient parameter
`M : SBI` does not by itself count here as substantive use of A1, A2, or A3.
An axiom is reported only when its corresponding Lean declaration is reached
through the checked dependency graph.

The GraphML is intentionally compressed.  It contains:

  * retained Time declarations that directly cross the SBI boundary;
  * the SBI declarations directly used by those Time declarations;
  * the SBI axioms actually reached from those interface declarations.

Edges SBI-interface -> Time are direct checked dependencies.  Edges
axiom -> SBI-interface summarize a checked transitive SBI path; one exact
witness path is retained in the CSV/Markdown report and as GraphML edge data.
-/

/-- Imported SBI modules used as the formal boundary below Time. -/
def sbiModulePrefix : Name := `SBILeanProject.SBI

/-- All declarations belonging to imported SBI modules. -/
def sbiProjectDeclSet (env : Environment) : NameSet := Id.run do
  let mut out : NameSet := {}

  for modName in env.header.moduleNames do
    if sbiModulePrefix.isPrefixOf modName then
      if let some idx := env.getModuleIdx? modName then
        let i := idx.toNat
        if h : i < env.header.moduleData.size then
          let modData := env.header.moduleData[i]'h
          for n in modData.constNames do
            out := out.insert n

  return out

/-- User-facing declarations in the imported SBI development. -/
def reportableSbiDeclSet (env : Environment) : NameSet :=
  (sbiProjectDeclSet env).filter (isReportableDecl env)

/-- Exact manuscript axiom projections whose checked use we want to expose. -/
def sbiAxiomNames : List Name := [
  `SBI.A1,
  `SBI.A2,
  `SBI.A3
]

/-- Append a declaration name only when it is not already present. -/
def appendUniqueName (xs : List Name) (n : Name) : List Name :=
  if xs.contains n then xs else xs ++ [n]

/--
Breadth/depth-first search state for one concrete dependency-path witness.

Each queue entry stores a declaration and the reverse path from the start
declaration to that node.
-/
partial def dependencyPathLoop
    (env : Environment)
    (allowed : NameSet)
    (target : Name)
    (todo : List (Name × List Name))
    (seen : NameSet) : Option (List Name) :=
  match todo with
  | [] =>
      none
  | (n, pathRev) :: rest =>
      if n == target then
        some pathRev.reverse
      else if seen.contains n then
        dependencyPathLoop env allowed target rest seen
      else
        let seen' := seen.insert n
        let more :=
          (directDeps env allowed n).toList.map fun d =>
            (d, d :: pathRev)
        dependencyPathLoop
          env allowed target (more ++ rest) seen'

/--
Find one checked dependency path from `start` to `target`, restricted to
the supplied declaration set.

The returned path includes both endpoints.  Failure means that no such path
was found in the checked dependency graph under that restriction.
-/
def dependencyPath?
    (env : Environment)
    (allowed : NameSet)
    (start target : Name) : Option (List Name) :=
  dependencyPathLoop
    env allowed target [(start, [start])] {}

/-- Human-readable rendering of one dependency-path witness. -/
def renderDependencyPath (path : List Name) : String :=
  String.intercalate " -> " (path.map toString)

/--
Compact visible label for the SBI/Time boundary graph.

The full Lean declaration name remains stored as GraphML metadata.  Only the
common namespace prefix is removed from the visible label, so nested
declarations such as `ConfigurationChangeSemantics.AdmissibleStep` remain
unambiguous without filling the figure with repeated `SBI.Time.` or `SBI.`
prefixes.
-/
def boundaryDisplayName (n : Name) : String :=
  let s := toString n
  if s.startsWith "SBI.Time." then
    (s.drop 9).toString
  else if s.startsWith "SBI." then
    (s.drop 4).toString
  else
    s

/--
Generate the SBI/Time boundary audit.

CSV/Markdown contain one row for each direct checked dependency from a
retained Time declaration to an imported SBI declaration.  For that interface
declaration, all reachable manuscript axioms are listed together with one
machine-discovered witness path per axiom.

The GraphML is a compact boundary view in logical-flow direction:

    SBI axiom -> SBI interface -> Time declaration.

The axiom-to-interface edge is explicitly marked as a collapsed transitive
path rather than a direct dependency.
-/
def generateSbiBoundaryReports
    (env : Environment) : String × String × String := Id.run do

  let timeAllowed := reportableProjectDeclSet env
  let retainedTime := spineDeclSet timeAllowed
  let sbiAllowed := reportableSbiDeclSet env
  let retainedTimeNames := retainedTime.toList

  let mut boundaryTimeNames : List Name := []
  let mut interfaceNames : List Name := []
  let mut reachedAxiomNames : List Name := []

  let mut csvLines : Array String := #[
    "time_declaration,direct_sbi_interface,sbi_module,sbi_kind,reachable_axioms,witness_paths"
  ]

  let mut mdLines : Array String := #[
    "# Time / SBI formal boundary report",
    "",
    "Each row records a direct checked dependency from a declaration retained in the Time manuscript spine to a declaration in the imported SBI formalization.",
    "",
    "The **Reachable SBI axioms** column contains only exact Lean declarations `SBI.A1`, `SBI.A2`, or `SBI.A3` reached through checked SBI-local dependency edges. Merely carrying an ambient `M : SBI` parameter is not treated as an axiom dependency.",
    "",
    "For every reported axiom, **Witness path** gives one machine-discovered declaration-level dependency path from the SBI interface declaration to that axiom. Other valid checked paths may also exist.",
    "",
    "The CSV/Markdown table is exhaustive at the retained Time/SBI boundary. The GraphML is intentionally smaller: it shows only machine-derived Time boundary roots, their directly used SBI interfaces, and the axioms reached through checked SBI paths.",
    "",
    "| Time declaration | Direct SBI interface | SBI module | Kind | Reachable SBI axioms | Witness path(s) |",
    "|---|---|---|---|---|---|"
  ]

  for t in retainedTimeNames do
    let directSbi := directDeps env sbiAllowed t

    for s in directSbi.toList do
      boundaryTimeNames := appendUniqueName boundaryTimeNames t
      interfaceNames := appendUniqueName interfaceNames s

      let mut reachableAxioms : List Name := []
      let mut witnessPaths : List String := []

      for a in sbiAxiomNames do
        match dependencyPath? env sbiAllowed s a with
        | none =>
            pure ()
        | some path =>
            reachableAxioms := appendUniqueName reachableAxioms a
            reachedAxiomNames := appendUniqueName reachedAxiomNames a
            witnessPaths :=
              witnessPaths ++
                [toString a ++ ": " ++ renderDependencyPath path]

      let modName :=
        match moduleNameOf? env s with
        | some m => toString m
        | none   => "<unknown>"

      let kind :=
        match env.find? s with
        | some ci => kindString ci
        | none    => "<unknown>"

      let axiomText :=
        String.intercalate "; " (reachableAxioms.map toString)

      let witnessText :=
        String.intercalate " | " witnessPaths

      csvLines := csvLines.push <|
        String.intercalate "," [
          csv (toString t),
          csv (toString s),
          csv modName,
          csv kind,
          csv axiomText,
          csv witnessText
        ]

      mdLines := mdLines.push <|
        "| `" ++ toString t ++
        "` | `" ++ toString s ++
        "` | `" ++ modName ++
        "` | " ++ kind ++
        " | " ++ axiomText ++
        " | " ++ witnessText ++ " |"

  /-
  Human-readable GraphML view.

  The CSV and Markdown reports above intentionally retain every direct
  cross-boundary dependency.  Plotting all of those edges is not useful:
  most downstream Time declarations repeat the same SBI type parameters.

  For the visual graph we therefore keep only machine-derived boundary roots:
  retained Time declarations that

    1. directly depend on at least one SBI declaration, and
    2. have no retained Time dependency in the manuscript spine.

  No Time root is selected by hand.  This is the formal entry surface through
  which imported SBI structure first enters the retained Time derivation.
  -/
  let boundaryRootTimeNames :=
    boundaryTimeNames.filter fun t =>
      (manuscriptSpineDeps env timeAllowed retainedTime t).isEmpty

  let mut visualInterfaceNames : List Name := []

  for t in boundaryRootTimeNames do
    for s in (directDeps env sbiAllowed t).toList do
      visualInterfaceNames :=
        appendUniqueName visualInterfaceNames s

  let mut visualAxiomNames : List Name := []

  for s in visualInterfaceNames do
    for a in sbiAxiomNames do
      match dependencyPath? env sbiAllowed s a with
      | none =>
          pure ()
      | some _ =>
          visualAxiomNames :=
            appendUniqueName visualAxiomNames a

  let mut graphNames : List Name := []

  for a in visualAxiomNames do
    graphNames := appendUniqueName graphNames a

  for s in visualInterfaceNames do
    graphNames := appendUniqueName graphNames s

  for t in boundaryRootTimeNames do
    graphNames := appendUniqueName graphNames t

  let mut graphmlLines : Array String := #[
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
    "<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\"",
    "         xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"",
    "         xmlns:y=\"http://www.yworks.com/xml/graphml\"",
    "         xsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns http://www.yworks.com/xml/schema/graphml/1.1/ygraphml.xsd\">",
    "  <key id=\"d0\" for=\"node\" attr.name=\"declaration\" attr.type=\"string\"/>",
    "  <key id=\"d1\" for=\"node\" attr.name=\"layer\" attr.type=\"string\"/>",
    "  <key id=\"d2\" for=\"node\" attr.name=\"module\" attr.type=\"string\"/>",
    "  <key id=\"d3\" for=\"node\" attr.name=\"kind\" attr.type=\"string\"/>",
    "  <key id=\"d4\" for=\"node\" yfiles.type=\"nodegraphics\"/>",
    "  <key id=\"d5\" for=\"edge\" attr.name=\"relation\" attr.type=\"string\"/>",
    "  <key id=\"d6\" for=\"edge\" attr.name=\"witness_path\" attr.type=\"string\"/>",
    "  <key id=\"d7\" for=\"edge\" yfiles.type=\"edgegraphics\"/>",
    "  <graph id=\"G\" edgedefault=\"directed\">"
  ]

  let mut nodeIndex : Nat := 0

  for n in graphNames do
    let nS := toString n

    let layer :=
      if visualAxiomNames.contains n then
        "SBI axiom"
      else if visualInterfaceNames.contains n then
        "SBI interface"
      else
        "Time"

    let modName :=
      match moduleNameOf? env n with
      | some m => toString m
      | none   => "<unknown>"

    let kind :=
      match env.find? n with
      | some ci => kindString ci
      | none    => "<unknown>"

    let shape :=
      if visualAxiomNames.contains n then
        "ellipse"
      else if visualInterfaceNames.contains n then
        "roundrectangle"
      else
        "rectangle"

    let nodeId := "n" ++ toString nodeIndex

    graphmlLines := graphmlLines.push <|
      "    <node id=\"" ++ nodeId ++ "\">"
    graphmlLines := graphmlLines.push <|
      "      <data key=\"d0\">" ++ xmlEscape nS ++ "</data>"
    graphmlLines := graphmlLines.push <|
      "      <data key=\"d1\">" ++ xmlEscape layer ++ "</data>"
    graphmlLines := graphmlLines.push <|
      "      <data key=\"d2\">" ++ xmlEscape modName ++ "</data>"
    graphmlLines := graphmlLines.push <|
      "      <data key=\"d3\">" ++ xmlEscape kind ++ "</data>"
    graphmlLines := graphmlLines.push <| "      <data key=\"d4\">"
    graphmlLines := graphmlLines.push <| "        <y:ShapeNode>"
    graphmlLines := graphmlLines.push <|
      "          <y:NodeLabel>" ++ xmlEscape (boundaryDisplayName n) ++ "</y:NodeLabel>"
    graphmlLines := graphmlLines.push <|
      "          <y:Shape type=\"" ++ shape ++ "\"/>"
    graphmlLines := graphmlLines.push <| "        </y:ShapeNode>"
    graphmlLines := graphmlLines.push <| "      </data>"
    graphmlLines := graphmlLines.push <| "    </node>"

    nodeIndex := nodeIndex + 1

  let mut edgeIndex : Nat := 0

  -- Exact direct cross-boundary edges: SBI interface -> retained Time node.
  for t in boundaryRootTimeNames do
    if let some timeId := graphmlNodeId? graphNames t then
      for s in (directDeps env sbiAllowed t).toList do
        if let some sbiId := graphmlNodeId? graphNames s then
          graphmlLines := graphmlLines.push <|
            "    <edge id=\"be" ++ toString edgeIndex ++
            "\" source=\"" ++ sbiId ++
            "\" target=\"" ++ timeId ++ "\">"
          graphmlLines := graphmlLines.push <|
            "      <data key=\"d5\">direct checked cross-boundary dependency</data>"
          graphmlLines := graphmlLines.push <|
            "      <data key=\"d6\"></data>"
          graphmlLines := graphmlLines.push <| "      <data key=\"d7\">"
          graphmlLines := graphmlLines.push <| "        <y:PolyLineEdge>"
          graphmlLines := graphmlLines.push <|
            "          <y:Arrows source=\"none\" target=\"standard\"/>"
          graphmlLines := graphmlLines.push <| "        </y:PolyLineEdge>"
          graphmlLines := graphmlLines.push <| "      </data>"
          graphmlLines := graphmlLines.push <| "    </edge>"
          edgeIndex := edgeIndex + 1

  -- Collapsed SBI-internal witness paths: axiom -> directly imported interface.
  for s in visualInterfaceNames do
    if let some interfaceId := graphmlNodeId? graphNames s then
      for a in visualAxiomNames do
        match dependencyPath? env sbiAllowed s a with
        | none =>
            pure ()
        | some path =>
            if !(s == a) then
              if let some axiomId := graphmlNodeId? graphNames a then
                graphmlLines := graphmlLines.push <|
                  "    <edge id=\"be" ++ toString edgeIndex ++
                  "\" source=\"" ++ axiomId ++
                  "\" target=\"" ++ interfaceId ++ "\">"
                graphmlLines := graphmlLines.push <|
                  "      <data key=\"d5\">collapsed checked SBI dependency path</data>"
                graphmlLines := graphmlLines.push <|
                  "      <data key=\"d6\">" ++
                  xmlEscape (renderDependencyPath path) ++
                  "</data>"
                graphmlLines := graphmlLines.push <| "      <data key=\"d7\">"
                graphmlLines := graphmlLines.push <| "        <y:PolyLineEdge>"
                graphmlLines := graphmlLines.push <|
                  "          <y:Arrows source=\"none\" target=\"standard\"/>"
                graphmlLines := graphmlLines.push <| "        </y:PolyLineEdge>"
                graphmlLines := graphmlLines.push <| "      </data>"
                graphmlLines := graphmlLines.push <| "    </edge>"
                edgeIndex := edgeIndex + 1

  graphmlLines := graphmlLines.push "  </graph>"
  graphmlLines := graphmlLines.push "</graphml>"

  let csvText := String.intercalate "\n" csvLines.toList ++ "\n"
  let mdText := String.intercalate "\n" mdLines.toList ++ "\n"
  let graphmlText := String.intercalate "\n" graphmlLines.toList ++ "\n"

  return (csvText, mdText, graphmlText)


syntax (name := timeDependencyReportCmd) "#time_dependency_report" : command

@[command_elab timeDependencyReportCmd]
def elabTimeDependencyReport : CommandElab := fun _ => do
  let env ← getEnv
  let (csvText, mdText, dotText, graphmlText) := generateReports env
  let (spineCsvText, spineMdText, spineGraphmlText) := generateSpineReports env
  let (manuscriptCsvText, manuscriptMdText, manuscriptGraphmlText) :=
    generateManuscriptMapReports env
  let (groupedCsvText, groupedMdText, groupedGraphmlText) :=
    generateGroupedManuscriptMapReports env
  let (boundaryCsvText, boundaryMdText, boundaryGraphmlText) :=
    generateSbiBoundaryReports env

  liftIO <| IO.FS.writeFile "time-dependencies.csv" csvText
  liftIO <| IO.FS.writeFile "time-dependencies.md" mdText
  liftIO <| IO.FS.writeFile "time-dependencies.dot" dotText
  liftIO <| IO.FS.writeFile "time-dependencies.graphml" graphmlText

  liftIO <| IO.FS.writeFile "time-logical-spine.csv" spineCsvText
  liftIO <| IO.FS.writeFile "time-logical-spine.md" spineMdText
  liftIO <| IO.FS.writeFile "time-logical-spine.graphml" spineGraphmlText

  liftIO <| IO.FS.writeFile "time-manuscript-map.csv" manuscriptCsvText
  liftIO <| IO.FS.writeFile "time-manuscript-map.md" manuscriptMdText
  liftIO <| IO.FS.writeFile "time-manuscript-map.graphml" manuscriptGraphmlText

  liftIO <| IO.FS.writeFile "time-grouped-map.csv" groupedCsvText
  liftIO <| IO.FS.writeFile "time-grouped-map.md" groupedMdText
  liftIO <| IO.FS.writeFile "time-grouped-map.graphml" groupedGraphmlText

  liftIO <| IO.FS.writeFile "time-sbi-boundary.csv" boundaryCsvText
  liftIO <| IO.FS.writeFile "time-sbi-boundary.md" boundaryMdText
  liftIO <| IO.FS.writeFile "time-sbi-boundary.graphml" boundaryGraphmlText

  let allowed := reportableProjectDeclSet env
  let retained := spineDeclSet allowed
  let spineNames := retained.toList
  let nDecls := allowed.toList.length
  let nSpine := spineNames.length
  let nSpineEdges := countRetainedEdges spineNames (fun n => manuscriptSpineDeps env allowed retained n)
  let nReducedEdges := countRetainedEdges spineNames (fun n => transitiveReducedSpineDeps env allowed retained n)
  let presentGroups := presentManuscriptGroups retained
  let nGroups := presentGroups.length
  let nGroupEdges :=
    presentGroups.foldl
      (fun total g =>
        total +
          (transitiveReducedManuscriptGroupDeps
            env allowed retained g).length)
      0

  -- Validate the human-supplied grouping against the current retained spine.
  -- This does not affect the graph; it only prevents silent drift between
  -- manuscript grouping and the Lean declaration set.
  for n in spineNames do
    let count := manuscriptGroupMembershipCount n
    if count == 0 then
      logWarning m!"Ungrouped manuscript-spine declaration: {n}"
    else if count > 1 then
      logWarning m!"Declaration belongs to more than one manuscript group: {n}"

  for g in presentManuscriptGroups retained do
    if (retainedInterfacesOfGroup retained g).isEmpty then
      logWarning m!"Conceptual manuscript group has no retained interface declaration: {g.label}"

  -- A cycle can arise after quotienting an acyclic declaration graph when
  -- declarations assigned to two conceptual groups interleave logically.
  -- Such a cycle is a useful warning that the chosen grouping does not match
  -- a clean proof-stage decomposition.
  for g in presentGroups do
    let hasCycle :=
      (manuscriptGroupDirectDeps env allowed retained g).any fun dependencyId =>
        manuscriptGroupReachable env allowed retained dependencyId g.id
    if hasCycle then
      logWarning m!"Conceptual manuscript grouping produces a cycle involving group: {g.label}"

  logInfo m!"Time dependency reports written: {nDecls} audit declarations, {nSpine} logical-spine declarations, {nSpineEdges} collapsed-spine edges, {nReducedEdges} transitively reduced manuscript-map edges, {nGroups} conceptual proof groups, {nGroupEdges} reduced group edges.\n  time-dependencies.csv\n  time-dependencies.md\n  time-dependencies.dot\n  time-dependencies.graphml\n  time-logical-spine.csv\n  time-logical-spine.md\n  time-logical-spine.graphml\n  time-manuscript-map.csv\n  time-manuscript-map.md\n  time-manuscript-map.graphml\n  time-grouped-map.csv\n  time-grouped-map.md\n  time-grouped-map.graphml\n  time-sbi-boundary.csv\n  time-sbi-boundary.md\n  time-sbi-boundary.graphml"

end TimeDependencyReport

-- Run the report when this file is elaborated directly.
#time_dependency_report
