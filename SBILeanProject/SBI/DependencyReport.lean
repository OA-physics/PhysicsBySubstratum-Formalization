import SBILeanProject.SBI.Defects
import Lean
import Lean.Elab.Command
import Lean.Util.FoldConsts

set_option autoImplicit false

open Lean Elab Command

namespace SBIDependencyReport

/--
All imported modules below this prefix are treated as part of the SBI project.
Because `DependencyReport.lean` imports `Defects.lean`, this automatically picks
up the complete current dependency chain Basic -> ... -> Defects.
-/
def projectModulePrefix : Name := `SBILeanProject.SBI

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
below `SBILeanProject.SBI`.
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

/-- User-facing SBI declarations only. -/
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
Direct kernel-level dependencies of `n`, restricted to user-facing SBI
project declarations. Both the declaration's type and its checked body/proof
are inspected.
-/
/-
Direct kernel-level dependencies of `n`, restricted to user-facing SBI
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
  -- Axioms / primitive support
  "A1", "A1_relational_support", "A2", "A3",

  -- Substratum
  "CoAccess", "EmbeddedObserver", "RelConnected", "one_substratum",
  "AccessibleFamily", "ObserverSubstratum", "observerSubstratum_connected",
  "substratum_theorem",

  -- Network / FOA
  "accessible_has_establishment", "finite_operational_accessibility",
  "MediationChain", "DirectMediationChain",
  "ConnectionEstablishmentCoherent", "ObserverRelConnected",
  "OperationalResolutionOfRelConnected", "observerSubstratum_is_operationallyConnected", "finite_mediation_witness",
  "mediationChain_is_direct",
  "IsDirectRelation", "DirectRelation",
  "IsLocalRelationalConjunction", "LocalRelationalConjunction",
  "Incident", "IncidenceNetwork", "ObserverNetwork",
  "ObserverDirectMediationChain", "SharedMediationAccessible",
  "OperationalConnectionWitness", "OperationalConnectionSemantics",
  "finite_observer_local_mediation",

  -- Retained because it is a recognizable manuscript proof step: a finite
  -- operational connection is realized as an incidence chain in the bundled
  -- ObserverNetwork before the Network Representation Theorem is stated.
  "NetworkIncidenceChain",
  "network_representation_theorem",

  -- Local relational configuration / operational local finiteness
  --
  -- `Restrict`, `LocalRestriction`, and `localRestriction_is_admissible`
  -- formalize the restriction clause of manuscript Definition 5.  They are
  -- deliberately omitted from the reduced manuscript spine because that
  -- clause establishes the consistency of the local notation but is not used
  -- as a downstream premise of the persistence/frustration argument.
  --
  -- The local configuration space and its admissible subset *are* used
  -- downstream, so their manuscript-facing declarations remain retained.
  "OperationalContext", "GlobalConfig", "LocalConfig",
  "AdmissibleLocal", "IsAdmissibleLocal",
  "FOAWitness", "IsOperationalConjunction", "OperationalConjunction",
  "OperationallyLocallyFinite", "LocalConfigurationsRepresentedByAlternatives",
  "operational_domain_is_locallyFinite",

  -- Persistence
  "PersistenceContext", "PersistenceClassPresent", "PersistentStructuresPresent",
  "OperationallyReidentified", "OperationalSupport",
  "operationallyReidentified_has_finiteSupport",
  "LocalPersistenceSemantics", "PersistencePreservingLocal",
  "PersistenceRestrictsLocally",

  -- `persistenceRestrictsLocally_excludes_admissible` remains in Lean as an
  -- explanatory proper-subset lemma but is omitted here because it is not a
  -- downstream premise in the manuscript proof.
  "RelationalAdaptation", "NonIncidentConjunctions",
  "ConjunctionDomainSemantics", "AdaptationInductionSemantics",
  "localPropagation_of_relationalAdaptation",

  -- Frustration / reorganization
  "LocalPersistenceRequirement", "SatisfiesPersistenceRequirement",
  "SatisfiesAllRequirements", "FiniteLocalStructuralFrustration",
  "FullRequirementFamily",
  "SatisfiesFullRequirementFamily", "FullLocalIncompatibility",
  "IsFiniteSubfamily", "IsFiniteFrustrationWitness",
  "fullIncompatibility_has_finiteWitness", "LocalPersistenceSituation",
  "SameRequirementFamily", "RelationalReorganization",
  "SituationPreservesRequirements", "frustration_requires_reorganization",
  "ReorganizationMediationSemantics",
  "reorganizationRealization_is_locallyMediated",
  "frustration_persistence_requires_localReorganization",
  "FrustrationReorganizationEpisode", "RecurrentStructuralFrustration",
  "recurrentFrustration_requires_continualReorganization",

  -- Deformation / defects
  "ConfigurationChangeSemantics",
  "AdmissibleDeformation", "PersistencePreservingDeformation",
  "EssentialToReidentification", "realization_independence",
  "LocalDeformationSemantics", "ContextPreservingLocalStep",
  "ContextPreservingLocalDeformation", "LocallyNonEliminable",
  "OperationallyReidentifiableAt", "PersistentRelationalDefect",
  "persistentRelationalDefect_has_finiteOperationalSupport",
  "persistentRelationalDefect_identifyingProperty_invariant",
  "persistentRelationalDefect_is_locallyNonEliminable",

  -- The former `PersistentDefectCharacterization` packaging structure has
  -- been removed from Defects.lean.  The public theorem now states the three
  -- manuscript conclusions directly.
  "persistentRelationalDefect_characterization"
]

/-- Declarations retained in the reduced logical-spine graph. -/
def spineDeclSet (allowed : NameSet) : NameSet :=
  allowed.filter fun n =>
    spineShortNames.any fun s => s == shortNameString n

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
def manuscriptSemanticInputShortNames : List String := [
  "accessible_has_establishment"
]

/-- True for a declaration treated as a semantic input in the reduced map. -/
def isManuscriptSemanticInput (n : Name) : Bool :=
  manuscriptSemanticInputShortNames.any fun s =>
    s == shortNameString n

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
    "# SBI Lean dependency report",
    "",
    "Direct dependencies are constants occurring in the checked declaration type or body/proof, filtered to user-facing declarations in imported `SBILeanProject.SBI.*` modules.",
    "",
    "| Declaration | Module | Kind | Direct SBI dependencies | Transitive SBI dependencies |",
    "|---|---|---|---|---|"
  ]

  let mut dotLines : Array String := #[
    "digraph SBI_Dependencies {",
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
    "declaration,module,kind,collapsed_principal_dependencies"
  ]

  let mut mdLines : Array String := #[
    "# SBI Lean logical-spine dependency report",
    "",
    "This is a reduced quotient of the checked Lean dependency graph. Suppressed implementation declarations are collapsed; each listed dependency is the nearest retained declaration reached along a project-local dependency path.",
    "",
    "| Declaration | Module | Kind | Principal Lean-derived dependencies |",
    "|---|---|---|---|"
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
      let deps := manuscriptSpineDeps env allowed retained n
      let modName :=
        match moduleNameOf? env n with
        | some m => toString m
        | none   => "<unknown>"
      let k := kindString ci
      let nS := toString n
      let depsS := renderNames deps

      csvLines := csvLines.push <|
        String.intercalate "," [csv nS, csv modName, csv k, csv depsS]

      mdLines := mdLines.push <|
        "| `" ++ nS ++ "` | `" ++ modName ++ "` | " ++ k ++
        " | " ++ depsS ++ " |"

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

  -- Presentation direction: dependency -> dependent.
  let mut edgeIndex : Nat := 0
  for dependent in names do
    if let some dependentId := graphmlNodeId? names dependent then
      for dependency in (manuscriptSpineDeps env allowed retained dependent).toList do
        if let some dependencyId := graphmlNodeId? names dependency then
          graphmlLines := graphmlLines.push <|
            "    <edge id=\"e" ++ toString edgeIndex ++ "\" source=\"" ++
            dependencyId ++ "\" target=\"" ++ dependentId ++ "\">"
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
  let names := retained.toList

  let mut csvLines : Array String := #[
    "declaration,module,kind,transitively_reduced_principal_dependencies"
  ]

  let mut mdLines : Array String := #[
    "# SBI manuscript dependency map",
    "",
    "This map is derived from the checked Lean dependency graph in two steps: suppressed implementation declarations are first collapsed, and then transitively redundant edges are removed from the retained DAG.",
    "",
    "If `A -> B`, `B -> C`, and `A -> C` are all present in logical-flow direction, the direct `A -> C` edge is omitted because its dependency is already represented through `B`.",
    "",
    "| Declaration | Module | Kind | Transitively reduced principal dependencies |",
    "|---|---|---|---|"
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
      let deps := transitiveReducedSpineDeps env allowed retained n
      let modName :=
        match moduleNameOf? env n with
        | some m => toString m
        | none   => "<unknown>"
      let k := kindString ci
      let nS := toString n
      let depsS := renderNames deps

      csvLines := csvLines.push <|
        String.intercalate "," [csv nS, csv modName, csv k, csv depsS]

      mdLines := mdLines.push <|
        "| `" ++ nS ++ "` | `" ++ modName ++ "` | " ++ k ++
        " | " ++ depsS ++ " |"

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

  -- Presentation direction: dependency -> dependent.
  let mut edgeIndex : Nat := 0
  for dependent in names do
    if let some dependentId := graphmlNodeId? names dependent then
      for dependency in (transitiveReducedSpineDeps env allowed retained dependent).toList do
        if let some dependencyId := graphmlNodeId? names dependency then
          graphmlLines := graphmlLines.push <|
            "    <edge id=\"e" ++ toString edgeIndex ++ "\" source=\"" ++
            dependencyId ++ "\" target=\"" ++ dependentId ++ "\">"
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
  let mdText := String.intercalate "\n" mdLines.toList ++ "\n"
  let graphmlText := String.intercalate "\n" graphmlLines.toList ++ "\n"

  return (csvText, mdText, graphmlText)


/-
===============================================================================
GROUPED MANUSCRIPT MAP
===============================================================================

The declaration-level manuscript map is deliberately retained as an audit
layer.  The grouped map below adds a second, coarser representation whose
nodes correspond to recognizable proof steps in Supplementary Discussion S2.

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
    id := "a1-relational-closure"
    label := "A1 — Relational closure"
    members := ["A1", "A1_relational_support"]
    interfaces := ["A1", "A1_relational_support"]
  },
  {
    id := "a2-local-mediation"
    label := "A2 — Local mediation"
    members := ["A2"]
    interfaces := ["A2"]
  },
  {
    id := "a3-persistence"
    label := "A3 — Persistence"
    members := ["A3"]
    interfaces := ["A3"]
  },
  {
    id := "substratum"
    label := "Observer-accessible substratum"
    members := [
      "CoAccess", "EmbeddedObserver", "RelConnected", "one_substratum",
      "AccessibleFamily", "ObserverSubstratum",
      "observerSubstratum_connected", "substratum_theorem"
    ]
    interfaces := ["substratum_theorem"]
  },
  {
    id := "operational-accessibility"
    label := "Operational accessibility"
    members := ["accessible_has_establishment"]
    interfaces := ["accessible_has_establishment"]
  },
  {
    id := "finite-operational-accessibility"
    label := "Finite operational accessibility"
    members := ["finite_operational_accessibility"]
    interfaces := ["finite_operational_accessibility"]
  },
  {
    id := "resolved-connectivity"
    label := "Operationally resolved connectivity"
    members := [
      "ObserverRelConnected", "OperationalResolutionOfRelConnected",
      "observerSubstratum_is_operationallyConnected"
    ]
    interfaces := ["observerSubstratum_is_operationallyConnected"]
  },
  {
    id := "connection-semantics"
    label := "Operational connection semantics"
    members := [
      "MediationChain", "DirectMediationChain",
      "ConnectionEstablishmentCoherent",
      "SharedMediationAccessible",
      "OperationalConnectionWitness", "OperationalConnectionSemantics"
    ]
    interfaces := ["OperationalConnectionSemantics"]
  },
  {
    id := "finite-local-mediation"
    label := "Finite observer-local mediation"
    members := [
      "finite_mediation_witness", "mediationChain_is_direct",
      "ObserverDirectMediationChain",
      "finite_observer_local_mediation"
    ]
    interfaces := ["finite_observer_local_mediation"]
  },
  {
    id := "network-representation"
    label := "Incidence-network representation"
    members := [
      "IsDirectRelation", "DirectRelation",
      "IsLocalRelationalConjunction", "LocalRelationalConjunction",
      "Incident", "IncidenceNetwork", "ObserverNetwork",
      "NetworkIncidenceChain",
      "network_representation_theorem"
    ]
    interfaces := ["network_representation_theorem"]
  },
  {
    id := "local-relational-configuration"
    label := "Local relational configuration"
    members := [
      "OperationalContext", "GlobalConfig", "LocalConfig",
      "AdmissibleLocal", "IsAdmissibleLocal",

      -- Internal Lean support for the restriction clause of S2 Definition 5.
      -- These declarations are intentionally not retained as separate nodes
      -- in the manuscript-level declaration graph.
      "LocalRestriction", "localRestriction_is_admissible"
    ]
    interfaces := ["LocalConfig", "IsAdmissibleLocal"]
  },
  {
    id := "operational-local-finiteness"
    label := "Operational local finiteness"
    members := [
      "FOAWitness", "IsOperationalConjunction", "OperationalConjunction",
      "OperationallyLocallyFinite",
      "LocalConfigurationsRepresentedByAlternatives",
      "operational_domain_is_locallyFinite"
    ]
    interfaces := ["operational_domain_is_locallyFinite"]
  },
  {
    id := "persistent-support"
    label := "Persistent structures and finite support"
    members := [
      "PersistenceContext", "PersistenceClassPresent",
      "PersistentStructuresPresent", "OperationallyReidentified",
      "OperationalSupport", "operationallyReidentified_has_finiteSupport"
    ]
    interfaces := ["operationallyReidentified_has_finiteSupport"]
  },
  {
    id := "local-persistence"
    label := "Local persistence and adaptation"
    members := [
      "LocalPersistenceSemantics", "PersistencePreservingLocal",
      "PersistenceRestrictsLocally",

      -- Internal explanatory support for the proper-subset interpretation of
      -- local persistence restriction.  The theorem is not retained as a
      -- separate manuscript-level node because no downstream proof step uses
      -- it as a premise.
      "persistenceRestrictsLocally_excludes_admissible",

      "RelationalAdaptation", "NonIncidentConjunctions",
      "ConjunctionDomainSemantics", "AdaptationInductionSemantics",
      "localPropagation_of_relationalAdaptation"
    ]
    interfaces := [
      "PersistencePreservingLocal",
      "LocalPersistenceSemantics",
      "localPropagation_of_relationalAdaptation"
    ]
  },
  {
    id := "structural-frustration"
    label := "Structural frustration"
    members := [
      "LocalPersistenceRequirement", "SatisfiesPersistenceRequirement",
      "SatisfiesAllRequirements", "FiniteLocalStructuralFrustration",
      "FullRequirementFamily", "SatisfiesFullRequirementFamily",
      "FullLocalIncompatibility", "IsFiniteSubfamily",
      "IsFiniteFrustrationWitness", "fullIncompatibility_has_finiteWitness"
    ]
    interfaces := [
      "FiniteLocalStructuralFrustration",
      "fullIncompatibility_has_finiteWitness"
    ]
  },
  {
    id := "required-reorganization"
    label := "Required reorganization"
    members := [
      "LocalPersistenceSituation", "SameRequirementFamily",
      "RelationalReorganization", "SituationPreservesRequirements",
      "frustration_requires_reorganization",
      "ReorganizationMediationSemantics",
      "reorganizationRealization_is_locallyMediated",
      "frustration_persistence_requires_localReorganization"
    ]
    interfaces := [
      "frustration_persistence_requires_localReorganization",
      "reorganizationRealization_is_locallyMediated"
    ]
  },
  {
    id := "continual-reorganization"
    label := "Continual reorganization"
    members := [
      "FrustrationReorganizationEpisode", "RecurrentStructuralFrustration",
      "recurrentFrustration_requires_continualReorganization"
    ]
    interfaces := ["recurrentFrustration_requires_continualReorganization"]
  },
  {
    id := "admissible-deformation"
    label := "Admissible deformation"
    members := [
      "ConfigurationChangeSemantics", "AdmissibleDeformation",
      "PersistencePreservingDeformation", "EssentialToReidentification",
      "realization_independence", "LocalDeformationSemantics",
      "ContextPreservingLocalStep", "ContextPreservingLocalDeformation"
    ]
    interfaces := [
      "PersistencePreservingDeformation",
      "realization_independence",
      "ContextPreservingLocalDeformation"
    ]
  },
  {
    id := "persistent-defects"
    label := "Persistent relational defects"
    members := [
      "LocallyNonEliminable", "OperationallyReidentifiableAt",
      "PersistentRelationalDefect",
      "persistentRelationalDefect_has_finiteOperationalSupport",
      "persistentRelationalDefect_identifyingProperty_invariant",
      "persistentRelationalDefect_is_locallyNonEliminable",
      "persistentRelationalDefect_characterization"
    ]
    interfaces := ["persistentRelationalDefect_characterization"]
  }
]

/-- True when declaration `n` is assigned to conceptual group `g`. -/
def manuscriptGroupContains (g : ManuscriptGroup) (n : Name) : Bool :=
  g.members.any fun s => s == shortNameString n

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
    g.interfaces.any fun s => s == shortNameString n

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
    "# SBI grouped manuscript proof map",
    "",
    "This is a conceptual quotient of the declaration-level manuscript map.",
    "Group membership is supplied explicitly to match the proof structure of Supplementary Discussion S2; all edges between groups are derived from checked Lean declaration dependencies.",
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


syntax (name := sbiDependencyReportCmd) "#sbi_dependency_report" : command

@[command_elab sbiDependencyReportCmd]
def elabSBIDependencyReport : CommandElab := fun _ => do
  let env ← getEnv
  let (csvText, mdText, dotText, graphmlText) := generateReports env
  let (spineCsvText, spineMdText, spineGraphmlText) := generateSpineReports env
  let (manuscriptCsvText, manuscriptMdText, manuscriptGraphmlText) :=
    generateManuscriptMapReports env
  let (groupedCsvText, groupedMdText, groupedGraphmlText) :=
    generateGroupedManuscriptMapReports env

  liftIO <| IO.FS.writeFile "sbi-dependencies.csv" csvText
  liftIO <| IO.FS.writeFile "sbi-dependencies.md" mdText
  liftIO <| IO.FS.writeFile "sbi-dependencies.dot" dotText
  liftIO <| IO.FS.writeFile "sbi-dependencies.graphml" graphmlText

  liftIO <| IO.FS.writeFile "sbi-logical-spine.csv" spineCsvText
  liftIO <| IO.FS.writeFile "sbi-logical-spine.md" spineMdText
  liftIO <| IO.FS.writeFile "sbi-logical-spine.graphml" spineGraphmlText

  liftIO <| IO.FS.writeFile "sbi-manuscript-map.csv" manuscriptCsvText
  liftIO <| IO.FS.writeFile "sbi-manuscript-map.md" manuscriptMdText
  liftIO <| IO.FS.writeFile "sbi-manuscript-map.graphml" manuscriptGraphmlText

  liftIO <| IO.FS.writeFile "sbi-grouped-map.csv" groupedCsvText
  liftIO <| IO.FS.writeFile "sbi-grouped-map.md" groupedMdText
  liftIO <| IO.FS.writeFile "sbi-grouped-map.graphml" groupedGraphmlText

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

  logInfo m!"SBI dependency reports written: {nDecls} audit declarations, {nSpine} logical-spine declarations, {nSpineEdges} collapsed-spine edges, {nReducedEdges} transitively reduced manuscript-map edges, {nGroups} conceptual proof groups, {nGroupEdges} reduced group edges.\n  sbi-dependencies.csv\n  sbi-dependencies.md\n  sbi-dependencies.dot\n  sbi-dependencies.graphml\n  sbi-logical-spine.csv\n  sbi-logical-spine.md\n  sbi-logical-spine.graphml\n  sbi-manuscript-map.csv\n  sbi-manuscript-map.md\n  sbi-manuscript-map.graphml\n  sbi-grouped-map.csv\n  sbi-grouped-map.md\n  sbi-grouped-map.graphml"

end SBIDependencyReport

-- Run the report when this file is elaborated directly.
#sbi_dependency_report
