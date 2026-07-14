import Lean.Server.References
import Lean.Util.FoldConsts

import ProvableComputation.LinearAlgebra.Echelon
import ProvableComputation.LinearAlgebra.GaussianElimination.Defs
import ProvableComputation.LinearAlgebra.GaussianElimination.Elementary
import ProvableComputation.LinearAlgebra.GaussianElimination.Pivot
import ProvableComputation.LinearAlgebra.GaussianElimination.Rref
import ProvableComputation.LinearAlgebra.GaussianElimination.RrefCorrectness
import ProvableComputation.LinearAlgebra.GaussianElimination.RrefUniqueness
import ProvableComputation.LinearAlgebra.LU.Basic
import ProvableComputation.LinearAlgebra.LU.Correctness

/-!
# Gaussian dependency graph generator

This executable builds a declaration-level dependency graph for the current Echelon and
Gaussian-elimination sources.  LU modules are summarized as downstream boundary nodes.
-/

open Lean System
open Lean.Lsp Lean.Server

namespace GaussianDependencyGraph

structure ModuleSpec where
  name : Name
  source : String
  label : String
deriving Inhabited

def coreModules : Array ModuleSpec := #[
  { name := `ProvableComputation.LinearAlgebra.Echelon
    source := "ProvableComputation/LinearAlgebra/Echelon.lean"
    label := "Echelon" },
  { name := `ProvableComputation.LinearAlgebra.GaussianElimination.Defs
    source := "ProvableComputation/LinearAlgebra/GaussianElimination/Defs.lean"
    label := "GaussianElimination.Defs" },
  { name := `ProvableComputation.LinearAlgebra.GaussianElimination.Rref
    source := "ProvableComputation/LinearAlgebra/GaussianElimination/Rref.lean"
    label := "GaussianElimination.Rref" },
  { name := `ProvableComputation.LinearAlgebra.GaussianElimination.Elementary
    source := "ProvableComputation/LinearAlgebra/GaussianElimination/Elementary.lean"
    label := "GaussianElimination.Elementary" },
  { name := `ProvableComputation.LinearAlgebra.GaussianElimination.Pivot
    source := "ProvableComputation/LinearAlgebra/GaussianElimination/Pivot.lean"
    label := "GaussianElimination.Pivot" },
  { name := `ProvableComputation.LinearAlgebra.GaussianElimination.RrefCorrectness
    source := "ProvableComputation/LinearAlgebra/GaussianElimination/RrefCorrectness.lean"
    label := "GaussianElimination.RrefCorrectness" },
  { name := `ProvableComputation.LinearAlgebra.GaussianElimination.RrefUniqueness
    source := "ProvableComputation/LinearAlgebra/GaussianElimination/RrefUniqueness.lean"
    label := "GaussianElimination.RrefUniqueness" }
]

def luBasicModule : ModuleSpec :=
  { name := `ProvableComputation.LinearAlgebra.LU.Basic
    source := "ProvableComputation/LinearAlgebra/LU/Basic.lean"
    label := "LU.Basic" }

def luCorrectnessModule : ModuleSpec :=
  { name := `ProvableComputation.LinearAlgebra.LU.Correctness
    source := "ProvableComputation/LinearAlgebra/LU/Correctness.lean"
    label := "LU.Correctness" }

def importedModules : Array Name :=
  (coreModules.map (·.name)).push luBasicModule.name |>.push luCorrectnessModule.name

inductive DependencyKind where
  | signature
  | body
  | metadata
deriving BEq, DecidableEq, Inhabited, Repr

def DependencyKind.label : DependencyKind → String
  | .signature => "signature"
  | .body => "body"
  | .metadata => "metadata"

def dependencyKinds : Array DependencyKind := #[.signature, .body, .metadata]

structure SourceDecl where
  rawName : Name
  userName : Name
  module : ModuleSpec
  kind : String
  line : Nat
deriving Inhabited

def SourceDecl.visibility (decl : SourceDecl) : String :=
  if isPrivateName decl.rawName then "private" else "public"

def SourceDecl.id (decl : SourceDecl) : String :=
  if isPrivateName decl.rawName then
    decl.rawName.toString
  else
    decl.userName.toString

structure Dependency where
  consumer : Name
  dependency : Name
  kinds : Array DependencyKind := #[]
  viaGenerated : Bool := false
  direct : Bool := false
deriving Inhabited

def Dependency.addKind (edge : Dependency) (kind : DependencyKind) : Dependency :=
  if edge.kinds.contains kind then edge else { edge with kinds := edge.kinds.push kind }

def addDependency (edges : Array Dependency) (consumer dependency : Name)
    (kind : DependencyKind) (viaGenerated : Bool) : Array Dependency :=
  match edges.findIdx? (fun edge => edge.consumer == consumer && edge.dependency == dependency) with
  | none => edges.push {
      consumer, dependency, kinds := #[kind], viaGenerated, direct := !viaGenerated }
  | some index =>
      let edge := edges[index]!
      edges.set! index { edge.addKind kind with
        viaGenerated := edge.viaGenerated || viaGenerated
        direct := edge.direct || !viaGenerated }

def moduleConstants (env : Environment) (moduleName : Name) : IO (Array Name) := do
  let some index := env.getModuleIdx? moduleName
    | throw <| IO.userError s!"module is not loaded: {moduleName}"
  return env.header.moduleData[index.toNat]!.constNames

def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def positionLe (left right : Lsp.Position) : Bool :=
  left.line < right.line || (left.line == right.line && left.character ≤ right.character)

def rangeContains (outer inner : Lsp.Range) : Bool :=
  positionLe outer.start inner.start && positionLe inner.«end» outer.«end»

structure IntroducedDecl where
  name : Name
  info : DeclInfo

def topLevelDeclarations (constants : Array Name) (ilean : Ilean) : IO (Array IntroducedDecl) := do
  let mut all := #[]
  for (rawName, info) in ilean.decls.toList do
    let candidates := constants.filter fun name => name.toString == rawName
    if candidates.size != 1 then
      throw <| IO.userError <|
        s!"expected one compiled constant for .ilean key {rawName}, found {candidates.toList}"
    all := all.push { name := candidates[0]!, info }
  return all.filter (fun candidate =>
      !all.any fun other =>
        other.name != candidate.name && other.info.range != candidate.info.range &&
          rangeContains other.info.range candidate.info.range)
    |>.qsort fun left right =>
      left.info.selectionRange.start.line < right.info.selectionRange.start.line ||
        (left.info.selectionRange.start.line == right.info.selectionRange.start.line &&
          (left.info.selectionRange.start.character < right.info.selectionRange.start.character ||
            (left.info.selectionRange.start.character ==
                right.info.selectionRange.start.character &&
              left.name.toString < right.name.toString)))

def parseSourceDeclarations (env : Environment)
    (module : ModuleSpec) : IO (Array SourceDecl) := do
  let oleanPath ← findOLean module.name
  let ilean ← Ilean.load <| oleanPath.withExtension "ilean"
  unless ilean.module == module.name do
    throw <| IO.userError s!"wrong .ilean module: expected {module.name}, got {ilean.module}"
  let constants ← moduleConstants env module.name
  let mut declarations := #[]
  for entry in ← topLevelDeclarations constants ilean do
    let some compiledInfo := env.find? entry.name
      | throw <| IO.userError s!".ilean declaration is absent from compiled output: {entry.name}"
    let some moduleIndex := env.getModuleIdxFor? entry.name
      | throw <| IO.userError s!"compiled declaration has no module: {entry.name}"
    let compiledModule := env.header.moduleNames[moduleIndex.toNat]!
    unless compiledModule == module.name do
      throw <| IO.userError <|
        s!"compiled declaration {entry.name} belongs to {compiledModule}, not {module.name}"
    declarations := declarations.push {
      rawName := entry.name
      userName := privateToUserName entry.name
      module
      kind := constantKind compiledInfo
      line := entry.info.selectionRange.start.line + 1
    }
  return declarations

def parseModules (env : Environment) (modules : Array ModuleSpec) : IO (Array SourceDecl) := do
  let mut declarations := #[]
  for module in modules do
    declarations := declarations ++ (← parseSourceDeclarations env module)
  return declarations

def namesOf (declarations : Array SourceDecl) : NameSet :=
  declarations.foldl (init := {}) fun names declaration => names.insert declaration.rawName

def constantsOf (env : Environment) (modules : Array ModuleSpec) : IO NameSet := do
  let mut constants : NameSet := {}
  for module in modules do
    for name in ← moduleConstants env module.name do
      constants := constants.insert name
  return constants

def insertNames (names : NameSet) (newNames : List Name) : NameSet :=
  newNames.foldl (init := names) NameSet.insert

def metadataReferences : ConstantInfo → NameSet
  | .inductInfo value => insertNames {} value.ctors
  | .recInfo value => insertNames {} value.all
  | _ => {}

def referencesForKind (constant : ConstantInfo) : DependencyKind → NameSet
  | .signature => constant.type.getUsedConstantsAsSet
  | .body =>
      match constant.value? (allowOpaque := true) with
      | some value => value.getUsedConstantsAsSet
      | none => {}
  | .metadata => metadataReferences constant

def allReferences (constant : ConstantInfo) : NameSet :=
  dependencyKinds.foldl (init := {}) fun names kind => names ++ referencesForKind constant kind

partial def findPrimaryTargets (env : Environment) (primary scopedNames visited : NameSet)
    (name : Name) (viaGenerated : Bool) : Array (Name × Bool) :=
  if primary.contains name then
    #[(name, viaGenerated)]
  else if visited.contains name || !scopedNames.contains name then
    #[]
  else
    match env.find? name with
    | none => #[]
    | some constant =>
        let visited := visited.insert name
        (allReferences constant).toList.foldl (init := #[]) fun targets reference =>
          targets ++ findPrimaryTargets env primary scopedNames visited reference true

def collectDependencies (env : Environment) (roots : Array SourceDecl)
    (primary scopedNames : NameSet) : Array Dependency := Id.run do
  let mut edges := #[]
  for root in roots do
    let some constant := env.find? root.rawName
      | panic! s!"missing declaration after source matching: {root.rawName}"
    for kind in dependencyKinds do
      for reference in (referencesForKind constant kind).toList do
        for (target, viaGenerated) in
            findPrimaryTargets env primary scopedNames {} reference false do
          if target != root.rawName then
            edges := addDependency edges root.rawName target kind viaGenerated
  return edges

def luBasicBoundaryName : Name := `GaussianDependencyGraph.Boundary.LUBasic

def luCorrectnessBoundaryName : Name := `GaussianDependencyGraph.Boundary.LUCorrectness

def aggregateBoundaryDependencies (edges : Array Dependency) (consumer : Name)
    (allowedDependencies : NameSet) : Array Dependency :=
  edges.foldl (init := #[]) fun aggregated edge =>
    if allowedDependencies.contains edge.dependency then
      edge.kinds.foldl (init := aggregated) fun result kind =>
        addDependency result consumer edge.dependency kind edge.viaGenerated
    else
      aggregated

def aggregateModuleBoundaryDependency (edges : Array Dependency) (consumer dependency : Name)
    (moduleDeclarations : NameSet) : Array Dependency :=
  edges.foldl (init := #[]) fun aggregated edge =>
    if moduleDeclarations.contains edge.dependency then
      edge.kinds.foldl (init := aggregated) fun result kind =>
        addDependency result consumer dependency kind edge.viaGenerated
    else
      aggregated

def findSourceDecl? (declarations : Array SourceDecl) (rawName : Name) : Option SourceDecl :=
  declarations.find? fun declaration => declaration.rawName == rawName

def nodeId (declarations : Array SourceDecl) (name : Name) : String :=
  if name == luBasicBoundaryName then
    "boundary:LU.Basic"
  else if name == luCorrectnessBoundaryName then
    "boundary:LU.Correctness"
  else
    match findSourceDecl? declarations name with
    | some declaration => declaration.id
    | none => panic! s!"missing graph node for {name}"

def validateGraph (declarations : Array SourceDecl) (edges : Array Dependency) : IO Unit := do
  let ids := (declarations.map SourceDecl.id).push "boundary:LU.Basic"
    |>.push "boundary:LU.Correctness"
  for id in ids do
    unless ids.countP (· == id) == 1 do
      throw <| IO.userError s!"duplicate graph node id: {id}"
  let allowedNames := namesOf declarations |>.insert luBasicBoundaryName
    |>.insert luCorrectnessBoundaryName
  for edge in edges do
    unless allowedNames.contains edge.consumer do
      throw <| IO.userError s!"edge consumer has no graph node: {edge.consumer}"
    unless allowedNames.contains edge.dependency do
      throw <| IO.userError s!"edge dependency has no graph node: {edge.dependency}"
    if edge.kinds.isEmpty then
      throw <| IO.userError s!"edge has no dependency kind: {edge.dependency} -> {edge.consumer}"
    unless edges.countP (fun candidate =>
        candidate.consumer == edge.consumer && candidate.dependency == edge.dependency) == 1 do
      throw <| IO.userError s!"duplicate graph edge: {edge.dependency} -> {edge.consumer}"

def sourceUrl (revision source : String) (line : Nat) : String :=
  s!"https://github.com/uw-math-ai/provable_computation/blob/{revision}/{source}#L{line}"

def sourceNodeJson (revision : String) (declaration : SourceDecl) : Json :=
  Json.mkObj [
    ("id", declaration.id),
    ("displayName", declaration.userName.toString),
    ("module", declaration.module.label),
    ("kind", declaration.kind),
    ("visibility", declaration.visibility),
    ("source", declaration.module.source),
    ("line", declaration.line),
    ("sourceUrl", sourceUrl revision declaration.module.source declaration.line),
    ("boundary", false)
  ]

def boundaryNodeJson (revision : String) (module : ModuleSpec) (id : String) : Json :=
  Json.mkObj [
    ("id", id),
    ("displayName", s!"{module.label} downstream consumers"),
    ("module", module.label),
    ("kind", "boundary"),
    ("visibility", "public"),
    ("source", module.source),
    ("line", 1),
    ("sourceUrl", sourceUrl revision module.source 1),
    ("boundary", true)
  ]

def edgeJson (declarations : Array SourceDecl) (edge : Dependency) : Json :=
  Json.mkObj [
    ("source", nodeId declarations edge.dependency),
    ("target", nodeId declarations edge.consumer),
    ("kinds", Json.arr <| edge.kinds.map fun kind => Json.str kind.label),
    ("viaGenerated", edge.viaGenerated),
    ("direct", edge.direct)
  ]

def graphJson (revision : String) (declarations : Array SourceDecl)
    (edges : Array Dependency) : Json :=
  let edges := edges.qsort fun left right =>
    let leftSource := nodeId declarations left.dependency
    let rightSource := nodeId declarations right.dependency
    leftSource < rightSource ||
      (leftSource == rightSource &&
        nodeId declarations left.consumer < nodeId declarations right.consumer)
  let publicCount := declarations.countP fun declaration => !isPrivateName declaration.rawName
  let privateCount := declarations.size - publicCount
  let nodes := (declarations.map <| sourceNodeJson revision) ++ #[
    boundaryNodeJson revision luBasicModule "boundary:LU.Basic",
    boundaryNodeJson revision luCorrectnessModule "boundary:LU.Correctness"
  ]
  Json.mkObj [
    ("metadata", Json.mkObj [
      ("schemaVersion", "1.0.0"),
      ("commit", revision),
      ("edgeDirection", "dependency-to-consumer"),
      ("viaGeneratedMeaning", "at-least-one-collapsed-path"),
      ("scope", Json.mkObj [
        ("coreModules", Json.arr <| coreModules.map fun module => Json.str module.name.toString),
        ("boundaryModules", Json.arr <| #[luBasicModule, luCorrectnessModule].map fun module =>
          Json.str module.name.toString)
      ]),
      ("counts", Json.mkObj [
        ("sourceDeclarations", declarations.size),
        ("publicDeclarations", publicCount),
        ("privateDeclarations", privateCount),
        ("boundaryNodes", 2),
        ("edges", edges.size)
      ])
    ]),
    ("nodes", Json.arr nodes),
    ("edges", Json.arr <| edges.map <| edgeJson declarations)
  ]

structure Config where
  output : Option String := none
  blueprint : Option String := none
  revision : Option String := none
  help : Bool := false
deriving Inhabited

partial def parseArgs (args : List String) (config : Config := {}) : Except String Config :=
  match args with
  | [] => .ok config
  | "--output" :: value :: rest => parseArgs rest { config with output := some value }
  | "--blueprint" :: value :: rest => parseArgs rest { config with blueprint := some value }
  | "--revision" :: value :: rest => parseArgs rest { config with revision := some value }
  | "--help" :: rest => parseArgs rest { config with help := true }
  | flag :: _ => .error s!"unknown or incomplete argument: {flag}"

def usage : String :=
  "Usage: lake exe gaussian_dependency_graph --output DIR --revision SHA " ++
  "[--blueprint FILE]"

def renderHtml (json : String) : IO String := do
  let template ← IO.FS.readFile "ProvableComputation/Tools/GaussianDependencyGraphTemplate.html"
  let sigma ← IO.FS.readFile ".lake/packages/importGraph/html-template/vendor/sigma.min.js"
  let graphology ←
    IO.FS.readFile ".lake/packages/importGraph/html-template/vendor/graphology.min.js"
  let graphologyLibrary ←
    IO.FS.readFile ".lake/packages/importGraph/html-template/vendor/graphology-library.min.js"
  return template
    |>.replace "/*__SIGMA_JS__*/" sigma
    |>.replace "/*__GRAPHOLOGY_JS__*/" graphology
    |>.replace "/*__GRAPHOLOGY_LIBRARY_JS__*/" graphologyLibrary
    |>.replace "/*__GRAPH_JSON__*/" (json.replace "</script" "<\\/script")

def findRedirectHtml (declarations : Array SourceDecl)
    (links : Array (String × Name)) : String :=
  let aliases := Json.mkObj <| links.toList.map fun (leanName, graphName) =>
    (leanName, nodeId declarations graphName)
  "<!doctype html><meta charset=\"utf-8\"><title>Open declaration</title><script>" ++
  s!"const aliases={aliases.compress};" ++
  "const prefix='#doc/';" ++
  "const requested=decodeURIComponent(location.hash.slice(prefix.length));" ++
  "const target=aliases[requested]??requested;" ++
  "location.replace('../index.html#doc/'+encodeURIComponent(target))" ++
  "</script><a href=\"../index.html\">Open the dependency graph</a>"

structure GraphData where
  coreDeclarations : Array SourceDecl
  basicDeclarations : Array SourceDecl
  correctnessDeclarations : Array SourceDecl
  edges : Array Dependency

def buildGraph (env : Environment) : IO GraphData := do
  let coreDeclarations ← parseModules env coreModules
  let basicDeclarations ← parseSourceDeclarations env luBasicModule
  let correctnessDeclarations ← parseSourceDeclarations env luCorrectnessModule
  let coreNames := namesOf coreDeclarations
  let basicNames := namesOf basicDeclarations
  let correctnessNames := namesOf correctnessDeclarations
  let coreConstants ← constantsOf env coreModules
  let basicConstants ← constantsOf env #[luBasicModule]
  let correctnessConstants ← constantsOf env #[luCorrectnessModule]
  let mut edges := collectDependencies env coreDeclarations coreNames coreConstants
  let basicPrimary := coreNames ++ basicNames
  let basicScoped := coreConstants ++ basicConstants
  let basicEdges := collectDependencies env basicDeclarations basicPrimary basicScoped
  edges := edges ++ aggregateBoundaryDependencies basicEdges luBasicBoundaryName coreNames
  let correctnessPrimary := coreNames ++ basicNames ++ correctnessNames
  let correctnessScoped := coreConstants ++ basicConstants ++ correctnessConstants
  let correctnessEdges :=
    collectDependencies env correctnessDeclarations correctnessPrimary correctnessScoped
  edges := edges ++
    aggregateBoundaryDependencies correctnessEdges luCorrectnessBoundaryName coreNames
  edges := edges ++ aggregateModuleBoundaryDependency correctnessEdges
    luCorrectnessBoundaryName luBasicBoundaryName basicNames
  return { coreDeclarations, basicDeclarations, correctnessDeclarations, edges }

structure BlueprintNode where
  label : String
  leanNames : Array String := #[]
  uses : Array String := #[]
  leanok : Bool := false
deriving Inhabited

def containsText (text needle : String) : Bool :=
  (text.splitOn needle).length > 1

def commandArgument? (line command : String) : Option String :=
  match line.splitOn ("\\" ++ command ++ "{") with
  | [_prefix, suffix] => (suffix.splitOn "}").head?.map fun value => value.trimAscii.toString
  | _ => none

def commaSeparated (value : String) : Array String :=
  (value.splitOn ",").foldl (init := #[]) fun values item =>
    let item := item.trimAscii.toString
    if item.isEmpty then values else values.push item

def parseBlueprintNodes (content : String) : Except String (Array BlueprintNode) := do
  if containsText content "\\notready" then
    throw "Blueprint must not contain \\notready nodes"
  let normalized := content.replace "\n" " "
  let leanCommandCount := (normalized.splitOn "\\lean{").length - 1
  let usesCommandCount := (normalized.splitOn "\\uses{").length - 1
  let mut nodes := #[]
  for block in (normalized.splitOn "\\label{").drop 1 do
    let labeledBlock := "\\label{" ++ block
    let some label := commandArgument? labeledBlock "label"
      | throw "Blueprint label has no closing brace"
    if (block.splitOn "\\lean{").length > 2 then
      throw s!"Blueprint node {label} has more than one \\lean command"
    if (block.splitOn "\\uses{").length > 2 then
      throw s!"Blueprint node {label} has more than one \\uses command"
    let leanNames := (commandArgument? block "lean").map commaSeparated |>.getD #[]
    let uses := (commandArgument? block "uses").map commaSeparated |>.getD #[]
    nodes := nodes.push { label, leanNames, uses, leanok := containsText block "\\leanok" }
  for node in nodes do
    if nodes.countP (fun candidate => candidate.label == node.label) != 1 then
      throw s!"duplicate Blueprint label: {node.label}"
    if node.leanNames.isEmpty then
      throw s!"Blueprint node {node.label} has no \\lean declarations"
    if !node.leanok then
      throw s!"Blueprint node {node.label} is missing \\leanok"
  unless leanCommandCount == nodes.size do
    throw "every Blueprint \\lean command must belong to exactly one labeled node"
  let parsedUsesCount := nodes.countP fun node => !node.uses.isEmpty
  unless usesCommandCount == parsedUsesCount do
    throw "every Blueprint \\uses command must belong to exactly one labeled node"
  return nodes

def publicDeclarationMatches (declarations : Array SourceDecl)
    (leanName : String) : Array SourceDecl :=
  declarations.filter fun declaration =>
    !isPrivateName declaration.rawName && declaration.userName.toString == leanName

def resolveBlueprintName (graph : GraphData) (leanName : String) : Except String Name := do
  let coreMatches := publicDeclarationMatches graph.coreDeclarations leanName
  let basicMatches := publicDeclarationMatches graph.basicDeclarations leanName
  let correctnessMatches := publicDeclarationMatches graph.correctnessDeclarations leanName
  let count := coreMatches.size + basicMatches.size + correctnessMatches.size
  if count == 0 then
    throw s!"Blueprint declaration is outside the allowed public scope: {leanName}"
  if count != 1 then
    throw s!"Blueprint declaration is ambiguous in the allowed scope: {leanName}"
  if let some declaration := coreMatches[0]? then
    return declaration.rawName
  if !basicMatches.isEmpty then
    return luBasicBoundaryName
  return luCorrectnessBoundaryName

structure ResolvedBlueprintNode where
  source : BlueprintNode
  declarations : Array Name

partial def reachesDependency (edges : Array Dependency) (consumer dependency : Name)
    (visited : NameSet := {}) : Bool :=
  if consumer == dependency then
    true
  else if visited.contains consumer then
    false
  else
    let visited := visited.insert consumer
    edges.any fun edge =>
      edge.consumer == consumer && reachesDependency edges edge.dependency dependency visited

def validateBlueprint (path : FilePath) (graph : GraphData) : IO (Array (String × Name)) := do
  let content ← IO.FS.readFile path
  let nodes ← IO.ofExcept <| parseBlueprintNodes content
  let mut resolved : Array ResolvedBlueprintNode := #[]
  let mut links := #[]
  for node in nodes do
    let mut declarations := #[]
    for leanName in node.leanNames do
      let graphName ← IO.ofExcept <| resolveBlueprintName graph leanName
      declarations := declarations.push graphName
      links := links.push (leanName, graphName)
    resolved := resolved.push { source := node, declarations }
  for node in resolved do
    for usedLabel in node.source.uses do
      let some dependencyNode := resolved.find? fun candidate =>
          candidate.source.label == usedLabel
        | throw <| IO.userError <|
            s!"Blueprint node {node.source.label} uses unknown label {usedLabel}"
      let isRealDependency := node.declarations.any fun consumer =>
        dependencyNode.declarations.any fun dependency =>
          reachesDependency graph.edges consumer dependency
      unless isRealDependency do
        throw <| IO.userError <|
          s!"Blueprint relation {usedLabel} -> {node.source.label} has no dependency path"
  let leanCount := resolved.foldl (init := 0) fun count node =>
    count + node.declarations.size
  let usesCount := resolved.foldl (init := 0) fun count node => count + node.source.uses.size
  IO.println (s!"validated {resolved.size} Blueprint nodes, {leanCount} declarations, " ++
    s!"and {usesCount} uses relations")
  return links

def run (config : Config) : IO Unit := do
  let some output := config.output | throw <| IO.userError "missing --output"
  let some revision := config.revision | throw <| IO.userError "missing --revision"
  initSearchPath (← findSysroot)
  let env ← importModules (importedModules.map fun module => { module }) {} (trustLevel := 1024)
  let graph ← buildGraph env
  validateGraph graph.coreDeclarations graph.edges
  let blueprintLinks ← match config.blueprint with
    | some blueprint => validateBlueprint blueprint graph
    | none => pure #[]
  let json := (graphJson revision graph.coreDeclarations graph.edges).pretty 120
  let outputPath : FilePath := output
  let findPath := outputPath / "find"
  IO.FS.createDirAll outputPath
  IO.FS.createDirAll findPath
  IO.FS.writeFile (outputPath / "graph.json") json
  IO.FS.writeFile (outputPath / "index.html") (← renderHtml json)
  IO.FS.writeFile (findPath / "index.html") <|
    findRedirectHtml graph.coreDeclarations blueprintLinks
  IO.println (s!"generated {graph.coreDeclarations.size + 2} nodes and " ++
    s!"{graph.edges.size} edges in {output}")

end GaussianDependencyGraph

def main (args : List String) : IO UInt32 := do
  match GaussianDependencyGraph.parseArgs args with
  | .error message =>
      IO.eprintln message
      IO.eprintln GaussianDependencyGraph.usage
      return 1
  | .ok config =>
      if config.help then
        IO.println GaussianDependencyGraph.usage
        return 0
      try
        GaussianDependencyGraph.run config
        return 0
      catch exception =>
        IO.eprintln exception.toString
        return 1
