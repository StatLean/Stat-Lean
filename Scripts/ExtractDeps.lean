/-
Dependency-graph extractor for the Asymptotica website.

Reads `website/targets.txt` (lines of `<id>\t<fullName>`), and for each target
walks its proof-term / statement dependencies *through repository declarations*,
stopping at the first Mathlib (or core) declaration it reaches. Emits one JSON
graph per target at `website/src/data/graphs/<id>.json`.

Run (after `lake build`):  `lake exe deps`
-/
import Lean

open Lean

/-- Maximum number of nodes per graph, to keep the picture readable. -/
def maxNodes : Nat := 46

/-- A declaration is "from this repository" iff its defining module is under
the `AsymptoticStatistics` namespace. Everything else (Mathlib, Init, Std, Lean)
is treated as an external leaf. -/
def isRepoModule (mod : Name) : Bool :=
  (`AsymptoticStatistics).isPrefixOf mod

/-- Modules whose declarations are tactic/meta plumbing (e.g. the `ring` and
`norm_num` proof-construction lemmas) rather than real mathematical results. -/
def isNoiseModule (mod : Name) : Bool :=
  mod.components.any (fun c => c == `Tactic || c == `Meta || c == `Elab)
  || (`Lean).isPrefixOf mod
  || (`Init).isPrefixOf mod
  || (`Std).isPrefixOf mod

/-- Drop auto-generated / noise constants so the graph shows real lemmas. -/
def isJunk (n : Name) : Bool :=
  n.isInternalDetail
  || n.hasMacroScopes
  || (match n with | .num .. => true | _ => false)
  || -- structural / eliminator boilerplate, and instance clutter
     let last := n.getString!
     [ "rec", "recOn", "casesOn", "below", "ibelow", "brecOn", "noConfusion",
       "noConfusionType", "ofNat", "proof_1", "proof_2", "eq_1", "eq_2",
       "match_1", "match_2", "sizeOf", "sizeOf_spec" ].contains last
  || "_cstage".isPrefixOf last
  || "match_".isPrefixOf last
  || "proof_".isPrefixOf last
  || "inst".isPrefixOf last
where
  -- safe last-component string
  lastStr (n : Name) : String := match n with | .str _ s => s | _ => ""

/-- Ubiquitous logical primitives we never want as nodes. -/
def isPrimitive (n : Name) : Bool :=
  [ ``Eq, ``Eq.refl, ``Eq.mpr, ``Eq.mp, ``Eq.trans, ``Eq.symm, ``rfl,
    ``id, ``Iff, ``Iff.intro, ``Iff.mp, ``Iff.mpr, ``And, ``And.intro,
    ``And.left, ``And.right, ``Or, ``Exists, ``Exists.intro, ``True, ``False,
    ``HEq, ``HEq.refl, ``congrArg, ``congrFun, ``funext, ``letFun,
    ``sorryAx, ``trivial, ``Not, ``Function.comp ].contains n

/-- The module a declaration was defined in (`.anonymous` if local/unknown). -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx]!
  | none => .anonymous

/-- Is `n` a proven result (a `theorem`/lemma), as opposed to a definition,
structure, class, or instance? These are the "results" the graph is about. -/
def isResult (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

/-- A dependency worth showing: not boilerplate, not a logical primitive, and
not a structure-projection function (those are typeclass plumbing, e.g.
`toUniformSpace`, that swamp the real mathematical content). -/
def usefulDep (env : Environment) (n : Name) : Bool :=
  !isJunk n && !isPrimitive n && (env.getProjectionFnInfo? n).isNone

/-- Direct, de-noised constant dependencies of a declaration (type + proof). -/
def directDeps (env : Environment) (c : Name) : Array Name := Id.run do
  match env.find? c with
  | none => return #[]
  | some info =>
    let fromType := info.type.getUsedConstants
    let fromVal := (info.value?.map Expr.getUsedConstants).getD #[]
    let mut seen : NameSet := {}
    let mut out : Array Name := #[]
    for n in fromType ++ fromVal do
      if n != c && usefulDep env n && !seen.contains n then
        seen := seen.insert n
        out := out.push n
    return out

structure Node where
  full : Name
  kind : String  -- "root" | "repo" | "mathlib"
  module : Name
  decl : String  -- "thm" (theorem/lemma) | "def" (definition/structure)

def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc ch =>
    acc ++ (match ch with
      | '\\' => "\\\\"
      | '"'  => "\\\""
      | '\n' => "\\n"
      | _    => String.singleton ch)

/-- Build the dependency graph for `root`, BFS through repository declarations,
with Mathlib declarations as leaves.

Two modes, chosen by the root:
* if the root is a **result** (theorem/lemma) we show the *logical* dependency
  graph — repository concepts/lemmas plus the Mathlib **results** the proofs
  invoke (the "first level of Mathlib results used"); Mathlib definitions and
  typeclasses are pruned so the real lemmas stand out.
* if the root is a **definition/structure** we show the *concept-construction*
  graph — the repository and Mathlib notions it is built from. -/
def buildGraph (env : Environment) (root : Name) :
    Array Node × Array (Name × Name) := Id.run do
  let proofMode := isResult env root
  -- Should a Mathlib (non-repo) dependency appear as a leaf node?
  let keepMathlib := fun (n : Name) => if proofMode then isResult env n else true
  let declKind := fun (n : Name) => if isResult env n then "thm" else "def"
  let mut nodes : Array Node := #[⟨root, "root", moduleOf env root, declKind root⟩]
  let mut nodeIds : NameSet := NameSet.empty.insert root
  let mut edges : Array (Name × Name) := #[]
  let mut edgeSeen : Std.HashSet (Name × Name) := {}
  -- queue of repo nodes whose dependencies still need expanding
  let mut queue : Array Name := #[root]
  let mut qi := 0
  while qi < queue.size do
    let cur := queue[qi]!
    qi := qi + 1
    if nodes.size ≥ maxNodes then
      break
    for dep in directDeps env cur do
      let mod := moduleOf env dep
      let depIsRepo := isRepoModule mod
      -- drop tactic/meta plumbing entirely
      if isNoiseModule mod then
        continue
      -- prune Mathlib plumbing that isn't a "result" in proof mode
      if !depIsRepo && !keepMathlib dep then
        continue
      -- record node
      if !nodeIds.contains dep then
        if nodes.size ≥ maxNodes then
          continue
        nodeIds := nodeIds.insert dep
        nodes := nodes.push ⟨dep, if depIsRepo then "repo" else "mathlib", mod, declKind dep⟩
        -- only expand further through repository declarations
        if depIsRepo then
          queue := queue.push dep
      -- record edge (only between nodes we actually kept)
      if nodeIds.contains dep then
        let e := (cur, dep)
        if !edgeSeen.contains e then
          edgeSeen := edgeSeen.insert e
          edges := edges.push e
  return (nodes, edges)

def nodeJson (n : Node) : String :=
  let label := n.full.getString!
  "    {\"id\":\"" ++ jsonEscape n.full.toString ++
  "\",\"label\":\"" ++ jsonEscape label ++
  "\",\"full\":\"" ++ jsonEscape n.full.toString ++
  "\",\"kind\":\"" ++ n.kind ++
  "\",\"decl\":\"" ++ n.decl ++
  "\",\"module\":\"" ++ jsonEscape n.module.toString ++ "\"}"

def edgeJson (e : Name × Name) : String :=
  "    {\"source\":\"" ++ jsonEscape e.1.toString ++
  "\",\"target\":\"" ++ jsonEscape e.2.toString ++ "\"}"

def graphJson (root : Name) (nodes : Array Node) (edges : Array (Name × Name)) : String :=
  let ns := String.intercalate ",\n" (nodes.toList.map nodeJson)
  let es := String.intercalate ",\n" (edges.toList.map edgeJson)
  "{\n  \"root\": \"" ++ jsonEscape root.toString ++ "\",\n" ++
  "  \"nodes\": [\n" ++ ns ++ "\n  ],\n" ++
  "  \"edges\": [\n" ++ es ++ "\n  ]\n}\n"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  IO.println "Importing AsymptoticStatistics environment…"
  let env ← importModules #[{ module := `AsymptoticStatistics }] {} (trustLevel := 1024)
  let targetsFile := "website/targets.txt"
  let content ← IO.FS.readFile targetsFile
  let outDir : System.FilePath := "website/src/data/graphs"
  IO.FS.createDirAll outDir
  let mut ok := 0
  let mut missing : Array String := #[]
  for line in content.splitOn "\n" do
    let line := line.trim
    if line.isEmpty then continue
    let parts := line.splitOn "\t"
    if parts.length < 2 then continue
    let id := parts[0]!.trim
    let full := parts[1]!.trim.toName
    if (env.find? full).isNone then
      missing := missing.push s!"{id} ({full})"
      continue
    let (nodes, edges) := buildGraph env full
    let json := graphJson full nodes edges
    IO.FS.writeFile (outDir / s!"{id}.json") json
    ok := ok + 1
    IO.println s!"  ✓ {id}: {nodes.size} nodes, {edges.size} edges"
  IO.println s!"\nWrote {ok} graphs to {outDir}."
  if !missing.isEmpty then
    IO.println s!"⚠ {missing.size} targets not found in environment:"
    for m in missing do IO.println s!"    {m}"
