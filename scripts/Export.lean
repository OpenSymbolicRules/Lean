import OSR

/-!
# Export and audit

Run with `just export` (see the `justfile`), which sets:

* `OSR_OUT_DIR` — output directory;
* `OSR_SOURCE_DIGEST` — digest of the sources (see `scripts/source-digest.sh`).

For every catalogue entry this script checks, in the elaborated environment:

1. the rule declaration evaluates to the catalogue's rule value;
2. the rule is well formed and uses only registered OpenMath symbols;
3. each listed proof is a theorem whose type is *exactly*
   `OSR.Rule.Holds <ruleDecl> <domain>`;
4. each proof depends only on the standard axioms
   `propext`, `Classical.choice`, `Quot.sound`.

Any violation is an error and the export fails.  Kernel checking itself
happened when the modules were compiled; `just check` additionally replays the
modules with `leanchecker`.
-/

open Lean Meta OSR OSR.Export

/-- Axioms accepted in certified proofs (the standard Mathlib foundations). -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Read the pinned Mathlib revision from `lake-manifest.json`. -/
def mathlibRevision : IO String := do
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile "lake-manifest.json")
  let pkgs ← IO.ofExcept <| json.getObjValAs? (Array Json) "packages"
  for p in pkgs do
    if (p.getObjValAs? String "name").toOption == some "mathlib" then
      return ← IO.ofExcept <| p.getObjValAs? String "rev"
  throw <| IO.userError "mathlib not found in lake-manifest.json"

unsafe def evalRule (decl : Name) : MetaM Rule :=
  evalExpr Rule (mkConst ``OSR.Rule) (mkConst decl)

/-- Audit one proof of one rule. -/
unsafe def auditProof (e : CatalogEntry) (d : Domain) (thm : Name) : MetaM Verification := do
  let some info := (← getEnv).find? thm
    | throwError "{e.rule.id}: proof {thm} does not exist"
  unless info matches .thmInfo _ do
    throwError "{e.rule.id}: {thm} is not a theorem"
  let domainConst := match d with
    | .real => ``OSR.Domain.real
    | .complex => ``OSR.Domain.complex
  let expected := mkApp2 (mkConst ``OSR.Rule.Holds) (mkConst e.ruleDecl) (mkConst domainConst)
  unless info.type == expected do
    throwError "{e.rule.id}: {thm} has type{indentExpr info.type}\nexpected{indentExpr expected}"
  let axioms := (← collectAxioms thm).toList.mergeSort (·.toString ≤ ·.toString)
  let forbidden := axioms.filter (· ∉ standardAxioms)
  unless forbidden.isEmpty do
    throwError "{e.rule.id}: {thm} depends on forbidden axioms {forbidden}"
  let assurance := Registry.mappingAssurance e.rule.symbols d
  return { domain := d, status := .proved, theoremName := some thm,
           statement := some s!"OSR.Rule.Holds {e.ruleDecl} {domainConst}",
           axioms, mappingAssurance := assurance, certified := assurance.certifiable }

/-- Audit one catalogue entry and return its verification records. -/
unsafe def auditEntry (e : CatalogEntry) : MetaM (List Verification) := do
  let r ← evalRule e.ruleDecl
  unless r == e.rule do
    throwError "{e.rule.id}: catalogue rule differs from declaration {e.ruleDecl}"
  let problems := e.rule.wellFormed
  unless problems.isEmpty do
    throwError "{e.rule.id}: ill-formed rule: {problems}"
  for s in e.rule.symbols do
    if (Registry.lookup s).isNone then
      throwError "{e.rule.id}: OpenMath symbol {s.uri} is not in the registry"
  let mut out := []
  for d in [Domain.real, Domain.complex] do
    match e.proofs.lookup d with
    | some thm => out := out ++ [← auditProof e d thm]
    | none =>
      let status := if e.unproved.contains d then Status.unproved else Status.unsupported
      out := out ++ [{ domain := d, status, theoremName := none, statement := none, axioms := [],
                       mappingAssurance := Registry.mappingAssurance e.rule.symbols d,
                       certified := false }]
  return out

/-- Check the registry: unique entries, existing Lean constants and obligations. -/
def auditRegistry : MetaM Unit := do
  let env ← getEnv
  for e in Registry.entries do
    if (Registry.entries.filter (·.symbol == e.symbol)).length != 1 then
      throwError "registry: duplicate entry for {e.symbol.uri}"
    if (Registry.cds.find? (·.cd == e.symbol.cd)).isNone then
      throwError "registry: CD {e.symbol.cd} is not pinned"
    for i in e.interpretations do
      unless env.contains i.leanConst do
        throwError "registry: {i.leanConst} does not exist"
      for o in i.obligations do
        let some info := env.find? o.theoremName
          | throwError "registry: obligation {o.theoremName} does not exist"
        unless info matches .thmInfo _ do
          throwError "registry: obligation {o.theoremName} is not a theorem"
        let forbidden := (← collectAxioms o.theoremName).toList.filter (· ∉ standardAxioms)
        unless forbidden.isEmpty do
          throwError "registry: obligation {o.theoremName} depends on {forbidden}"
      if i.assurance == .formallyRelated && i.obligations.isEmpty then
        throwError "registry: {e.symbol.uri} ({i.domain.key}) is formally_related without obligations"

/-- Count of verification records satisfying `p` in domain `d`. -/
def countIn (audited : List (CatalogEntry × List Verification)) (d : Domain)
    (p : Verification → Bool) : Nat :=
  (audited.filter fun (_, vs) => vs.any fun v => v.domain == d && p v).length

/-- Separate metrics; deliberately no combined percentage. -/
def metricsJson (audited : List (CatalogEntry × List Verification)) : Json :=
  let perDomain (d : Domain) := Json.mkObj [
    ("proved", toJson (countIn audited d (·.status == .proved))),
    ("certified", toJson (countIn audited d (·.certified))),
    ("unproved", toJson (countIn audited d (·.status == .unproved))),
    ("counterexample", toJson (countIn audited d (·.status == .counterexample))),
    ("unsupported", toJson (countIn audited d (·.status == .unsupported))),
    ("blocked_by_mapping_assurance",
      toJson (countIn audited d fun v => v.status == .proved && !v.certified))]
  Json.mkObj [
    ("rules_migrated", toJson audited.length),
    ("rules_exported", toJson audited.length),
    ("rules_with_findings", toJson (audited.filter (!·.1.findings.isEmpty)).length),
    ("real", perDomain .real),
    ("complex", perDomain .complex),
    ("julia_execution", Json.str "not measured by the exporter; see OpenSymbolicRules.jl test/test_osr_v1.jl")]

private def cell (vs : List Verification) (d : Domain) : String :=
  match vs.find? (·.domain == d) with
  | some v =>
    let c := if v.certified then "certified" else s!"not certified ({v.mappingAssurance.key} mapping)"
    if v.status == .proved then s!"proved, {c}" else v.status.key
  | none => "—"

/-- Human-readable verification report. -/
def reportMarkdown (b : BuildInfo) (audited : List (CatalogEntry × List Verification)) : String :=
  let header := s!"# Trigonometry verification report

Generated by `scripts/Export.lean`. Do not edit by hand.

- Lean toolchain: `{b.leanToolchain}`
- Mathlib revision: `{b.mathlibRevision}`
- Source digest: `sha256:{b.sourceDigest}`
- Accepted axioms: `propext`, `Classical.choice`, `Quot.sound`

A rule is *certified* in a domain when its theorem `Rule.Holds rule domain`
is proved with accepted axioms only **and** every OpenMath symbol it uses has
a `reviewed` or `formally_related` mapping in that domain.

## Metrics

| Metric | ℝ | ℂ |
|---|---|---|
| Rules migrated | {audited.length} | {audited.length} |
| Proved | {countIn audited .real (·.status == .proved)} | {countIn audited .complex (·.status == .proved)} |
| Certified | {countIn audited .real (·.certified)} | {countIn audited .complex (·.certified)} |
| Proved but blocked by mapping assurance | {countIn audited .real fun v => v.status == .proved && !v.certified} | {countIn audited .complex fun v => v.status == .proved && !v.certified} |
| Unproved | {countIn audited .real (·.status == .unproved)} | {countIn audited .complex (·.status == .unproved)} |
| Counterexamples | {countIn audited .real (·.status == .counterexample)} | {countIn audited .complex (·.status == .counterexample)} |

Julia execution is tested separately (OpenSymbolicRules.jl, `test/test_osr_v1.jl`)
and is not part of these figures.

## Rules

| Rule | v0.1 identity | ℝ | ℂ | Real theorem |
|---|---|---|---|---|
"
  let rows := audited.map fun (e, vs) =>
    let thm := (vs.find? (·.domain == .real)).bind (·.theoremName) |>.map toString |>.getD "—"
    s!"| `{e.rule.id}` | `{e.rule.legacyId.getD "—"}` | {cell vs .real} | {cell vs .complex} | `{thm}` |"
  let findings := audited.filter (!·.1.findings.isEmpty) |>.map fun (e, _) =>
    s!"### `{e.rule.id}`\n\n" ++ String.intercalate "\n" (e.findings.map ("- " ++ ·))
  header ++ String.intercalate "\n" rows ++ "\n\n## Findings\n\n" ++
    String.intercalate "\n\n" findings ++ "\n"

/-! ## Strategy analysis and conformance cases -/

/-- Step budget of the termination check and of the conformance cases. -/
def fuel : Nat := 64

private def tv : OSR.Expr := .var "t"
private def uv : OSR.Expr := .var "u"

/-- Inputs beyond the rule patterns: nested redexes, contexts and literals. -/
def extraSeeds : List (String × OSR.Expr) := [
  ("nested.pythagorean_in_product",
    .app2 .mul (.int 2) (.app2 .add (.powNat (.app1 .sin tv) 2) (.powNat (.app1 .cos tv) 2))),
  ("nested.pythagorean_of_sum",
    .app2 .add (.powNat (.app1 .sin (.app2 .add tv uv)) 2)
      (.powNat (.app1 .cos (.app2 .add tv uv)) 2)),
  ("nested.sin_of_double_sum", .app1 .sin (.app2 .add (.app2 .mul (.int 2) tv) uv)),
  ("nested.tan_arctan_inside_sin", .app1 .sin (.app1 .tan (.app1 .arctan tv))),
  ("literal.cube_is_not_square", .app2 .add (.powNat (.app1 .sin tv) 3) (.powNat (.app1 .cos tv) 3)),
  ("literal.three_is_not_two", .app1 .sin (.app2 .mul (.int 3) tv)),
  ("nonlinear.sin_add_sin_same", .app2 .add (.app1 .sin tv) (.app1 .sin tv)),
  ("normal.atom", tv)]

/-- Seeds of the termination check: every catalogue pattern, plus `extraSeeds`. -/
def seeds : List (String × OSR.Expr) :=
  Trigonometry.catalog.map (fun e => (s!"pattern.{e.rule.id}", e.rule.lhs)) ++ extraSeeds

/-- One normalization per profile and seed. -/
def strategyRuns : List (String × String × OSR.Expr × Normalization) :=
  Trigonometry.profiles.flatMap fun p =>
    seeds.map fun (name, e) => (p, name, e, normalize (Trigonometry.profileRules p) fuel e)

def strategyJson : Json :=
  Json.mkObj [
    ("engine", Json.str "OSR.normalize (reference rewriter, proved sound: OSR.normalize_sound)"),
    ("fuel", toJson fuel),
    ("seeds", toJson seeds.length),
    ("profiles", Json.mkObj (Trigonometry.profiles.map fun p =>
      let runs := strategyRuns.filter (·.1 == p)
      (p, Json.mkObj [
        ("rules", Json.arr ((Trigonometry.profileRules p).map (Json.str ·.id)).toArray),
        ("terminates_on_seeds", toJson (runs.all (·.2.2.2.normal))),
        ("max_steps", toJson ((runs.map (·.2.2.2.trace.length)).foldl max 0))])))]

def conformanceJson (b : BuildInfo) : Json :=
  Json.mkObj [
    ("osr_format", Json.str formatVersion),
    ("suite", Json.str "trigonometry.rewrite"),
    ("ruleset", Json.str "trigonometry.osr.json"),
    ("source_digest", Json.str s!"sha256:{b.sourceDigest}"),
    ("semantics", Json.mkObj [
      ("domain", Json.str "real"),
      ("rules", Json.str "the rules of the profile, unconditional only, in priority order"),
      ("strategy", Json.str "outermost-leftmost: at each step, try the root (rules in order), then the arguments left to right; one rewrite per step"),
      ("matching", Json.str "syntactic; a pattern variable occurring twice matches equal subterms; integers compare by value; input OMV are constants"),
      ("fuel", toJson fuel),
      ("reference", Json.str "OSR.normalize in OpenSymbolicRules/Lean (OSR/Rewrite.lean)")]),
    ("cases", Json.arr (strategyRuns.map fun (p, name, e, n) =>
      Json.mkObj [
        ("id", Json.str s!"{p}/{name}"),
        ("profile", Json.str p),
        ("input", e.toOMJson),
        ("expected", n.result.toOMJson),
        ("trace", Json.arr (n.trace.map Json.str).toArray),
        ("normal", toJson n.normal)]).toArray)]

def strategyMarkdown : String :=
  let rows := Trigonometry.profiles.map fun p =>
    let runs := strategyRuns.filter (·.1 == p)
    let ok := runs.all (·.2.2.2.normal)
    let maxSteps := (runs.map (·.2.2.2.trace.length)).foldl max 0
    s!"| `{p}` | {(Trigonometry.profileRules p).length} | {if ok then "yes" else "**no**"} | {maxSteps} |"
  s!"## Strategy

Each profile is run with the reference rewriter (`OSR.normalize`, proved
sound) on {seeds.length} seeds: every catalogue pattern plus nested inputs.
Termination is tested on these seeds with a budget of {fuel} steps, not proved.

| Profile | Rules | Normal form on every seed | Max steps |
|---|---|---|---|
" ++ String.intercalate "\n" rows ++ "\n"

unsafe def runExport : MetaM Unit := do
  let some outDir ← IO.getEnv "OSR_OUT_DIR" | throwError "OSR_OUT_DIR is not set"
  let some digest ← IO.getEnv "OSR_SOURCE_DIGEST" | throwError "OSR_SOURCE_DIGEST is not set"
  let toolchain := (← IO.FS.readFile "lean-toolchain").replace "\n" ""
  let build : BuildInfo :=
    { leanToolchain := toolchain, mathlibRevision := ← mathlibRevision, sourceDigest := digest }
  auditRegistry
  let ids := Trigonometry.catalog.map (·.rule.id)
  unless ids.eraseDups.length == ids.length do
    throwError "duplicate rule identifiers in the Trigonometry catalogue"
  let stuck := strategyRuns.filter (!·.2.2.2.normal)
  unless stuck.isEmpty do
    throwError "profiles do not terminate within {fuel} steps: {stuck.map fun r => (r.1, r.2.1)}"
  let mut audited := []
  for e in Trigonometry.catalog do
    audited := audited ++ [(e, ← auditEntry e)]
  let doc := rulesetJson "trigonometry" build "OSR.Trigonometry" audited
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir ++ "/trigonometry.osr.json") (doc.pretty ++ "\n")
  let registry := Json.mkObj [
    ("osr_format", Json.str formatVersion),
    ("cdbase", Json.str OMSymbol.cdbase),
    ("symbols", Json.arr (Registry.entries.map symbolJson).toArray)]
  IO.FS.writeFile (outDir ++ "/registry.json") (registry.pretty ++ "\n")
  let report := Json.mkObj [
    ("osr_format", Json.str formatVersion),
    ("build", Json.mkObj [("lean_toolchain", Json.str build.leanToolchain),
      ("mathlib_revision", Json.str build.mathlibRevision),
      ("source_digest", Json.str s!"sha256:{build.sourceDigest}")]),
    ("metrics", metricsJson audited),
    ("strategy", strategyJson)]
  IO.FS.writeFile (outDir ++ "/report.json") (report.pretty ++ "\n")
  IO.FS.writeFile (outDir ++ "/report.md") (reportMarkdown build audited ++ "\n" ++ strategyMarkdown)
  IO.FS.createDirAll (outDir ++ "/conformance")
  IO.FS.writeFile (outDir ++ "/conformance/trigonometry.cases.json")
    ((conformanceJson build).pretty ++ "\n")
  logInfo m!"exported {audited.length} rules to {outDir}"

#eval runExport
