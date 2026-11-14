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

For every profile of every rule set (`ruleSets`) it checks that the
termination theorem has type exactly `OSR.Terminates (<profileRules> p)
<weight>`, with the same axioms.

Per rule set `<name>` it writes `<name>.osr.json`, `<name>.report.json`,
`<name>.report.md` and `conformance/<name>.cases.json`; `registry.json` is
shared.

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
    | .boolean => ``OSR.Domain.boolean
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

/-! ## Rule sets -/

/-- Everything the exporter needs to know about one rule set. -/
structure RuleSet where
  /-- File and identifier prefix, e.g. `trigonometry`. -/
  name : String
  title : String
  /-- The Lean module defining the rules. -/
  module : String
  catalog : List CatalogEntry
  profiles : List String
  /-- The `profileRules` declaration (its value must be `profileRules`). -/
  profileRulesDecl : Name
  profileRules : String → List Rule
  /-- Per profile: weight declaration and termination theorem. -/
  termination : List (String × Name × Name)
  /-- Inputs beyond the rule patterns: nested redexes, contexts and literals. -/
  extraSeeds : List (String × OSR.Expr)
  /-- v0.1 rules outside the fragment: legacy identifier and reason. -/
  notMigrated : List (String × String) := []

private def tv : OSR.Expr := .var "t"
private def uv : OSR.Expr := .var "u"
private def vv : OSR.Expr := .var "v"

def trigonometry : RuleSet where
  name := "trigonometry"
  title := "Trigonometry"
  module := "OSR.Trigonometry"
  catalog := Trigonometry.catalog
  profiles := Trigonometry.profiles
  profileRulesDecl := ``Trigonometry.profileRules
  profileRules := Trigonometry.profileRules
  termination := [
    ("default", ``Trigonometry.defaultWeight, ``Trigonometry.default_terminates),
    ("product_to_sum", ``Trigonometry.productToSumWeight,
      ``Trigonometry.productToSum_terminates),
    ("power_reduction", ``Trigonometry.powerReductionWeight,
      ``Trigonometry.powerReduction_terminates),
    ("sum_to_product", ``Trigonometry.sumToProductWeight,
      ``Trigonometry.sumToProduct_terminates)]
  extraSeeds := [
    ("nested.pythagorean_in_product",
      .app2 .mul (.int 2) (.app2 .add (.pow (.app1 .sin tv) (.int 2)) (.pow (.app1 .cos tv) (.int 2)))),
    ("nested.pythagorean_of_sum",
      .app2 .add (.pow (.app1 .sin (.app2 .add tv uv)) (.int 2))
        (.pow (.app1 .cos (.app2 .add tv uv)) (.int 2))),
    ("nested.sin_of_double_sum", .app1 .sin (.app2 .add (.app2 .mul (.int 2) tv) uv)),
    ("nested.tan_arctan_inside_sin", .app1 .sin (.app1 .tan (.app1 .arctan tv))),
    ("literal.cube_is_not_square",
      .app2 .add (.pow (.app1 .sin tv) (.int 3)) (.pow (.app1 .cos tv) (.int 3))),
    ("literal.three_is_not_two", .app1 .sin (.app2 .mul (.int 3) tv)),
    ("nonlinear.sin_add_sin_same", .app2 .add (.app1 .sin tv) (.app1 .sin tv)),
    ("normal.atom", tv)]

def algebra : RuleSet where
  name := "algebra"
  title := "Algebra"
  module := "OSR.Algebra"
  catalog := Algebra.catalog
  profiles := Algebra.profiles
  profileRulesDecl := ``Algebra.profileRules
  profileRules := Algebra.profileRules
  termination := [
    ("default", ``Algebra.defaultWeight, ``Algebra.default_terminates),
    ("factor_polynomials", ``Algebra.factorWeight, ``Algebra.factor_terminates)]
  extraSeeds := [
    ("nested.identities", .app2 .mul (.int 1) (.app2 .add tv (.app2 .mul uv (.int 0)))),
    ("nested.distribute_twice",
      .app2 .mul tv (.app2 .add uv (.app2 .mul vv (.app2 .add tv (.int 1))))),
    ("nested.factor_inside_sum",
      .app2 .add (.app2 .add (.app2 .mul tv uv) (.app2 .mul tv vv)) (.int 0)),
    ("conditional.ln_mul_not_applied", .app1 .ln (.app2 .mul tv uv)),
    ("conditional.exp_ln_not_applied", .app1 .exp (.app1 .ln tv)),
    ("literal.two_is_not_one", .app2 .mul tv (.int 2)),
    ("nonlinear.factor_needs_same_factor",
      .app2 .add (.app2 .mul tv uv) (.app2 .mul uv vv)),
    ("normal.atom", tv)]
  notMigrated := Algebra.notMigrated

def ruleSets : List RuleSet := [trigonometry, algebra]

/-- Separate metrics; deliberately no combined percentage. -/
def metricsJson (rs : RuleSet) (audited : List (CatalogEntry × List Verification)) : Json :=
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
    ("rules_not_migrated", toJson rs.notMigrated.length),
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
def reportMarkdown (rs : RuleSet) (b : BuildInfo)
    (audited : List (CatalogEntry × List Verification)) : String :=
  let header := s!"# {rs.title} verification report

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
| Unsupported | {countIn audited .real (·.status == .unsupported)} | {countIn audited .complex (·.status == .unsupported)} |
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
  let notMigrated :=
    if rs.notMigrated.isEmpty then ""
    else "\n## Rules not migrated\n\n| v0.1 identity | Reason |\n|---|---|\n" ++
      String.intercalate "\n" (rs.notMigrated.map fun (id, why) => s!"| `{id}` | {why} |") ++ "\n"
  header ++ String.intercalate "\n" rows ++ "\n" ++ notMigrated ++ "\n## Findings\n\n" ++
    String.intercalate "\n\n" findings ++ "\n"

/-! ## Strategy analysis and conformance cases -/

/-- Step budget of the termination check and of the conformance cases. -/
def fuel : Nat := 64

/-- Seeds of the termination check: every catalogue pattern, plus the extra seeds. -/
def RuleSet.seeds (rs : RuleSet) : List (String × OSR.Expr) :=
  rs.catalog.map (fun e => (s!"pattern.{e.rule.id}", e.rule.lhs)) ++ rs.extraSeeds

/-- One normalization per profile and seed. -/
def RuleSet.runs (rs : RuleSet) : List (String × String × OSR.Expr × Normalization) :=
  rs.profiles.flatMap fun p =>
    rs.seeds.map fun (name, e) => (p, name, e, normalize (rs.profileRules p) fuel e)

/-- Check that a profile's termination theorem has type exactly
`OSR.Terminates (<profileRules> p) weight` and depends only on the standard
axioms.  Returns the JSON record. -/
def auditTermination (rs : RuleSet) (p : String) : MetaM Json := do
  let some (_, w, thm) := rs.termination.find? (·.1 == p)
    | throwError "{rs.name}: profile {p} has no termination proof"
  let some info := (← getEnv).find? thm
    | throwError "{rs.name}/{p}: termination proof {thm} does not exist"
  unless info matches .thmInfo _ do
    throwError "{rs.name}/{p}: {thm} is not a theorem"
  let expected := mkApp2 (mkConst ``OSR.Terminates)
    (mkApp (mkConst rs.profileRulesDecl) (mkStrLit p)) (mkConst w)
  unless info.type == expected do
    throwError "{rs.name}/{p}: {thm} has type{indentExpr info.type}\nexpected{indentExpr expected}"
  let axioms := (← collectAxioms thm).toList.mergeSort (·.toString ≤ ·.toString)
  let forbidden := axioms.filter (· ∉ standardAxioms)
  unless forbidden.isEmpty do
    throwError "{rs.name}/{p}: {thm} depends on forbidden axioms {forbidden}"
  return Json.mkObj [
    ("status", Json.str "proved"),
    ("theorem", Json.str thm.toString),
    ("statement", Json.str s!"OSR.Terminates ({rs.profileRulesDecl} \"{p}\") {w}"),
    ("weight", Json.str w.toString),
    ("axioms", Json.arr (axioms.map (Json.str ·.toString)).toArray)]

def strategyJson (rs : RuleSet) (termination : List (String × Json)) : Json :=
  Json.mkObj [
    ("engine", Json.str "OSR.normalize (reference rewriter, proved sound: OSR.normalize_sound)"),
    ("fuel", toJson fuel),
    ("seeds", toJson rs.seeds.length),
    ("profiles", Json.mkObj (rs.profiles.map fun p =>
      let runs := rs.runs.filter (·.1 == p)
      (p, Json.mkObj [
        ("rules", Json.arr ((rs.profileRules p).map (Json.str ·.id)).toArray),
        ("termination", (termination.lookup p).getD Json.null),
        ("terminates_on_seeds", toJson (runs.all (·.2.2.2.normal))),
        ("max_steps", toJson ((runs.map (·.2.2.2.trace.length)).foldl max 0))])))]

def conformanceJson (rs : RuleSet) (b : BuildInfo) : Json :=
  Json.mkObj [
    ("osr_format", Json.str formatVersion),
    ("suite", Json.str s!"{rs.name}.rewrite"),
    ("ruleset", Json.str s!"{rs.name}.osr.json"),
    ("source_digest", Json.str s!"sha256:{b.sourceDigest}"),
    ("semantics", Json.mkObj [
      ("domain", Json.str "real"),
      ("rules", Json.str "the rules of the profile, unconditional only, in priority order"),
      ("strategy", Json.str "outermost-leftmost: at each step, try the root (rules in order), then the arguments left to right; one rewrite per step"),
      ("matching", Json.str "syntactic; a pattern variable occurring twice matches equal subterms; integers compare by value; input OMV are constants"),
      ("fuel", toJson fuel),
      ("reference", Json.str "OSR.normalize in OpenSymbolicRules/Lean (OSR/Rewrite.lean)")]),
    ("cases", Json.arr (rs.runs.map fun (p, name, e, n) =>
      Json.mkObj [
        ("id", Json.str s!"{p}/{name}"),
        ("profile", Json.str p),
        ("input", e.toOMJson),
        ("expected", n.result.toOMJson),
        ("trace", Json.arr (n.trace.map Json.str).toArray),
        ("normal", toJson n.normal)]).toArray)]

def strategyMarkdown (rs : RuleSet) : String :=
  let rows := rs.profiles.map fun p =>
    let runs := rs.runs.filter (·.1 == p)
    let ok := runs.all (·.2.2.2.normal)
    let maxSteps := (runs.map (·.2.2.2.trace.length)).foldl max 0
    s!"| `{p}` | {(rs.profileRules p).length} | {if ok then "yes" else "**no**"} | {maxSteps} |"
  let proofRows := rs.termination.map fun (p, w, thm) => s!"| `{p}` | `{w}` | `{thm}` |"
  s!"## Strategy

Termination of every profile is proved: each profile has a weight, a strictly
monotone interpretation of the operators into ℕ, under which all its rules
decrease, so the reference rewriter (`OSR.normalize`, proved sound) reaches a
normal form within the weight of its input (`OSR.Terminates`).

| Profile | Weight | Theorem |
|---|---|---|
" ++ String.intercalate "\n" proofRows ++ s!"

Each profile is also run on {rs.seeds.length} seeds (every catalogue pattern plus
nested inputs) with a budget of {fuel} steps; these runs are the conformance
cases.

| Profile | Rules | Normal form on every seed | Max steps |
|---|---|---|---|
" ++ String.intercalate "\n" rows ++ "\n"

/-- Audit one rule set and write its rule set, report and conformance cases. -/
unsafe def exportRuleSet (outDir : String) (build : BuildInfo) (rs : RuleSet) : MetaM Nat := do
  let ids := rs.catalog.map (·.rule.id)
  unless ids.eraseDups.length == ids.length do
    throwError "duplicate rule identifiers in the {rs.title} catalogue"
  unless ids.all (·.startsWith s!"{rs.name}.") do
    throwError "{rs.title}: every rule identifier must start with {rs.name}."
  let stuck := rs.runs.filter (!·.2.2.2.normal)
  unless stuck.isEmpty do
    throwError "{rs.name}: profiles do not terminate within {fuel} steps: {stuck.map fun r => (r.1, r.2.1)}"
  let termination ← rs.profiles.mapM fun p => return (p, ← auditTermination rs p)
  let mut audited := []
  for e in rs.catalog do
    audited := audited ++ [(e, ← auditEntry e)]
  let doc := rulesetJson rs.name build rs.module audited
  IO.FS.writeFile (outDir ++ s!"/{rs.name}.osr.json") (doc.pretty ++ "\n")
  let report := Json.mkObj [
    ("osr_format", Json.str formatVersion),
    ("ruleset", Json.str rs.name),
    ("build", Json.mkObj [("lean_toolchain", Json.str build.leanToolchain),
      ("mathlib_revision", Json.str build.mathlibRevision),
      ("source_digest", Json.str s!"sha256:{build.sourceDigest}")]),
    ("metrics", metricsJson rs audited),
    ("not_migrated", Json.arr (rs.notMigrated.map fun (id, why) =>
      Json.mkObj [("legacy_id", Json.str id), ("reason", Json.str why)]).toArray),
    ("strategy", strategyJson rs termination)]
  IO.FS.writeFile (outDir ++ s!"/{rs.name}.report.json") (report.pretty ++ "\n")
  IO.FS.writeFile (outDir ++ s!"/{rs.name}.report.md")
    (reportMarkdown rs build audited ++ "\n" ++ strategyMarkdown rs)
  IO.FS.writeFile (outDir ++ s!"/conformance/{rs.name}.cases.json")
    ((conformanceJson rs build).pretty ++ "\n")
  return audited.length

/-! ## Logic: the Boolean rule set -/

private def jstr (s : String) : Json := Json.str s
private def jstrs (l : List String) : Json := Json.arr (l.map Json.str).toArray

unsafe def evalBRule (decl : Name) : MetaM Logic.BRule :=
  evalExpr Logic.BRule (mkConst ``OSR.Logic.BRule) (mkConst decl)

/-- Audit one Boolean rule: declaration, registry symbols, and a theorem of
type exactly `OSR.Logic.BRule.Holds <decl>` with the standard axioms. -/
unsafe def auditLogicEntry (e : Logic.LogicEntry) : MetaM Verification := do
  let r ← evalBRule e.ruleDecl
  unless r == e.rule do
    throwError "{e.rule.id}: catalogue rule differs from declaration {e.ruleDecl}"
  unless e.rule.rhs.vars.all (· ∈ e.rule.lhs.vars) do
    throwError "{e.rule.id}: replacement uses unbound variables"
  for s in e.rule.symbols do
    if (Registry.lookup s).isNone then
      throwError "{e.rule.id}: OpenMath symbol {s.uri} is not in the registry"
  let some info := (← getEnv).find? e.proof
    | throwError "{e.rule.id}: proof {e.proof} does not exist"
  unless info matches .thmInfo _ do
    throwError "{e.rule.id}: {e.proof} is not a theorem"
  let expected := mkApp (mkConst ``OSR.Logic.BRule.Holds) (mkConst e.ruleDecl)
  unless info.type == expected do
    throwError "{e.rule.id}: {e.proof} has type{indentExpr info.type}\nexpected{indentExpr expected}"
  let axioms := (← collectAxioms e.proof).toList.mergeSort (·.toString ≤ ·.toString)
  let forbidden := axioms.filter (· ∉ standardAxioms)
  unless forbidden.isEmpty do
    throwError "{e.rule.id}: {e.proof} depends on forbidden axioms {forbidden}"
  let assurance := Registry.mappingAssurance e.rule.symbols .boolean
  return { domain := .boolean, status := .proved, theoremName := some e.proof,
           statement := some s!"OSR.Logic.BRule.Holds {e.ruleDecl}", axioms,
           mappingAssurance := assurance, certified := assurance.certifiable }

def logicTermination : List (String × Name × Name) := [
  ("default", ``Logic.defaultWeight, ``Logic.default_terminates),
  ("to_cnf", ``Logic.cnfWeight, ``Logic.cnf_terminates),
  ("to_dnf", ``Logic.dnfWeight, ``Logic.dnf_terminates)]

def auditLogicTermination (p : String) : MetaM Json := do
  let some (_, w, thm) := logicTermination.find? (·.1 == p)
    | throwError "logic: profile {p} has no termination proof"
  let some info := (← getEnv).find? thm
    | throwError "logic/{p}: termination proof {thm} does not exist"
  let expected := mkApp2 (mkConst ``OSR.Logic.Terminates)
    (mkApp (mkConst ``Logic.profileRules) (mkStrLit p)) (mkConst w)
  unless info.type == expected do
    throwError "logic/{p}: {thm} has type{indentExpr info.type}\nexpected{indentExpr expected}"
  let axioms := (← collectAxioms thm).toList.mergeSort (·.toString ≤ ·.toString)
  unless (axioms.filter (· ∉ standardAxioms)).isEmpty do
    throwError "logic/{p}: {thm} depends on forbidden axioms"
  return Json.mkObj [
    ("status", jstr "proved"), ("theorem", jstr thm.toString),
    ("statement", jstr s!"OSR.Logic.Terminates (OSR.Logic.profileRules \"{p}\") {w}"),
    ("weight", jstr w.toString),
    ("axioms", Json.arr (axioms.map (jstr ·.toString)).toArray)]

private def logicP : Logic.BExpr := .var "p"
private def logicQ : Logic.BExpr := .var "q"
private def logicR : Logic.BExpr := .var "r"

def logicExtraSeeds : List (String × Logic.BExpr) := [
  ("nested.not_implies", .not (.bin .implies logicP logicQ)),
  ("nested.not_equivalent", .not (.bin .equivalent logicP logicQ)),
  ("nested.xor_self", .bin .xor logicP logicP),
  ("nested.nand_or", .bin .nand (.bin .or logicP logicQ) logicR),
  ("nested.or_and", .bin .or logicP (.bin .and logicQ logicR)),
  ("nested.and_or", .bin .and logicP (.bin .or logicQ logicR)),
  ("nonlinear.or_not_other", .bin .or logicP (.not logicQ)),
  ("quantifier.not_forall_body", .not (.all "y" (.bin .and (.var "y") logicQ))),
  ("quantifier.merge_forall", .bin .and (.all "y" (.bin .or (.var "y") logicP))
    (.all "y" (.bin .or (.var "y") logicQ))),
  ("quantifier.different_binders", .bin .and (.all "y" logicP) (.all "z" logicQ)),
  ("normal.atom", logicP)]

def logicSeeds : List (String × Logic.BExpr) :=
  Logic.catalog.map (fun e => (s!"pattern.{e.rule.id}", e.rule.lhs)) ++ logicExtraSeeds

def logicRuns : List (String × String × Logic.BExpr × Logic.BNormalization) :=
  Logic.profiles.flatMap fun p =>
    logicSeeds.map fun (name, e) => (p, name, e, Logic.normalize (Logic.profileRules p) fuel e)

def bruleJson (b : BuildInfo) (e : Logic.LogicEntry) (v : Verification) : Json :=
  let r := e.rule
  Json.mkObj ([
    ("id", jstr r.id),
    ("description", jstr r.description),
    ("variables", Json.arr (r.vars.map omv).toArray),
    ("pattern", r.lhs.toOMJson),
    ("replacement", r.rhs.toOMJson),
    ("conditions", Json.arr #[]),
    ("orientation", jstr "forward"),
    ("applicability", jstr "defined_pattern"),
    ("profiles", jstrs r.profiles),
    ("priority", toJson r.priority),
    ("symbols", jstrs (r.symbols.map OMSymbol.uri)),
    ("provenance", provenanceJson r.provenance),
    ("verification", Json.arr #[verificationJson b "OSR.Logic" v]),
    ("findings", jstrs e.findings)] ++
    (match r.legacyId with | some l => [("legacy_id", jstr l)] | none => []) ++
    (if r.independent.isEmpty then [] else
      [("independent", Json.arr (r.independent.map fun (v, x) =>
        Json.mkObj [("variable", jstr v), ("of", jstr x)]).toArray)]))

def logicRulesetJson (b : BuildInfo) (audited : List (Logic.LogicEntry × Verification)) : Json :=
  let syms := (((audited.map (·.1.rule.symbols)).flatten ++ [Domain.boolean.carrier]).eraseDups).filterMap Registry.lookup
  Json.mkObj [
    ("osr_format", jstr formatVersion),
    ("ruleset", jstr "logic"),
    ("expression_encoding", Json.mkObj [
      ("standard", jstr "OpenMath 2.0 JSON encoding (2019 revision, section 3.3)"),
      ("cdbase", jstr OMSymbol.cdbase)]),
    ("build", Json.mkObj [
      ("generator", jstr "OpenSymbolicRules/Lean scripts/Export.lean"),
      ("lean_toolchain", jstr b.leanToolchain),
      ("mathlib_revision", jstr b.mathlibRevision),
      ("source_digest", jstr s!"sha256:{b.sourceDigest}")]),
    ("symbols", Json.arr (syms.map symbolJson).toArray),
    ("profiles", Json.mkObj (Logic.profiles.map fun p =>
      (p, Json.mkObj [("rules", jstrs ((Logic.profileRules p).map (·.id)))]))),
    ("rules", Json.arr (audited.map fun (e, v) => bruleJson b e v).toArray)]

unsafe def exportLogic (outDir : String) (build : BuildInfo) : MetaM Nat := do
  let ids := Logic.catalog.map (·.rule.id)
  unless ids.eraseDups.length == ids.length do
    throwError "duplicate rule identifiers in the Logic catalogue"
  let stuck := logicRuns.filter (!·.2.2.2.normal)
  unless stuck.isEmpty do
    throwError "logic: profiles do not terminate within {fuel} steps: {stuck.map fun r => (r.1, r.2.1)}"
  let termination ← Logic.profiles.mapM fun p => return (p, ← auditLogicTermination p)
  let mut audited := []
  for e in Logic.catalog do
    audited := audited ++ [(e, ← auditLogicEntry e)]
  IO.FS.writeFile (outDir ++ "/logic.osr.json") ((logicRulesetJson build audited).pretty ++ "\n")
  let proved := (audited.filter (·.2.status == .proved)).length
  let certified := (audited.filter (·.2.certified)).length
  let report := Json.mkObj [
    ("osr_format", jstr formatVersion),
    ("ruleset", jstr "logic"),
    ("build", Json.mkObj [("lean_toolchain", jstr build.leanToolchain),
      ("mathlib_revision", jstr build.mathlibRevision),
      ("source_digest", jstr s!"sha256:{build.sourceDigest}")]),
    ("metrics", Json.mkObj [
      ("rules_migrated", toJson audited.length),
      ("rules_exported", toJson audited.length),
      ("rules_not_migrated", toJson Logic.notMigrated.length),
      ("rules_with_findings", toJson (audited.filter (!·.1.findings.isEmpty)).length),
      ("boolean", Json.mkObj [("proved", toJson proved), ("certified", toJson certified),
        ("unproved", toJson 0), ("counterexample", toJson 0), ("unsupported", toJson 0),
        ("blocked_by_mapping_assurance", toJson (proved - certified))]),
      ("julia_execution", jstr "not measured by the exporter; see OpenSymbolicRules.jl test/test_osr_v1.jl")]),
    ("not_migrated", Json.arr (Logic.notMigrated.map fun (id, why) =>
      Json.mkObj [("legacy_id", jstr id), ("reason", jstr why)]).toArray),
    ("strategy", Json.mkObj [
      ("engine", jstr "OSR.Logic.normalize (reference rewriter, proved sound: OSR.Logic.normalize_sound)"),
      ("fuel", toJson fuel),
      ("seeds", toJson logicSeeds.length),
      ("profiles", Json.mkObj (Logic.profiles.map fun p =>
        let runs := logicRuns.filter (·.1 == p)
        (p, Json.mkObj [
          ("rules", jstrs ((Logic.profileRules p).map (·.id))),
          ("termination", (termination.lookup p).getD Json.null),
          ("terminates_on_seeds", toJson (runs.all (·.2.2.2.normal))),
          ("max_steps", toJson ((runs.map (·.2.2.2.trace.length)).foldl max 0))])))])]
  IO.FS.writeFile (outDir ++ "/logic.report.json") (report.pretty ++ "\n")
  let rows := audited.map fun (e, v) =>
    s!"| `{e.rule.id}` | `{e.rule.legacyId.getD "—"}` | {if v.certified then "proved, certified" else v.status.key} | `{e.proof}` |"
  let nm := String.intercalate "\n" (Logic.notMigrated.map fun (id, why) => s!"| `{id}` | {why} |")
  let profRows := Logic.profiles.map fun p =>
    let runs := logicRuns.filter (·.1 == p)
    let w := (logicTermination.find? (·.1 == p)).map (·.2.1.toString) |>.getD "—"
    let t := (logicTermination.find? (·.1 == p)).map (·.2.2.toString) |>.getD "—"
    s!"| `{p}` | {(Logic.profileRules p).length} | `{w}` | `{t}` | {(runs.map (·.2.2.2.trace.length)).foldl max 0} |"
  let md := s!"# Logic verification report

Generated by `scripts/Export.lean`. Do not edit by hand.

- Lean toolchain: `{build.leanToolchain}`
- Mathlib revision: `{build.mathlibRevision}`
- Source digest: `sha256:{build.sourceDigest}`
- Accepted axioms: `propext`, `Classical.choice`, `Quot.sound`

Rules are interpreted in the Boolean domain (carrier `setname2#Boolean`, Lean
`Bool`).  A rule is *certified* when its theorem `OSR.Logic.BRule.Holds rule`
(both sides have the same truth value for every assignment) is proved with
accepted axioms only **and** every OpenMath symbol it uses has a `reviewed` or
`formally_related` mapping.

## Metrics

| Metric | 𝔹 |
|---|---|
| Rules migrated | {audited.length} |
| Proved | {proved} |
| Certified | {certified} |
| Rules not migrated | {Logic.notMigrated.length} |

## Rules

| Rule | v0.1 identity | 𝔹 | Theorem |
|---|---|---|---|
" ++ String.intercalate "\n" rows ++ s!"

## Rules not migrated

| v0.1 identity | Reason |
|---|---|
" ++ nm ++ s!"

## Strategy

Termination of every profile is proved with a weight (`OSR.Logic.BasicWeight`).
Each profile is also run on {logicSeeds.length} seeds with a budget of {fuel}
steps; these runs are the conformance cases.

| Profile | Rules | Weight | Theorem | Max steps |
|---|---|---|---|---|
" ++ String.intercalate "\n" profRows ++ "\n"
  IO.FS.writeFile (outDir ++ "/logic.report.md") md
  let cases := Json.mkObj [
    ("osr_format", jstr formatVersion),
    ("suite", jstr "logic.rewrite"),
    ("ruleset", jstr "logic.osr.json"),
    ("source_digest", jstr s!"sha256:{build.sourceDigest}"),
    ("semantics", Json.mkObj [
      ("domain", jstr "boolean"),
      ("rules", jstr "the rules of the profile, unconditional only, in priority order"),
      ("strategy", jstr "outermost-leftmost: at each step, try the root (rules in order), then the arguments left to right; one rewrite per step"),
      ("matching", jstr "syntactic; a pattern variable occurring twice matches equal subterms; input OMV are constants"),
      ("fuel", toJson fuel),
      ("reference", jstr "OSR.Logic.normalize in OpenSymbolicRules/Lean (OSR/LogicCore.lean)")]),
    ("cases", Json.arr (logicRuns.map fun (p, name, e, n) =>
      Json.mkObj [
        ("id", jstr s!"{p}/{name}"),
        ("profile", jstr p),
        ("input", e.toOMJson),
        ("expected", n.result.toOMJson),
        ("trace", Json.arr (n.trace.map Json.str).toArray),
        ("normal", toJson n.normal)]).toArray)]
  IO.FS.writeFile (outDir ++ "/conformance/logic.cases.json") (cases.pretty ++ "\n")
  return audited.length

/-! ## Calculus -/

unsafe def evalCRule (decl : Name) : MetaM Calculus.CRule :=
  evalExpr Calculus.CRule (mkConst ``OSR.Calculus.CRule) (mkConst decl)

/-- Audit one calculus rule: declaration, well-formedness, registry symbols,
and for each listed domain a theorem of type exactly
`OSR.Calculus.CRule.Holds <decl> <domain>` with the standard axioms. -/
unsafe def auditCalcEntry (e : Calculus.CEntry) : MetaM (List Verification) := do
  let r ← evalCRule e.ruleDecl
  unless r == e.rule do
    throwError "{e.rule.id}: catalogue rule differs from declaration {e.ruleDecl}"
  unless e.rule.shape == .antiderivRec || e.rule.wellFormed do
    throwError "{e.rule.id}: ill-formed calculus rule"
  unless e.rule.recOk do
    throwError "{e.rule.id}: ill-formed residual integrals"
  unless e.rule.conditionsOk do
    throwError "{e.rule.id}: conditions mention the bound variable or a non-antiderivative rule has conditions"
  for s in e.rule.symbols do
    if (Registry.lookup s).isNone then
      throwError "{e.rule.id}: OpenMath symbol {s.uri} is not in the registry"
  let mut out := []
  for d in [Domain.real, Domain.complex] do
    let assurance := Registry.mappingAssurance e.rule.symbols d
    match e.proofs.lookup d with
    | some thm =>
      let some info := (← getEnv).find? thm
        | throwError "{e.rule.id}: proof {thm} does not exist"
      unless info matches .thmInfo _ do
        throwError "{e.rule.id}: {thm} is not a theorem"
      let domainConst := match d with
        | .real => ``OSR.Domain.real
        | .complex => ``OSR.Domain.complex
        | .boolean => ``OSR.Domain.boolean
      let expected := mkApp2 (mkConst ``OSR.Calculus.CRule.Holds) (mkConst e.ruleDecl)
        (mkConst domainConst)
      unless info.type == expected do
        throwError "{e.rule.id}: {thm} has type{indentExpr info.type}\nexpected{indentExpr expected}"
      let axioms := (← collectAxioms thm).toList.mergeSort (·.toString ≤ ·.toString)
      let forbidden := axioms.filter (· ∉ standardAxioms)
      unless forbidden.isEmpty do
        throwError "{e.rule.id}: {thm} depends on forbidden axioms {forbidden}"
      let v : Verification :=
        { domain := d, status := .proved, theoremName := some thm,
          statement := some s!"OSR.Calculus.CRule.Holds {e.ruleDecl} {domainConst}", axioms,
          mappingAssurance := assurance, certified := assurance.certifiable }
      out := out ++ [v]
    | none =>
      match e.counterexamples.lookup d with
      | some thm =>
        let some info := (← getEnv).find? thm
          | throwError "{e.rule.id}: counterexample {thm} does not exist"
        let domainConst := match d with
          | .real => ``OSR.Domain.real
          | .complex => ``OSR.Domain.complex
          | .boolean => ``OSR.Domain.boolean
        let expected := mkApp (mkConst ``Not) (mkApp2 (mkConst ``OSR.Calculus.CRule.Holds)
          (mkConst e.ruleDecl) (mkConst domainConst))
        unless info.type == expected do
          throwError "{e.rule.id}: {thm} has type{indentExpr info.type}\nexpected{indentExpr expected}"
        let axioms := (← collectAxioms thm).toList.mergeSort (·.toString ≤ ·.toString)
        unless (axioms.filter (· ∉ standardAxioms)).isEmpty do
          throwError "{e.rule.id}: {thm} depends on forbidden axioms"
        let v : Verification :=
          { domain := d, status := .counterexample, theoremName := some thm,
            statement := some s!"¬ OSR.Calculus.CRule.Holds {e.ruleDecl} {domainConst}", axioms,
            mappingAssurance := assurance, certified := false }
        out := out ++ [v]
      | none =>
        let status := if e.unproved.contains d then Status.unproved else Status.unsupported
        let v : Verification :=
          { domain := d, status, theoremName := none, statement := none, axioms := [],
            mappingAssurance := assurance, certified := false }
        out := out ++ [v]
  return out

private def tvar : OSR.Expr := .var "t"

/-- Inputs: every rule pattern, the patterns with another bound variable, and
inputs no rule matches. -/
def calcSeeds : List (String × Calculus.CTerm) :=
  (Calculus.catalog.map fun e =>
    let r := e.rule
    (s!"pattern.{r.id}", match r.shape with
      | .deriv => Calculus.CTerm.diff r.x r.body
      | .limit => Calculus.CTerm.limit r.point r.x r.body
      | .antideriv | .antiderivRec => Calculus.CTerm.integral r.x r.body)) ++
  (Calculus.catalog.map fun e =>
    let r := e.rule
    let σ : Subst := [(r.x, .var "t")]
    (s!"renamed.{r.id}", match r.shape with
      | .deriv => Calculus.CTerm.diff "t" (r.body.subst σ)
      | .limit => Calculus.CTerm.limit r.point "t" (r.body.subst σ)
      | .antideriv | .antiderivRec => Calculus.CTerm.integral "t" (r.body.subst σ))) ++
  [("independent.constant_body", .diff "t" (.app1 .sin (.var "u"))),
   ("independent.limit_of_constant", .limit (.int 1) "t" (.app1 .sin (.var "u"))),
   ("independent.body_mentions_bound", .diff "t" (.app2 .mul tvar (.var "u"))),
   ("nomatch.sin_of_double", .diff "t" (.app1 .sin (.app2 .mul (.int 2) tvar))),
   ("nomatch.limit_at_one", .limit (.int 1) "t" (.app2 .div (.app1 .sin tvar) tvar)),
   ("nomatch.square", .diff "t" (.pow tvar (.int 2))),
   ("normal.lambda", .lam "t" (.app1 .cos tvar))]

/-- Inputs of the Integration set: every rule pattern, the patterns with
another bound variable, and inputs no rule matches. -/
def intSeeds : List (String × Calculus.CTerm) :=
  (Integration.catalog.map fun e => (s!"pattern.{e.rule.id}", .integral e.rule.x e.rule.body)) ++
  (Integration.catalog.map fun e =>
    (s!"renamed.{e.rule.id}", .integral "t" (e.rule.body.subst [(e.rule.x, .var "t")]))) ++
  [("independent.body_mentions_bound", .integral "t" tvar),
   ("independent.constant_of_other_variable", .integral "t" (.app1 .sin (.var "u"))),
   ("nomatch.derivative", .diff "t" (.var "u")),
   ("normal.lambda", .lam "t" (.app2 .mul (.var "u") tvar)),
   ("decided.power_cubic", .integral "t" (.pow tvar (.int 3))),
   ("decided.power_minus_two", .integral "t" (.pow tvar (.int (-2)))),
   ("decided.power_minus_one", .integral "t" (.pow tvar (.int (-1)))),
   ("decided.sin_log_literal", .integral "t" (.app1 .sin (.app2 .mul (.int 1)
     (.app2 .add (.int 0) (.app2 .mul (.int 1) (.app1 .ln (.app2 .mul (.int 1)
       (.pow tvar (.int 1))))))))),
   ("undecided.power_symbolic", .integral "t" (.pow tvar (.var "m")))]

/-- A rule set of calculus rules (`OSR.Calculus.CRule`). -/
structure CalcSet where
  /-- File and identifier prefix. -/
  name : String
  title : String
  catalog : List Calculus.CEntry
  notMigrated : List (String × String)
  seeds : List (String × Calculus.CTerm)
  /-- Report paragraph stating what the rules mean. -/
  statement : String
  /-- Report paragraph on the strategy, before the seed count. -/
  strategy : String

/-- The rules the reference engine applies: those proved over ℝ (the domain of
the conformance cases), in priority order. -/
def CalcSet.rules (cs : CalcSet) : List Calculus.CRule :=
  (cs.catalog.filter fun e => (e.proofs.lookup .real).isSome).map (·.rule)

def calculusSet : CalcSet where
  name := "calculus"
  title := "Calculus"
  catalog := Calculus.catalog
  notMigrated := Calculus.notMigrated
  seeds := calcSeeds
  statement := "A derivative rule `diff(λx. F) ⟶ λx. G` states that wherever `F` is defined
near `t`, `v ↦ F[x := v]` has derivative `G[x := t]` at `t` (`HasDerivAt`). A
limit rule `limit(a, both_sides, λx. F) ⟶ L` states `Tendsto` along `𝓝[≠] a`."
  strategy := "Rules apply at the root of a `diff` or `limit` term (their bodies are field
expressions, to which no calculus rule applies); the result of a rule is a
lambda or a value, so normalization takes at most one step
(`OSR.Calculus.rewrite_result`)."

def integrationSet : CalcSet where
  name := "integration"
  title := "Integration"
  catalog := Integration.catalog
  notMigrated := Integration.notMigrated
  seeds := intSeeds
  statement := "An antiderivative rule `int(λx. F) ⟶ λx. G` (`calculus1#int`) states that
wherever `F` is defined near `t`, `G` is defined near `t` and `v ↦ G[x := v]`
has derivative `F[x := t]` at `t` (`HasDerivAt`), for every assignment of the
metavariables satisfying the rule's conditions. A recursive rule
`int(λx. F) ⟶ λx. G[int(λx. H)(x)]` states that the residual integrands are
defined near `t` and that, for every choice of antiderivatives of them, the
result is an antiderivative of `F`. The rules are the twenty RUBI 4.16.1 rules
of `OpenSymbolicRules/Integration` with no `Int` in their result, whose
conditions are `FreeQ` or `NeQ` and whose heads, the outer `Int` removed, are
in the registry, and 168 rules with residual integrals (161 migrated); the other
6,069 rules are not yet considered. The reference rewriter applies a
conditional rule only when its substituted conditions are closed and decided
true by exact rational arithmetic (`OSR.Cond.decide?`), and does not apply
recursive rules."
  strategy := "Rules apply at the root of an `int` term (their bodies are field expressions,
to which no calculus rule applies); the result of a rule is a lambda, so
normalization takes at most one step (`OSR.Calculus.rewrite_result`)."

def calcRuleJson (b : BuildInfo) (e : Calculus.CEntry) (vs : List Verification) : Json :=
  let r := e.rule
  Json.mkObj ([
    ("id", jstr r.id),
    ("description", jstr r.description),
    ("variables", Json.arr ((r.x :: (r.body.vars ++ r.point.vars ++
      r.result.vars.filter (· ∉ r.holes) ++ (r.integrals.map (·.2.vars)).flatten)).eraseDups.map
      omv).toArray),
    ("pattern", r.patternOM.toJson),
    ("replacement", r.replacementOM.toJson),
    ("conditions", Json.arr (r.conditions.map condJson).toArray),
    ("orientation", jstr "forward"),
    ("applicability", jstr "defined_pattern"),
    ("profiles", jstrs ["default"]),
    ("priority", toJson r.priority),
    ("symbols", jstrs (r.symbols.map OMSymbol.uri)),
    ("provenance", provenanceJson r.provenance),
    ("verification", Json.arr (vs.map (verificationJson b "OSR.Calculus")).toArray),
    ("findings", jstrs e.findings)] ++
    (match r.legacyId with | some l => [("legacy_id", jstr l)] | none => []) ++
    (if r.independent.isEmpty then [] else
      [("independent", Json.arr (r.independent.map fun c =>
        Json.mkObj [("variable", jstr c), ("of", jstr r.x)]).toArray)]))

unsafe def exportCalcSet (outDir : String) (build : BuildInfo) (cs : CalcSet) : MetaM Nat := do
  let ids := cs.catalog.map (·.rule.id)
  unless ids.eraseDups.length == ids.length do
    throwError "duplicate rule identifiers in the {cs.title} catalogue"
  let mut audited := []
  for e in cs.catalog do
    audited := audited ++ [(e, ← auditCalcEntry e)]
  let syms := ((audited.map (·.1.rule.symbols)).flatten.eraseDups).filterMap Registry.lookup
  let doc := Json.mkObj [
    ("osr_format", jstr formatVersion),
    ("ruleset", jstr cs.name),
    ("expression_encoding", Json.mkObj [
      ("standard", jstr "OpenMath 2.0 JSON encoding (2019 revision, section 3.3)"),
      ("cdbase", jstr OMSymbol.cdbase)]),
    ("build", Json.mkObj [
      ("generator", jstr "OpenSymbolicRules/Lean scripts/Export.lean"),
      ("lean_toolchain", jstr build.leanToolchain),
      ("mathlib_revision", jstr build.mathlibRevision),
      ("source_digest", jstr s!"sha256:{build.sourceDigest}")]),
    ("symbols", Json.arr (syms.map symbolJson).toArray),
    ("profiles", Json.mkObj [("default", Json.mkObj [("rules", jstrs ids)])]),
    ("rules", Json.arr (audited.map fun (e, vs) => calcRuleJson build e vs).toArray)]
  IO.FS.writeFile (outDir ++ s!"/{cs.name}.osr.json") (doc.pretty ++ "\n")
  let count (d : Domain) (p : Verification → Bool) :=
    (audited.filter fun (_, vs) => vs.any fun v => v.domain == d && p v).length
  let dom (d : Domain) := Json.mkObj [
    ("proved", toJson (count d (·.status == .proved))),
    ("certified", toJson (count d (·.certified))),
    ("unproved", toJson (count d (·.status == .unproved))),
    ("counterexample", toJson (count d (·.status == .counterexample))),
    ("unsupported", toJson (count d (·.status == .unsupported))),
    ("blocked_by_mapping_assurance", toJson (count d fun v => v.status == .proved && !v.certified))]
  let runs := cs.seeds.map fun (name, t) => (name, t, Calculus.rewrite cs.rules t)
  let report := Json.mkObj [
    ("osr_format", jstr formatVersion),
    ("ruleset", jstr cs.name),
    ("build", Json.mkObj [("lean_toolchain", jstr build.leanToolchain),
      ("mathlib_revision", jstr build.mathlibRevision),
      ("source_digest", jstr s!"sha256:{build.sourceDigest}")]),
    ("metrics", Json.mkObj [
      ("rules_migrated", toJson audited.length),
      ("rules_exported", toJson audited.length),
      ("rules_not_migrated", toJson cs.notMigrated.length),
      ("rules_with_findings", toJson (audited.filter (!·.1.findings.isEmpty)).length),
      ("real", dom .real), ("complex", dom .complex),
      ("julia_execution", jstr "not measured by the exporter; see OpenSymbolicRules.jl test/test_osr_v1.jl")]),
    ("not_migrated", Json.arr (cs.notMigrated.map fun (id, why) =>
      Json.mkObj [("legacy_id", jstr id), ("reason", jstr why)]).toArray),
    ("strategy", Json.mkObj [
      ("engine", jstr "OSR.Calculus.rewrite (root rewriting; proved sound: OSR.Calculus.apply?_sound)"),
      ("termination", Json.mkObj [("status", jstr "proved"),
        ("theorem", jstr "OSR.Calculus.rewrite_result"),
        ("statement", jstr "no rule applies to the result of a rule: normalization takes at most one step")]),
      ("seeds", toJson cs.seeds.length)])]
  IO.FS.writeFile (outDir ++ s!"/{cs.name}.report.json") (report.pretty ++ "\n")
  let cell (vs : List Verification) (d : Domain) : String :=
    match vs.find? (·.domain == d) with
    | some v => if v.status == .proved then
        (if v.certified then "proved, certified" else s!"proved, not certified ({v.mappingAssurance.key} mapping)")
      else v.status.key
    | none => "—"
  let rows := audited.map fun (e, vs) =>
    s!"| `{e.rule.id}` | `{e.rule.legacyId.getD "—"}` | {cell vs .real} | {cell vs .complex} |"
  let nm := String.intercalate "\n" (cs.notMigrated.map fun (id, why) => s!"| `{id}` | {why} |")
  let findings := audited.filter (!·.1.findings.isEmpty) |>.map fun (e, _) =>
    s!"### `{e.rule.id}`\n\n" ++ String.intercalate "\n" (e.findings.map ("- " ++ ·))
  let md := s!"# {cs.title} verification report

Generated by `scripts/Export.lean`. Do not edit by hand.

- Lean toolchain: `{build.leanToolchain}`
- Mathlib revision: `{build.mathlibRevision}`
- Source digest: `sha256:{build.sourceDigest}`
- Accepted axioms: `propext`, `Classical.choice`, `Quot.sound`

{cs.statement}

## Metrics

| Metric | ℝ | ℂ |
|---|---|---|
| Rules migrated | {audited.length} | {audited.length} |
| Proved | {count .real (·.status == .proved)} | {count .complex (·.status == .proved)} |
| Certified | {count .real (·.certified)} | {count .complex (·.certified)} |
| Unproved | {count .real (·.status == .unproved)} | {count .complex (·.status == .unproved)} |
| Counterexamples | {count .real (·.status == .counterexample)} | {count .complex (·.status == .counterexample)} |
| Rules not migrated | {cs.notMigrated.length} | {cs.notMigrated.length} |

## Rules

| Rule | v0.1 identity | ℝ | ℂ |
|---|---|---|---|
" ++ String.intercalate "\n" rows ++ "

## Rules not migrated

| v0.1 identity | Reason |
|---|---|
" ++ nm ++ "

## Findings

" ++ String.intercalate "\n\n" findings ++ s!"

## Strategy

{cs.strategy} The {cs.seeds.length} seeds below are the
conformance cases.
"
  IO.FS.writeFile (outDir ++ s!"/{cs.name}.report.md") md
  let cases := Json.mkObj [
    ("osr_format", jstr formatVersion),
    ("suite", jstr s!"{cs.name}.rewrite"),
    ("ruleset", jstr s!"{cs.name}.osr.json"),
    ("source_digest", jstr s!"sha256:{build.sourceDigest}"),
    ("semantics", Json.mkObj [
      ("domain", jstr "real"),
      ("rules", jstr "the rules of the profile certified over the reals, in priority order"),
      ("strategy", jstr "outermost-leftmost: at each step, try the root (rules in order), then the arguments left to right; one rewrite per step"),
      ("matching", jstr "syntactic; a pattern's bound variable matches the input's bound variable; integers compare by value"),
      ("conditions", jstr "a conditional rule applies only when each of its conditions, with the match substituted, is closed (integers, +, -, *, /, unary minus, integer powers) and decided true by exact rational arithmetic; otherwise it is left alone"),
      ("fuel", toJson fuel),
      ("reference", jstr "OSR.Calculus.rewrite in OpenSymbolicRules/Lean (OSR/Calculus.lean)")]),
    ("cases", Json.arr (runs.map fun (name, t, res) =>
      Json.mkObj [
        ("id", jstr s!"default/{name}"),
        ("profile", jstr "default"),
        ("input", t.toOM.toJson),
        ("expected", ((res.map (·.2)).getD t).toOM.toJson),
        ("trace", Json.arr ((res.map fun (id, _) => #[jstr id]).getD #[])),
        ("normal", toJson true)]).toArray)]
  IO.FS.writeFile (outDir ++ s!"/conformance/{cs.name}.cases.json") (cases.pretty ++ "\n")
  return audited.length

unsafe def runExport : MetaM Unit := do
  let some outDir ← IO.getEnv "OSR_OUT_DIR" | throwError "OSR_OUT_DIR is not set"
  let some digest ← IO.getEnv "OSR_SOURCE_DIGEST" | throwError "OSR_SOURCE_DIGEST is not set"
  let toolchain := (← IO.FS.readFile "lean-toolchain").replace "\n" ""
  let build : BuildInfo :=
    { leanToolchain := toolchain, mathlibRevision := ← mathlibRevision, sourceDigest := digest }
  auditRegistry
  IO.FS.createDirAll (outDir ++ "/conformance")
  let registry := Json.mkObj [
    ("osr_format", Json.str formatVersion),
    ("cdbase", Json.str OMSymbol.cdbase),
    ("symbols", Json.arr (Registry.entries.map symbolJson).toArray)]
  IO.FS.writeFile (outDir ++ "/registry.json") (registry.pretty ++ "\n")
  for rs in ruleSets do
    let n ← exportRuleSet outDir build rs
    logInfo m!"exported {n} {rs.name} rules to {outDir}"
  let n ← exportLogic outDir build
  logInfo m!"exported {n} logic rules to {outDir}"
  for cs in [calculusSet, integrationSet] do
    let n ← exportCalcSet outDir build cs
    logInfo m!"exported {n} {cs.name} rules to {outDir}"

#eval runExport
