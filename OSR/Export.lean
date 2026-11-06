import OSR.Catalog

/-!
# OSR v1 interchange encoding

Pure rendering of rules, registry entries and verification records to JSON.
Facts that require the Lean environment (theorem types, axioms) are gathered
by `scripts/Export.lean` and passed in as `Verification` values.

Expressions use the normative OpenMath 2.0 JSON encoding (OpenMath 2.0,
revision 2019, §3.3).  Lean's `Json` objects are ordered by key, so
`Json.pretty`/`Json.compress` output is deterministic.
-/

namespace OSR.Export

open Lean (Json)
open OSR

/-- Version of the interchange format produced by this exporter. -/
def formatVersion : String := "1.0.0-alpha.1"

/-- Proof status of a rule in a domain. -/
inductive Status where
  | proved
  | unproved
  | counterexample
  | unsupported
  | generationError
  deriving DecidableEq, Repr, BEq

/-- Stable key of a status. -/
def Status.key : Status → String
  | .proved => "proved"
  | .unproved => "unproved"
  | .counterexample => "counterexample"
  | .unsupported => "unsupported"
  | .generationError => "generation_error"

/-- Verification facts for one rule in one domain. -/
structure Verification where
  domain : Domain
  status : Status
  theoremName : Option Lean.Name
  /-- The checked statement, e.g. `OSR.Rule.Holds OSR.Trigonometry.pythagorean OSR.Domain.real`. -/
  statement : Option String
  axioms : List Lean.Name
  mappingAssurance : Assurance
  /-- Proved, standard axioms only, and certifiable mapping assurance. -/
  certified : Bool
  deriving Repr

/-- Build-wide reproducibility information. -/
structure BuildInfo where
  leanToolchain : String
  mathlibRevision : String
  /-- SHA-256 over the sorted list of `sha256  path` lines of the Lean sources,
  `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`. -/
  sourceDigest : String
  deriving Repr

private def str (s : String) : Json := Json.str s
private def strs (l : List String) : Json := Json.arr (l.map Json.str).toArray
private def opt (k : String) (v : Option String) : List (String × Json) :=
  match v with
  | some s => [(k, Json.str s)]
  | none => []

/-- An OMV variable. -/
def omv (n : String) : Json := Json.mkObj [("kind", str "OMV"), ("name", str n)]

/-- A condition as an OpenMath application. -/
def condJson : Cond → Json
  | .ne a b => Expr.omaJson ⟨"relation1", "neq"⟩ [a.toOMJson, b.toOMJson]
  | .gt a b => Expr.omaJson ⟨"relation1", "gt"⟩ [a.toOMJson, b.toOMJson]

/-- Provenance as JSON. -/
def provenanceJson (p : Provenance) : Json :=
  Json.mkObj [
    ("method", str p.method.key),
    ("sources", Json.arr (p.sources.map fun s =>
      Json.mkObj ([("name", str s.name), ("locator", str s.locator)] ++
        opt "revision" s.revision ++ opt "license" s.license)).toArray)]

/-- A verification record as JSON. -/
def verificationJson (b : BuildInfo) (module : String) (v : Verification) : Json :=
  Json.mkObj ([
    ("domain", str v.domain.key),
    ("carrier", Expr.omsJson v.domain.carrier),
    ("status", str v.status.key),
    ("certified", Json.bool v.certified),
    ("mapping_assurance", str v.mappingAssurance.key),
    ("prover", str "lean4"),
    ("lean_toolchain", str b.leanToolchain),
    ("mathlib_revision", str b.mathlibRevision),
    ("source_digest", str s!"sha256:{b.sourceDigest}"),
    ("module", str module),
    ("axioms", strs (v.axioms.map toString))] ++
    opt "theorem" (v.theoremName.map toString) ++
    opt "statement" v.statement)

/-- A rule as JSON. -/
def ruleJson (b : BuildInfo) (module : String) (e : CatalogEntry) (vs : List Verification) : Json :=
  let r := e.rule
  Json.mkObj ([
    ("id", str r.id),
    ("description", str r.description),
    ("variables", Json.arr (r.vars.map omv).toArray),
    ("pattern", r.lhs.toOMJson),
    ("replacement", r.rhs.toOMJson),
    ("conditions", Json.arr (r.conditions.map condJson).toArray),
    ("orientation", str "forward"),
    ("applicability", str "defined_pattern"),
    ("profiles", strs r.profiles),
    ("priority", Lean.toJson r.priority),
    ("symbols", strs (r.symbols.map OMSymbol.uri)),
    ("provenance", provenanceJson r.provenance),
    ("verification", Json.arr (vs.map (verificationJson b module)).toArray),
    ("findings", strs e.findings)] ++
    opt "legacy_id" r.legacyId)

/-- A registry entry as JSON. -/
def symbolJson (e : SymbolEntry) : Json :=
  let cd := Registry.cds.find? (·.cd == e.symbol.cd)
  Json.mkObj ([
    ("cd", str e.symbol.cd),
    ("name", str e.symbol.name),
    ("uri", str e.symbol.uri),
    ("arity", Lean.toJson e.arity),
    ("fragment", str e.fragment),
    ("interpretations", Json.arr (e.interpretations.map fun i =>
      Json.mkObj [
        ("domain", str i.domain.key),
        ("lean", str (toString i.leanConst)),
        ("assurance", str i.assurance.key),
        ("definedness", str i.definedness),
        ("justification", str i.justification),
        ("obligations", Json.arr (i.obligations.map fun o =>
          Json.mkObj [("cmp", str o.cmp), ("theorem", str (toString o.theoremName)),
            ("note", str o.note)]).toArray),
        ("unresolved", strs i.unresolved)]).toArray)] ++
    match cd with
    | some c => [("cd_version", Lean.toJson c.version), ("cd_revision", Lean.toJson c.revision),
                 ("cd_date", str c.date), ("cd_sha256", str c.sha256)]
    | none => [])

/-- Profiles: rule ids of each profile, ordered by priority then catalogue order. -/
def profilesJson (entries : List CatalogEntry) : Json :=
  let names := (entries.map (·.rule.profiles)).flatten.eraseDups
  Json.mkObj (names.map fun p =>
    let rs := entries.filter (p ∈ ·.rule.profiles)
    let sorted := rs.mergeSort (fun e f => e.rule.priority ≤ f.rule.priority)
    (p, Json.mkObj [("rules", strs (sorted.map (·.rule.id)))]))

/-- A complete rule-set document. -/
def rulesetJson (name : String) (b : BuildInfo) (module : String)
    (entries : List (CatalogEntry × List Verification)) : Json :=
  let syms := ((entries.map (·.1.rule.symbols)).flatten.eraseDups).filterMap Registry.lookup
  Json.mkObj [
    ("osr_format", str formatVersion),
    ("ruleset", str name),
    ("expression_encoding", Json.mkObj [
      ("standard", str "OpenMath 2.0 JSON encoding (2019 revision, section 3.3)"),
      ("cdbase", str OMSymbol.cdbase)]),
    ("build", Json.mkObj [
      ("generator", str "OpenSymbolicRules/Lean scripts/Export.lean"),
      ("lean_toolchain", str b.leanToolchain),
      ("mathlib_revision", str b.mathlibRevision),
      ("source_digest", str s!"sha256:{b.sourceDigest}")]),
    ("symbols", Json.arr (syms.map symbolJson).toArray),
    ("profiles", profilesJson (entries.map (·.1))),
    ("rules", Json.arr (entries.map fun (e, vs) => ruleJson b module e vs).toArray)]

end OSR.Export
