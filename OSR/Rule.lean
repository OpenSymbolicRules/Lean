import OSR.Interp

/-!
# OSR rules

A `Rule` is an oriented rewrite `lhs ⟶ rhs` with explicit variables,
conditions and operational metadata.  Its mathematical content is the
proposition `Rule.Holds r d`, computed from the rule data itself:

> for every assignment satisfying the conditions, if the pattern is defined
> then the replacement is defined and has the same value.

This is the soundness property a rewriting engine needs for a forward
rewrite: rewriting never turns a meaningful expression into a different value
or into a meaningless one.  Because the statement is derived from the same
`Expr` values that the exporter serializes, the proved theorem and the exported
rule describe the same transformation (see `docs/trust-model.md` for what this
does and does not guarantee).

Rewrite *strategy* — ordering, repetition, termination — is not part of the
statement.  Profiles and priorities are metadata for engines.
-/

namespace OSR

/-- An explicit side condition of a rule. -/
inductive Cond where
  /-- The two expressions are defined and have different values. -/
  | ne (a b : Expr)
  /-- The two expressions are defined and the first is greater than the second
  (`relation1#gt`). -/
  | gt (a b : Expr)
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Cond

/-- Variables occurring in a condition. -/
def vars : Cond → List String
  | .ne a b | .gt a b => (a.vars ++ b.vars).eraseDups

/-- OpenMath symbols occurring in a condition (`relation1#neq` included). -/
def symbols : Cond → List OMSymbol
  | .ne a b => (⟨"relation1", "neq"⟩ :: a.symbols ++ b.symbols).eraseDups
  | .gt a b => (⟨"relation1", "gt"⟩ :: a.symbols ++ b.symbols).eraseDups

variable {α : Type} [Field α]

/-- Meaning of a condition. -/
def Holds (I : Interp α) (env : String → α) : Cond → Prop
  | .ne a b => Defined I env a ∧ Defined I env b ∧ eval I env a ≠ eval I env b
  | .gt a b => Defined I env a ∧ Defined I env b ∧ I.lt (eval I env b) (eval I env a)

end Cond

/-- How the rule was obtained. -/
inductive ProvenanceMethod where
  | authored
  | transcribed
  | converted
  | derived
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Stable key of a provenance method. -/
def ProvenanceMethod.key : ProvenanceMethod → String
  | .authored => "authored"
  | .transcribed => "transcribed"
  | .converted => "converted"
  | .derived => "derived"

/-- A provenance source. -/
structure Source where
  name : String
  locator : String
  revision : Option String := none
  license : Option String := none
  deriving Repr, Inhabited, BEq

/-- Provenance of a rule. -/
structure Provenance where
  method : ProvenanceMethod
  sources : List Source
  deriving Repr, Inhabited, BEq

/-- An oriented rewrite rule with metadata. -/
structure Rule where
  /-- Canonical, dotted identifier, e.g. `trigonometry.pythagorean`. -/
  id : String
  /-- Identity of the corresponding OSR v0.1 rule, when migrated. -/
  legacyId : Option String := none
  /-- Variables bound by the rule, in declaration order. -/
  vars : List String
  lhs : Expr
  rhs : Expr
  conditions : List Cond := []
  /-- Rewrite profiles in which the rule participates. -/
  profiles : List String
  /-- Engine priority within a profile; lower values are tried first. -/
  priority : Nat
  description : String
  provenance : Provenance
  deriving Repr, Inhabited, BEq

namespace Rule

/-- OpenMath symbols used by the rule, in first-use order. -/
def symbols (r : Rule) : List OMSymbol :=
  (r.lhs.symbols ++ r.rhs.symbols ++ (r.conditions.map Cond.symbols).flatten).eraseDups

/-- Structural problems that make a rule unusable as a rewrite.  The empty
list means the rule is well formed. -/
def wellFormed (r : Rule) : List String :=
  let lhsVars := r.lhs.vars
  let used := (lhsVars ++ r.rhs.vars ++ (r.conditions.map Cond.vars).flatten).eraseDups
  (if r.vars.eraseDups.length == r.vars.length then [] else ["duplicate variable declaration"]) ++
  (if r.lhs.isVar then ["pattern is a bare variable"] else []) ++
  (used.filter (· ∉ r.vars)).map (s!"undeclared variable {·}") ++
  (r.vars.filter (· ∉ lhsVars)).map (s!"variable {·} is not bound by the pattern") ++
  (if r.profiles.isEmpty then ["rule belongs to no profile"] else [])

variable {α : Type} [Field α]

/-- Soundness of the forward rewrite under an interpretation. -/
def Sound (r : Rule) (I : Interp α) : Prop :=
  ∀ env : String → α, (∀ c ∈ r.conditions, c.Holds I env) →
    Defined I env r.lhs → Defined I env r.rhs ∧ eval I env r.lhs = eval I env r.rhs

end Rule

/-- The proposition certified for a rule in a domain. -/
def Rule.Holds (r : Rule) : Domain → Prop
  | .real => r.Sound Interp.real
  | .complex => r.Sound Interp.complex

end OSR
