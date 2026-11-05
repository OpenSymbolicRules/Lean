import OSR.Semantics

/-!
# Rule catalogues

A catalogue entry ties a rule declaration to the theorems certifying it in
each domain.  The exporter checks, in the Lean environment, that every listed
theorem has exactly the type `Rule.Holds <rule> <domain>` and audits its
axioms, so the names here cannot point at an unrelated theorem.
-/

namespace OSR

/-- A rule together with its proofs and migration findings. -/
structure CatalogEntry where
  rule : Rule
  /-- The declaration defining `rule`. -/
  ruleDecl : Lean.Name
  /-- Theorems proving `Rule.Holds rule d`, per domain. -/
  proofs : List (Domain × Lean.Name)
  /-- Domains attempted without a complete proof. -/
  unproved : List Domain := []
  /-- Migration findings (missing hypotheses, semantic gaps, …). -/
  findings : List String := []
  deriving Repr, Inhabited

/-- Unfold `Rule.Holds r I` into its Lean meaning and introduce the
assignment and the definedness hypothesis `hd`. -/
syntax "osr_intro" ident ident : tactic

macro_rules
  | `(tactic| osr_intro $r:ident $i:ident) => do
    -- `hd` is deliberately unhygienic so that proofs can use the hypothesis.
    let hd := Lean.mkIdent `hd
    `(tactic|
      (simp only [Rule.Holds, Rule.Sound]
       intro env _ $hd:ident
       simp only [$r:ident, $i:ident, Defined, eval, Int.cast_ofNat, Int.cast_one,
         Int.cast_neg, true_and, and_true] at $hd:ident ⊢))

end OSR
