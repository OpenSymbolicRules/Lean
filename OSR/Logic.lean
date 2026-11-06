import OSR.LogicCore

/-!
# Logic

Migration of the propositional rules of `OpenSymbolicRules/Logic` at commit
`9e1789735df1b91e82029fa3eb44010f224b8065`: 35 of its 39 rules, interpreted
in the Boolean domain (`logic1` connectives on Lean's `Bool`, `quant1`
quantifiers over the truth values).  The other 4 need a "variable not free"
side condition, which has no OpenMath symbol (`notMigrated`).

Each rule is proved by evaluating both sides for every truth value of its
variables.  The three profiles follow v0.1: `default` simplifies, pushes
negations inward and eliminates derived connectives; `to_cnf` and `to_dnf`
add distribution in opposite directions.  Each has a termination proof.
-/

namespace OSR.Logic

open OSR

private def repo : String := "OpenSymbolicRules/Logic"
private def rev : String := "9e1789735df1b91e82029fa3eb44010f224b8065"

private def migrated (legacy : String) : Provenance :=
  { method := .derived,
    sources := [{ name := repo, locator := legacy, revision := some rev, license := some "MIT" }] }

/-- Every profile of the rule set. -/
def profiles : List String := ["default", "to_cnf", "to_dnf"]

/-! ## Rules -/

/-- Disjunction with false is the original proposition. -/
def orFalse : BRule where
  id := "logic.identity.or_false"
  legacyId := some "logic:1-identities/1.1-boolean-identities:1"
  vars := ["p"]
  lhs := (.bin .or (.var "p") .ff)
  rhs := (.var "p")
  profiles := profiles
  priority := 10
  description := "Disjunction with false is the original proposition."
  provenance := migrated "logic:1-identities/1.1-boolean-identities:1"

/-- Conjunction with true is the original proposition. -/
def andTrue : BRule where
  id := "logic.identity.and_true"
  legacyId := some "logic:1-identities/1.1-boolean-identities:2"
  vars := ["p"]
  lhs := (.bin .and (.var "p") .tt)
  rhs := (.var "p")
  profiles := profiles
  priority := 20
  description := "Conjunction with true is the original proposition."
  provenance := migrated "logic:1-identities/1.1-boolean-identities:2"

/-- Conjunction with false is false. -/
def andFalse : BRule where
  id := "logic.identity.and_false"
  legacyId := some "logic:1-identities/1.1-boolean-identities:3"
  vars := ["p"]
  lhs := (.bin .and (.var "p") .ff)
  rhs := .ff
  profiles := profiles
  priority := 30
  description := "Conjunction with false is false."
  provenance := migrated "logic:1-identities/1.1-boolean-identities:3"

/-- Repeated disjunction operands collapse to one proposition. -/
def orSelf : BRule where
  id := "logic.identity.or_self"
  legacyId := some "logic:1-identities/1.1-boolean-identities:4"
  vars := ["p"]
  lhs := (.bin .or (.var "p") (.var "p"))
  rhs := (.var "p")
  profiles := profiles
  priority := 40
  description := "Repeated disjunction operands collapse to one proposition."
  provenance := migrated "logic:1-identities/1.1-boolean-identities:4"

/-- Repeated conjunction operands collapse to one proposition. -/
def andSelf : BRule where
  id := "logic.identity.and_self"
  legacyId := some "logic:1-identities/1.1-boolean-identities:5"
  vars := ["p"]
  lhs := (.bin .and (.var "p") (.var "p"))
  rhs := (.var "p")
  profiles := profiles
  priority := 50
  description := "Repeated conjunction operands collapse to one proposition."
  provenance := migrated "logic:1-identities/1.1-boolean-identities:5"

/-- Disjunction with false is the original proposition. -/
def falseOr : BRule where
  id := "logic.identity.false_or"
  legacyId := some "logic:1-identities/1.2-boolean-symmetry:6"
  vars := ["p"]
  lhs := (.bin .or .ff (.var "p"))
  rhs := (.var "p")
  profiles := profiles
  priority := 60
  description := "Disjunction with false is the original proposition."
  provenance := migrated "logic:1-identities/1.2-boolean-symmetry:6"

/-- Conjunction with true is the original proposition. -/
def trueAnd : BRule where
  id := "logic.identity.true_and"
  legacyId := some "logic:1-identities/1.2-boolean-symmetry:7"
  vars := ["p"]
  lhs := (.bin .and .tt (.var "p"))
  rhs := (.var "p")
  profiles := profiles
  priority := 70
  description := "Conjunction with true is the original proposition."
  provenance := migrated "logic:1-identities/1.2-boolean-symmetry:7"

/-- Disjunction with true is true. -/
def orTrue : BRule where
  id := "logic.identity.or_true"
  legacyId := some "logic:1-identities/1.2-boolean-symmetry:8"
  vars := ["p"]
  lhs := (.bin .or (.var "p") .tt)
  rhs := .tt
  profiles := profiles
  priority := 80
  description := "Disjunction with true is true."
  provenance := migrated "logic:1-identities/1.2-boolean-symmetry:8"

/-- Disjunction with true is true. -/
def trueOr : BRule where
  id := "logic.identity.true_or"
  legacyId := some "logic:1-identities/1.2-boolean-symmetry:9"
  vars := ["p"]
  lhs := (.bin .or .tt (.var "p"))
  rhs := .tt
  profiles := profiles
  priority := 90
  description := "Disjunction with true is true."
  provenance := migrated "logic:1-identities/1.2-boolean-symmetry:9"

/-- Conjunction with false is false. -/
def falseAnd : BRule where
  id := "logic.identity.false_and"
  legacyId := some "logic:1-identities/1.2-boolean-symmetry:10"
  vars := ["p"]
  lhs := (.bin .and .ff (.var "p"))
  rhs := .ff
  profiles := profiles
  priority := 100
  description := "Conjunction with false is false."
  provenance := migrated "logic:1-identities/1.2-boolean-symmetry:10"

/-- Negating a proposition twice returns that proposition. -/
def notNot : BRule where
  id := "logic.negation.not_not"
  legacyId := some "logic:2-negation/2.1-complements:11"
  vars := ["p"]
  lhs := (.not (.not (.var "p")))
  rhs := (.var "p")
  profiles := profiles
  priority := 110
  description := "Negating a proposition twice returns that proposition."
  provenance := migrated "logic:2-negation/2.1-complements:11"

/-- A proposition disjoined with its complement is true. -/
def orNotSelf : BRule where
  id := "logic.negation.or_not_self"
  legacyId := some "logic:2-negation/2.1-complements:12"
  vars := ["p"]
  lhs := (.bin .or (.var "p") (.not (.var "p")))
  rhs := .tt
  profiles := profiles
  priority := 120
  description := "A proposition disjoined with its complement is true."
  provenance := migrated "logic:2-negation/2.1-complements:12"

/-- A proposition conjoined with its complement is false. -/
def andNotSelf : BRule where
  id := "logic.negation.and_not_self"
  legacyId := some "logic:2-negation/2.1-complements:13"
  vars := ["p"]
  lhs := (.bin .and (.var "p") (.not (.var "p")))
  rhs := .ff
  profiles := profiles
  priority := 130
  description := "A proposition conjoined with its complement is false."
  provenance := migrated "logic:2-negation/2.1-complements:13"

/-- De Morgan's law for the negation of a conjunction. -/
def notAnd : BRule where
  id := "logic.negation.not_and"
  legacyId := some "logic:2-negation/2.2-negation-normal-form:14"
  vars := ["p", "q"]
  lhs := (.not (.bin .and (.var "p") (.var "q")))
  rhs := (.bin .or (.not (.var "p")) (.not (.var "q")))
  profiles := profiles
  priority := 140
  description := "De Morgan's law for the negation of a conjunction."
  provenance := migrated "logic:2-negation/2.2-negation-normal-form:14"

/-- De Morgan's law for the negation of a disjunction. -/
def notOr : BRule where
  id := "logic.negation.not_or"
  legacyId := some "logic:2-negation/2.2-negation-normal-form:15"
  vars := ["p", "q"]
  lhs := (.not (.bin .or (.var "p") (.var "q")))
  rhs := (.bin .and (.not (.var "p")) (.not (.var "q")))
  profiles := profiles
  priority := 150
  description := "De Morgan's law for the negation of a disjunction."
  provenance := migrated "logic:2-negation/2.2-negation-normal-form:15"

/-- The negation of true is false. -/
def notTrue : BRule where
  id := "logic.negation.not_true"
  legacyId := some "logic:2-negation/2.2-negation-normal-form:16"
  vars := []
  lhs := (.not .tt)
  rhs := .ff
  profiles := profiles
  priority := 160
  description := "The negation of true is false."
  provenance := migrated "logic:2-negation/2.2-negation-normal-form:16"

/-- The negation of false is true. -/
def notFalse : BRule where
  id := "logic.negation.not_false"
  legacyId := some "logic:2-negation/2.2-negation-normal-form:17"
  vars := []
  lhs := (.not .ff)
  rhs := .tt
  profiles := profiles
  priority := 170
  description := "The negation of false is true."
  provenance := migrated "logic:2-negation/2.2-negation-normal-form:17"

/-- A proposition absorbs its conjunction with another proposition. -/
def orAndLeft : BRule where
  id := "logic.absorption.or_and_left"
  legacyId := some "logic:3-absorption/3.1-absorption:18"
  vars := ["p", "q"]
  lhs := (.bin .or (.var "p") (.bin .and (.var "p") (.var "q")))
  rhs := (.var "p")
  profiles := profiles
  priority := 180
  description := "A proposition absorbs its conjunction with another proposition."
  provenance := migrated "logic:3-absorption/3.1-absorption:18"

/-- A proposition absorbs its conjunction with another proposition. -/
def orAndRight : BRule where
  id := "logic.absorption.or_and_right"
  legacyId := some "logic:3-absorption/3.1-absorption:19"
  vars := ["p", "q"]
  lhs := (.bin .or (.bin .and (.var "p") (.var "q")) (.var "p"))
  rhs := (.var "p")
  profiles := profiles
  priority := 190
  description := "A proposition absorbs its conjunction with another proposition."
  provenance := migrated "logic:3-absorption/3.1-absorption:19"

/-- A proposition absorbs its disjunction with another proposition. -/
def andOrLeft : BRule where
  id := "logic.absorption.and_or_left"
  legacyId := some "logic:3-absorption/3.1-absorption:20"
  vars := ["p", "q"]
  lhs := (.bin .and (.var "p") (.bin .or (.var "p") (.var "q")))
  rhs := (.var "p")
  profiles := profiles
  priority := 200
  description := "A proposition absorbs its disjunction with another proposition."
  provenance := migrated "logic:3-absorption/3.1-absorption:20"

/-- A proposition absorbs its disjunction with another proposition. -/
def andOrRight : BRule where
  id := "logic.absorption.and_or_right"
  legacyId := some "logic:3-absorption/3.1-absorption:21"
  vars := ["p", "q"]
  lhs := (.bin .and (.bin .or (.var "p") (.var "q")) (.var "p"))
  rhs := (.var "p")
  profiles := profiles
  priority := 210
  description := "A proposition absorbs its disjunction with another proposition."
  provenance := migrated "logic:3-absorption/3.1-absorption:21"

/-- An implication is a disjunction with a negated antecedent. -/
def impliesElim : BRule where
  id := "logic.connective.implies"
  legacyId := some "logic:4-connectives/4.1-derived-connectives:22"
  vars := ["p", "q"]
  lhs := (.bin .implies (.var "p") (.var "q"))
  rhs := (.bin .or (.not (.var "p")) (.var "q"))
  profiles := profiles
  priority := 220
  description := "An implication is a disjunction with a negated antecedent."
  provenance := migrated "logic:4-connectives/4.1-derived-connectives:22"

/-- Logical equivalence is the conjunction of its two implication-free directions. -/
def equivalentElim : BRule where
  id := "logic.connective.equivalent"
  legacyId := some "logic:4-connectives/4.1-derived-connectives:23"
  vars := ["p", "q"]
  lhs := (.bin .equivalent (.var "p") (.var "q"))
  rhs := (.bin .and (.bin .or (.not (.var "p")) (.var "q")) (.bin .or (.not (.var "q")) (.var "p")))
  profiles := profiles
  priority := 230
  description := "Logical equivalence is the conjunction of its two implication-free directions."
  provenance := migrated "logic:4-connectives/4.1-derived-connectives:23"

/-- NAND is the negation of conjunction. -/
def nandElim : BRule where
  id := "logic.connective.nand"
  legacyId := some "logic:4-connectives/4.2-compound-connectives:28"
  vars := ["p", "q"]
  lhs := (.bin .nand (.var "p") (.var "q"))
  rhs := (.not (.bin .and (.var "p") (.var "q")))
  profiles := profiles
  priority := 240
  description := "NAND is the negation of conjunction."
  provenance := migrated "logic:4-connectives/4.2-compound-connectives:28"

/-- NOR is the negation of disjunction. -/
def norElim : BRule where
  id := "logic.connective.nor"
  legacyId := some "logic:4-connectives/4.2-compound-connectives:29"
  vars := ["p", "q"]
  lhs := (.bin .nor (.var "p") (.var "q"))
  rhs := (.not (.bin .or (.var "p") (.var "q")))
  profiles := profiles
  priority := 250
  description := "NOR is the negation of disjunction."
  provenance := migrated "logic:4-connectives/4.2-compound-connectives:29"

/-- Exclusive disjunction holds when exactly one operand is true. -/
def xorElim : BRule where
  id := "logic.connective.xor"
  legacyId := some "logic:4-connectives/4.2-compound-connectives:30"
  vars := ["p", "q"]
  lhs := (.bin .xor (.var "p") (.var "q"))
  rhs := (.bin .or (.bin .and (.var "p") (.not (.var "q"))) (.bin .and (.not (.var "p")) (.var "q")))
  profiles := profiles
  priority := 260
  description := "Exclusive disjunction holds when exactly one operand is true."
  provenance := migrated "logic:4-connectives/4.2-compound-connectives:30"

/-- Exclusive NOR holds when both operands have the same truth value. -/
def xnorElim : BRule where
  id := "logic.connective.xnor"
  legacyId := some "logic:4-connectives/4.2-compound-connectives:31"
  vars := ["p", "q"]
  lhs := (.bin .xnor (.var "p") (.var "q"))
  rhs := (.bin .and (.bin .or (.not (.var "p")) (.var "q")) (.bin .or (.not (.var "q")) (.var "p")))
  profiles := profiles
  priority := 270
  description := "Exclusive NOR holds when both operands have the same truth value."
  provenance := migrated "logic:4-connectives/4.2-compound-connectives:31"

/-- Distribute disjunction over conjunction to construct CNF. -/
def cnfLeft : BRule where
  id := "logic.cnf.or_and_left"
  legacyId := some "logic:5-normal-forms/5.1-to-cnf:24"
  vars := ["p", "q", "r"]
  lhs := (.bin .or (.var "p") (.bin .and (.var "q") (.var "r")))
  rhs := (.bin .and (.bin .or (.var "p") (.var "q")) (.bin .or (.var "p") (.var "r")))
  profiles := ["to_cnf"]
  priority := 280
  description := "Distribute disjunction over conjunction to construct CNF."
  provenance := migrated "logic:5-normal-forms/5.1-to-cnf:24"

/-- Distribute disjunction over conjunction to construct CNF. -/
def cnfRight : BRule where
  id := "logic.cnf.or_and_right"
  legacyId := some "logic:5-normal-forms/5.1-to-cnf:25"
  vars := ["q", "r", "p"]
  lhs := (.bin .or (.bin .and (.var "q") (.var "r")) (.var "p"))
  rhs := (.bin .and (.bin .or (.var "q") (.var "p")) (.bin .or (.var "r") (.var "p")))
  profiles := ["to_cnf"]
  priority := 290
  description := "Distribute disjunction over conjunction to construct CNF."
  provenance := migrated "logic:5-normal-forms/5.1-to-cnf:25"

/-- Distribute conjunction over disjunction to construct DNF. -/
def dnfLeft : BRule where
  id := "logic.dnf.and_or_left"
  legacyId := some "logic:5-normal-forms/5.2-to-dnf:26"
  vars := ["p", "q", "r"]
  lhs := (.bin .and (.var "p") (.bin .or (.var "q") (.var "r")))
  rhs := (.bin .or (.bin .and (.var "p") (.var "q")) (.bin .and (.var "p") (.var "r")))
  profiles := ["to_dnf"]
  priority := 300
  description := "Distribute conjunction over disjunction to construct DNF."
  provenance := migrated "logic:5-normal-forms/5.2-to-dnf:26"

/-- Distribute conjunction over disjunction to construct DNF. -/
def dnfRight : BRule where
  id := "logic.dnf.and_or_right"
  legacyId := some "logic:5-normal-forms/5.2-to-dnf:27"
  vars := ["q", "r", "p"]
  lhs := (.bin .and (.bin .or (.var "q") (.var "r")) (.var "p"))
  rhs := (.bin .or (.bin .and (.var "q") (.var "p")) (.bin .and (.var "r") (.var "p")))
  profiles := ["to_dnf"]
  priority := 310
  description := "Distribute conjunction over disjunction to construct DNF."
  provenance := migrated "logic:5-normal-forms/5.2-to-dnf:27"

/-- The negation of a universal quantifier is an existential quantifier of the negated body. -/
def notForall : BRule where
  id := "logic.quantifier.not_forall"
  legacyId := some "logic:6-quantifiers/6.1-negation:32"
  vars := ["x", "p"]
  lhs := (.not (.all "x" (.var "p")))
  rhs := (.ex "x" (.not (.var "p")))
  profiles := ["default"]
  priority := 320
  description := "The negation of a universal quantifier is an existential quantifier of the negated body."
  provenance := migrated "logic:6-quantifiers/6.1-negation:32"

/-- The negation of an existential quantifier is a universal quantifier of the negated body. -/
def notExists : BRule where
  id := "logic.quantifier.not_exists"
  legacyId := some "logic:6-quantifiers/6.1-negation:33"
  vars := ["x", "p"]
  lhs := (.not (.ex "x" (.var "p")))
  rhs := (.all "x" (.not (.var "p")))
  profiles := ["default"]
  priority := 330
  description := "The negation of an existential quantifier is a universal quantifier of the negated body."
  provenance := migrated "logic:6-quantifiers/6.1-negation:33"

/-- A universal quantifier distributes over conjunction, so two universals over the same variables merge into one. -/
def forallAnd : BRule where
  id := "logic.quantifier.forall_and"
  legacyId := some "logic:6-quantifiers/6.2-scope:34"
  vars := ["x", "p", "q"]
  lhs := (.bin .and (.all "x" (.var "p")) (.all "x" (.var "q")))
  rhs := (.all "x" (.bin .and (.var "p") (.var "q")))
  profiles := ["default"]
  priority := 340
  description := "A universal quantifier distributes over conjunction, so two universals over the same variables merge into one."
  provenance := migrated "logic:6-quantifiers/6.2-scope:34"

/-- An existential quantifier distributes over disjunction, so two existentials over the same variables merge into one. -/
def existsOr : BRule where
  id := "logic.quantifier.exists_or"
  legacyId := some "logic:6-quantifiers/6.2-scope:35"
  vars := ["x", "p", "q"]
  lhs := (.bin .or (.ex "x" (.var "p")) (.ex "x" (.var "q")))
  rhs := (.ex "x" (.bin .or (.var "p") (.var "q")))
  profiles := ["default"]
  priority := 350
  description := "An existential quantifier distributes over disjunction, so two existentials over the same variables merge into one."
  provenance := migrated "logic:6-quantifiers/6.2-scope:35"


/-! ## Rules not migrated -/

/-- v0.1 rules outside the fragment, with the reason. -/
def notMigrated : List (String × String) :=
  [36, 37, 38, 39].map fun i =>
    (s!"logic:6-quantifiers/6.2-scope:{i}",
      "the side condition FreeQ (a variable does not occur free) has no OpenMath symbol, so the rule cannot be stated in v1 without inventing one")

/-! ## Proofs -/


theorem orFalse_holds : orFalse.Holds := by
  intro ν I ρ; simp only [orFalse, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem andTrue_holds : andTrue.Holds := by
  intro ν I ρ; simp only [andTrue, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem andFalse_holds : andFalse.Holds := by
  intro ν I ρ; simp only [andFalse, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem orSelf_holds : orSelf.Holds := by
  intro ν I ρ; simp only [orSelf, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem andSelf_holds : andSelf.Holds := by
  intro ν I ρ; simp only [andSelf, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem falseOr_holds : falseOr.Holds := by
  intro ν I ρ; simp only [falseOr, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem trueAnd_holds : trueAnd.Holds := by
  intro ν I ρ; simp only [trueAnd, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem orTrue_holds : orTrue.Holds := by
  intro ν I ρ; simp only [orTrue, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem trueOr_holds : trueOr.Holds := by
  intro ν I ρ; simp only [trueOr, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem falseAnd_holds : falseAnd.Holds := by
  intro ν I ρ; simp only [falseAnd, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem notNot_holds : notNot.Holds := by
  intro ν I ρ; simp only [notNot, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem orNotSelf_holds : orNotSelf.Holds := by
  intro ν I ρ; simp only [orNotSelf, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem andNotSelf_holds : andNotSelf.Holds := by
  intro ν I ρ; simp only [andNotSelf, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; revert p; decide

theorem notAnd_holds : notAnd.Holds := by
  intro ν I ρ; simp only [notAnd, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; revert p q; decide

theorem notOr_holds : notOr.Holds := by
  intro ν I ρ; simp only [notOr, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; revert p q; decide

theorem notTrue_holds : notTrue.Holds := by
  intro ν I ρ; simp only [notTrue, BExpr.rename, BExpr.evalM]; decide

theorem notFalse_holds : notFalse.Holds := by
  intro ν I ρ; simp only [notFalse, BExpr.rename, BExpr.evalM]; decide

theorem orAndLeft_holds : orAndLeft.Holds := by
  intro ν I ρ; simp only [orAndLeft, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; revert p q; decide

theorem orAndRight_holds : orAndRight.Holds := by
  intro ν I ρ; simp only [orAndRight, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; revert p q; decide

theorem andOrLeft_holds : andOrLeft.Holds := by
  intro ν I ρ; simp only [andOrLeft, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; revert p q; decide

theorem andOrRight_holds : andOrRight.Holds := by
  intro ν I ρ; simp only [andOrRight, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; revert p q; decide

theorem impliesElim_holds : impliesElim.Holds := by
  intro ν I ρ; simp only [impliesElim, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; revert p q; decide

theorem equivalentElim_holds : equivalentElim.Holds := by
  intro ν I ρ; simp only [equivalentElim, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; revert p q; decide

theorem nandElim_holds : nandElim.Holds := by
  intro ν I ρ; simp only [nandElim, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; revert p q; decide

theorem norElim_holds : norElim.Holds := by
  intro ν I ρ; simp only [norElim, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; revert p q; decide

theorem xorElim_holds : xorElim.Holds := by
  intro ν I ρ; simp only [xorElim, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; revert p q; decide

theorem xnorElim_holds : xnorElim.Holds := by
  intro ν I ρ; simp only [xnorElim, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; revert p q; decide

theorem cnfLeft_holds : cnfLeft.Holds := by
  intro ν I ρ; simp only [cnfLeft, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; generalize I "r" ρ = r; revert p q r; decide

theorem cnfRight_holds : cnfRight.Holds := by
  intro ν I ρ; simp only [cnfRight, BExpr.rename, BExpr.evalM]; generalize I "q" ρ = q; generalize I "r" ρ = r; generalize I "p" ρ = p; revert q r p; decide

theorem dnfLeft_holds : dnfLeft.Holds := by
  intro ν I ρ; simp only [dnfLeft, BExpr.rename, BExpr.evalM]; generalize I "p" ρ = p; generalize I "q" ρ = q; generalize I "r" ρ = r; revert p q r; decide

theorem dnfRight_holds : dnfRight.Holds := by
  intro ν I ρ; simp only [dnfRight, BExpr.rename, BExpr.evalM]; generalize I "q" ρ = q; generalize I "r" ρ = r; generalize I "p" ρ = p; revert q r p; decide

theorem notForall_holds : notForall.Holds := by
  intro ν I ρ; simp only [notForall, BExpr.rename, BExpr.evalM, forallBool, existsBool]; generalize I "p" (upd ρ (ν "x") true) = pt; generalize I "p" (upd ρ (ν "x") false) = pf; revert pt pf; decide

theorem notExists_holds : notExists.Holds := by
  intro ν I ρ; simp only [notExists, BExpr.rename, BExpr.evalM, forallBool, existsBool]; generalize I "p" (upd ρ (ν "x") true) = pt; generalize I "p" (upd ρ (ν "x") false) = pf; revert pt pf; decide

theorem forallAnd_holds : forallAnd.Holds := by
  intro ν I ρ; simp only [forallAnd, BExpr.rename, BExpr.evalM, forallBool]; generalize I "p" (upd ρ (ν "x") true) = pt; generalize I "p" (upd ρ (ν "x") false) = pf; generalize I "q" (upd ρ (ν "x") true) = qt; generalize I "q" (upd ρ (ν "x") false) = qf; revert pt pf qt qf; decide

theorem existsOr_holds : existsOr.Holds := by
  intro ν I ρ; simp only [existsOr, BExpr.rename, BExpr.evalM, existsBool]; generalize I "p" (upd ρ (ν "x") true) = pt; generalize I "p" (upd ρ (ν "x") false) = pf; generalize I "q" (upd ρ (ν "x") true) = qt; generalize I "q" (upd ρ (ν "x") false) = qf; revert pt pf qt qf; decide


/-! ## Catalogue -/

/-- A Boolean rule with its proof. -/
structure LogicEntry where
  rule : BRule
  ruleDecl : Lean.Name
  proof : Lean.Name
  findings : List String := []
  deriving Repr, Inhabited

/-- The Logic catalogue, in v0.1 load order (= priority order). -/
def catalog : List LogicEntry := [
  { rule := orFalse, ruleDecl := ``orFalse, proof := ``orFalse_holds },
  { rule := andTrue, ruleDecl := ``andTrue, proof := ``andTrue_holds },
  { rule := andFalse, ruleDecl := ``andFalse, proof := ``andFalse_holds },
  { rule := orSelf, ruleDecl := ``orSelf, proof := ``orSelf_holds },
  { rule := andSelf, ruleDecl := ``andSelf, proof := ``andSelf_holds },
  { rule := falseOr, ruleDecl := ``falseOr, proof := ``falseOr_holds },
  { rule := trueAnd, ruleDecl := ``trueAnd, proof := ``trueAnd_holds },
  { rule := orTrue, ruleDecl := ``orTrue, proof := ``orTrue_holds },
  { rule := trueOr, ruleDecl := ``trueOr, proof := ``trueOr_holds },
  { rule := falseAnd, ruleDecl := ``falseAnd, proof := ``falseAnd_holds },
  { rule := notNot, ruleDecl := ``notNot, proof := ``notNot_holds },
  { rule := orNotSelf, ruleDecl := ``orNotSelf, proof := ``orNotSelf_holds,
    findings := ["operational: v0.1 has p ∨ ¬p ⟶ true but not ¬p ∨ p ⟶ true; the profiles are sound and terminating, not complete."] },
  { rule := andNotSelf, ruleDecl := ``andNotSelf, proof := ``andNotSelf_holds,
    findings := ["operational: v0.1 has p ∧ ¬p ⟶ false but not ¬p ∧ p ⟶ false, so for example p xor p normalizes to ¬p ∧ p; the profiles are sound and terminating, not complete."] },
  { rule := notAnd, ruleDecl := ``notAnd, proof := ``notAnd_holds },
  { rule := notOr, ruleDecl := ``notOr, proof := ``notOr_holds },
  { rule := notTrue, ruleDecl := ``notTrue, proof := ``notTrue_holds },
  { rule := notFalse, ruleDecl := ``notFalse, proof := ``notFalse_holds },
  { rule := orAndLeft, ruleDecl := ``orAndLeft, proof := ``orAndLeft_holds },
  { rule := orAndRight, ruleDecl := ``orAndRight, proof := ``orAndRight_holds },
  { rule := andOrLeft, ruleDecl := ``andOrLeft, proof := ``andOrLeft_holds },
  { rule := andOrRight, ruleDecl := ``andOrRight, proof := ``andOrRight_holds },
  { rule := impliesElim, ruleDecl := ``impliesElim, proof := ``impliesElim_holds },
  { rule := equivalentElim, ruleDecl := ``equivalentElim, proof := ``equivalentElim_holds },
  { rule := nandElim, ruleDecl := ``nandElim, proof := ``nandElim_holds },
  { rule := norElim, ruleDecl := ``norElim, proof := ``norElim_holds },
  { rule := xorElim, ruleDecl := ``xorElim, proof := ``xorElim_holds },
  { rule := xnorElim, ruleDecl := ``xnorElim, proof := ``xnorElim_holds },
  { rule := cnfLeft, ruleDecl := ``cnfLeft, proof := ``cnfLeft_holds },
  { rule := cnfRight, ruleDecl := ``cnfRight, proof := ``cnfRight_holds },
  { rule := dnfLeft, ruleDecl := ``dnfLeft, proof := ``dnfLeft_holds },
  { rule := dnfRight, ruleDecl := ``dnfRight, proof := ``dnfRight_holds },
  { rule := notForall, ruleDecl := ``notForall, proof := ``notForall_holds,
    findings := ["semantics: quantifiers range over the truth values (quantified Boolean formulas), as in the v0.1 tests; v0.1 binds a sequence of variables, v1 binds one (a sequence is a chain of binders)."] },
  { rule := notExists, ruleDecl := ``notExists, proof := ``notExists_holds,
    findings := ["semantics: quantifiers range over the truth values (quantified Boolean formulas), as in the v0.1 tests; v0.1 binds a sequence of variables, v1 binds one (a sequence is a chain of binders)."] },
  { rule := forallAnd, ruleDecl := ``forallAnd, proof := ``forallAnd_holds,
    findings := ["semantics: quantifiers range over the truth values (quantified Boolean formulas), as in the v0.1 tests; v0.1 binds a sequence of variables, v1 binds one (a sequence is a chain of binders)."] },
  { rule := existsOr, ruleDecl := ``existsOr, proof := ``existsOr_holds,
    findings := ["semantics: quantifiers range over the truth values (quantified Boolean formulas), as in the v0.1 tests; v0.1 binds a sequence of variables, v1 binds one (a sequence is a chain of binders)."] }
]

/-- The rules of a profile, in priority order. -/
def profileRules (p : String) : List BRule :=
  (catalog.map (·.rule)).filter (p ∈ ·.profiles)

/-- The rules shared by every profile. -/
def commonRules : List BRule := [orFalse, andTrue, andFalse, orSelf, andSelf, falseOr, trueAnd, orTrue, trueOr, falseAnd, notNot, orNotSelf, andNotSelf, notAnd, notOr, notTrue, notFalse, orAndLeft, orAndRight, andOrLeft, andOrRight, impliesElim, equivalentElim, nandElim, norElim, xorElim, xnorElim]

/-- The quantifier rules (`default` only, as in v0.1). -/
def quantifierRules : List BRule := [notForall, notExists, forallAnd, existsOr]

theorem profileRules_default : profileRules "default" = commonRules ++ quantifierRules := rfl
theorem profileRules_cnf : profileRules "to_cnf" = commonRules ++ [cnfLeft, cnfRight] := rfl
theorem profileRules_dnf : profileRules "to_dnf" = commonRules ++ [dnfLeft, dnfRight] := rfl

/-! ## Engine soundness -/

theorem catalog_holds : ∀ e ∈ catalog, e.rule.Holds := by
  intro e he
  simp only [catalog, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [orFalse_holds, andTrue_holds, andFalse_holds, orSelf_holds,
    andSelf_holds, falseOr_holds, trueAnd_holds, orTrue_holds,
    trueOr_holds, falseAnd_holds, notNot_holds, orNotSelf_holds,
    andNotSelf_holds, notAnd_holds, notOr_holds, notTrue_holds,
    notFalse_holds, orAndLeft_holds, orAndRight_holds, andOrLeft_holds,
    andOrRight_holds, impliesElim_holds, equivalentElim_holds, nandElim_holds,
    norElim_holds, xorElim_holds, xnorElim_holds, cnfLeft_holds,
    cnfRight_holds, dnfLeft_holds, dnfRight_holds, notForall_holds,
    notExists_holds, forallAnd_holds, existsOr_holds]

theorem profileRules_hold (p : String) : RulesHold (profileRules p) := by
  intro r hr
  simp only [profileRules, List.mem_filter, List.mem_map] at hr
  obtain ⟨⟨e, he, rfl⟩, _⟩ := hr
  exact catalog_holds e he

/-- Normalizing with any Logic profile preserves the truth value. -/
theorem profile_normalize_sound (p : String) (fuel : Nat) (env : String → Bool) (e : BExpr) :
    (normalize (profileRules p) fuel e).result.eval env = e.eval env :=
  normalize_sound _ (profileRules_hold p) env fuel e

/-! ## Termination -/

/-- Every common rule decreases under any `BasicWeight`. -/
theorem common_decreasing (W : BasicWeight) : ∀ r ∈ commonRules, W.Decreases r := by
  simp only [commonRules, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro env <;>
    simp only [orFalse, andTrue, andFalse, orSelf, andSelf, falseOr, trueAnd, orTrue, trueOr, falseAnd, notNot, orNotSelf, andNotSelf, notAnd, notOr, notTrue, notFalse, orAndLeft, orAndRight, andOrLeft, andOrRight, impliesElim, equivalentElim, nandElim, norElim, xorElim, xnorElim, BasicWeight.weigh, BasicWeight.bin]
  all_goals first
    | omega
    | exact W.disj_gtl _ _ | exact W.disj_gtr _ _ | exact W.conj_gtl _ _
    | exact W.conj_gtr _ _ | exact W.deMorgan_conj _ _ | exact W.deMorgan_disj _ _
    | exact W.nt_gt _
    | (have h1 := W.nt_gt (env "p"); have h2 := W.nt_gt (W.nt (env "p")); omega)
    | (have h1 := W.nt_gt (env "p"); have h2 := W.disj_gtr (env "p") (W.nt (env "p")); omega)
    | (have h1 := W.nt_gt (env "p"); have h2 := W.conj_gtr (env "p") (W.nt (env "p")); omega)

private theorem two_pow_ge (n : Nat) : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)

private theorem lt_two_pow_succ (a : Nat) : a < 2 ^ (a + 1) :=
  Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))

private theorem sum_lt (a b : Nat) : 2 ^ (a + 1) + 2 ^ (b + 1) + 5 < 2 ^ (a + b + 5 + 1) := by
  have := two_pow_ge a; have := two_pow_ge b
  have h : 2 ^ (a + b + 5 + 1) = 2 ^ a * 2 ^ b * 64 := by ring
  rw [h, pow_succ, pow_succ]; nlinarith

private theorem prod_lt (a b : Nat) :
    (2 ^ (a + 1) + 2) * (2 ^ (b + 1) + 2) < 2 ^ (a + b + 5 + 1) := by
  have := two_pow_ge a; have := two_pow_ge b
  have h : 2 ^ (a + b + 5 + 1) = 2 ^ a * 2 ^ b * 64 := by ring
  rw [h, pow_succ, pow_succ]; nlinarith

private theorem sum_lt_prod (a b : Nat) :
    2 ^ (a + 1) + 2 ^ (b + 1) + 5 < 2 ^ ((a + 2) * (b + 2) + 1) := by
  have := two_pow_ge a; have := two_pow_ge b
  have h2 : 2 ^ (a + b + 5) ≤ 2 ^ ((a + 2) * (b + 2) + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h : 2 ^ (a + b + 5) = 2 ^ a * 2 ^ b * 32 := by ring
  have : 2 ^ (a + 1) + 2 ^ (b + 1) + 5 < 2 ^ a * 2 ^ b * 32 := by
    rw [pow_succ, pow_succ]; nlinarith
  omega

/-- Weight of the `default` profile: negation weighs exponentially, so pushing
it inward pays for the duplicated connective. -/
def defaultWeight : BasicWeight where
  nt a := 2 ^ (a + 1)
  conj a b := a + b + 5
  disj a b := a + b + 5
  nt_mono _ _ h := Nat.pow_lt_pow_right (by norm_num) (by omega)
  conj_monol _ _ _ h := by omega
  conj_monor _ _ _ h := by omega
  disj_monol _ _ _ h := by omega
  disj_monor _ _ _ h := by omega
  nt_gt a := lt_two_pow_succ a
  conj_gtl _ _ := by omega
  conj_gtr _ _ := by omega
  disj_gtl _ _ := by omega
  disj_gtr _ _ := by omega
  deMorgan_conj a b := sum_lt a b
  deMorgan_disj a b := sum_lt a b

/-- Weight of the `to_cnf` profile: disjunction weighs multiplicatively, so
distributing it over a conjunction decreases the weight. -/
def cnfWeight : BasicWeight where
  nt a := 2 ^ (a + 1)
  conj a b := a + b + 5
  disj a b := (a + 2) * (b + 2)
  nt_mono _ _ h := Nat.pow_lt_pow_right (by norm_num) (by omega)
  conj_monol _ _ _ h := by omega
  conj_monor _ _ _ h := by omega
  disj_monol _ _ _ h := by nlinarith
  disj_monor _ _ _ h := by nlinarith
  nt_gt a := lt_two_pow_succ a
  conj_gtl _ _ := by omega
  conj_gtr _ _ := by omega
  disj_gtl _ _ := by nlinarith
  disj_gtr _ _ := by nlinarith
  deMorgan_conj a b := prod_lt a b
  deMorgan_disj a b := sum_lt_prod a b

/-- Weight of the `to_dnf` profile: conjunction weighs multiplicatively. -/
def dnfWeight : BasicWeight where
  nt a := 2 ^ (a + 1)
  conj a b := (a + 2) * (b + 2)
  disj a b := a + b + 5
  nt_mono _ _ h := Nat.pow_lt_pow_right (by norm_num) (by omega)
  conj_monol _ _ _ h := by nlinarith
  conj_monor _ _ _ h := by nlinarith
  disj_monol _ _ _ h := by omega
  disj_monor _ _ _ h := by omega
  nt_gt a := lt_two_pow_succ a
  conj_gtl _ _ := by nlinarith
  conj_gtr _ _ := by nlinarith
  disj_gtl _ _ := by omega
  disj_gtr _ _ := by omega
  deMorgan_conj a b := sum_lt_prod a b
  deMorgan_disj a b := prod_lt a b

/-- The weight proving termination of a profile. -/
def weight : String → BasicWeight
  | "to_cnf" => cnfWeight
  | "to_dnf" => dnfWeight
  | _ => defaultWeight

theorem default_terminates : Terminates (profileRules "default") defaultWeight := by
  rw [profileRules_default]
  refine defaultWeight.terminates _ fun r hr => ?_
  simp only [quantifierRules, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with hr | rfl | rfl | rfl | rfl
  · exact common_decreasing _ r hr
  all_goals
    intro env
    simp only [notForall, notExists, forallAnd, existsOr, BasicWeight.weigh, BasicWeight.bin,
      defaultWeight]
  · have := two_pow_ge (env "p"); rw [pow_succ, pow_succ]; omega
  · have := two_pow_ge (env "p"); rw [pow_succ, pow_succ]; omega
  · omega
  · omega

theorem cnf_terminates : Terminates (profileRules "to_cnf") cnfWeight := by
  rw [profileRules_cnf]
  refine cnfWeight.terminates _ fun r hr => ?_
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with hr | rfl | rfl
  · exact common_decreasing _ r hr
  all_goals
    intro env
    simp only [cnfLeft, cnfRight, BasicWeight.weigh, BasicWeight.bin, cnfWeight]
    nlinarith

theorem dnf_terminates : Terminates (profileRules "to_dnf") dnfWeight := by
  rw [profileRules_dnf]
  refine dnfWeight.terminates _ fun r hr => ?_
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with hr | rfl | rfl
  · exact common_decreasing _ r hr
  all_goals
    intro env
    simp only [dnfLeft, dnfRight, BasicWeight.weigh, BasicWeight.bin, dnfWeight]
    nlinarith

end OSR.Logic
