import OSR

/-!
# Logic tests
-/

namespace OSRTest.Logic

open OSR OSR.Logic

private def p : BExpr := .var "p"
private def q : BExpr := .var "q"

-- Every v0.1 rule is migrated or reported.
#guard Logic.catalog.length + Logic.notMigrated.length == 39

-- Identifiers are unique and every rule belongs to a known profile.
#guard (Logic.catalog.map (·.rule.id)).eraseDups.length == Logic.catalog.length
#guard Logic.catalog.all fun e => e.rule.profiles.all (· ∈ Logic.profiles)

-- Replacements only use pattern variables.
#guard Logic.catalog.all fun e => e.rule.rhs.vars.all (· ∈ e.rule.lhs.vars)

-- The two distributions never share a profile.
#guard Logic.profiles.all fun pr =>
  !((Logic.profileRules pr).contains Logic.cnfLeft && (Logic.profileRules pr).contains Logic.dnfLeft)

-- Decoding the export recovers every pattern and replacement.
#guard Logic.catalog.all fun e =>
  Logic.decode e.rule.lhs.toOM == some e.rule.lhs && Logic.decode e.rule.rhs.toOM == some e.rule.rhs

-- Every profile reaches a normal form on every pattern within the proved bound.
#guard Logic.profiles.all fun pr =>
  Logic.catalog.all fun e =>
    (normalize (Logic.profileRules pr) ((Logic.weight pr).weigh (fun _ => 0) e.rule.lhs)
      e.rule.lhs).normal

-- Examples.
#guard (normalize (Logic.profileRules "default") 16 (.not (.bin .implies p q))).result ==
  .bin .and p (.not q)
-- Distribution, then `p ∨ false`, then absorption of `(p ∨ q) ∧ p`.
#guard (normalize (Logic.profileRules "to_cnf") 16 (.bin .or p (.bin .and q .ff))).result == p

-- v0.1 has `p ∧ ¬p ⟶ false` but not `¬p ∧ p ⟶ false`, so `p xor p` stops at
-- `¬p ∧ p`: the profiles are sound and terminating, not complete.
#guard (normalize (Logic.profileRules "default") 16 (.bin .xor p p)).result ==
  .bin .and (.not p) p

-- Non-linear patterns need equal subterms.
#guard (normalize (Logic.profileRules "default") 16 (.bin .or p (.not q))).trace == []

-- Quantifiers range over the truth values.
private def y : BExpr := .var "y"
#guard (BExpr.all "y" (.bin .or y (.not y))).eval (fun _ => false) == true
#guard (BExpr.ex "y" (.bin .and y q)).eval (fun _ => false) == false

-- ¬∀y. (y ∧ q) ⟶ ∃y. ¬(y ∧ q) ⟶ … the binder name comes from the input.
#guard (rewriteStep (Logic.profileRules "default") (.not (.all "y" (.bin .and y q)))).map (·.2) ==
  some (.ex "y" (.not (.bin .and y q)))

-- Merging two universals needs the same bound variable (non-linear binder).
#guard (rewriteStep (Logic.profileRules "default")
    (.bin .and (.all "y" (.bin .or y p)) (.all "y" (.bin .or y q)))).map (·.2) ==
  some (.all "y" (.bin .and (.bin .or y p) (.bin .or y q)))
#guard (rewriteStep (Logic.profileRules "default")
    (.bin .and (.all "y" (.bin .or y p)) (.all "z" (.bin .or (.var "z") q)))).map (·.1) !=
  some "logic.quantifier.forall_and"

-- Soundness under binders, checked on every assignment of p and q: the
-- instance body mentions the bound variable, which a first-order
-- substitution would capture.
#guard [false, true].all fun vp => [false, true].all fun vq =>
  let ρ : String → Bool := fun n => if n = "p" then vp else if n = "q" then vq else false
  let e : BExpr := .not (.all "p" (.bin .or (.var "p") q))
  ((normalize (Logic.profileRules "default") 16 e).result.eval ρ == e.eval ρ)

-- FreeQ as a matching constraint: ∀y. (p ∨ q) is vacuous, ∀y. (y ∨ q) is not.
#guard (rewriteStep (Logic.profileRules "default") (.all "y" (.bin .or p q))).map (·.2) ==
  some (.bin .or p q)
#guard (rewriteStep (Logic.profileRules "default") (.all "y" (.bin .or y q))).map (·.1) ==
  some "logic.quantifier.forall_or_right"
#guard (rewriteStep (Logic.profileRules "default") (.all "y" (.bin .or y q))).map (·.2) ==
  some (.bin .or (.all "y" y) q)
#guard (rewriteStep (Logic.profileRules "default") (.ex "y" (.bin .and q y))).isNone

end OSRTest.Logic
