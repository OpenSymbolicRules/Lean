import OSR.Rewrite

/-!
# Termination of the reference rewriter

A *weight* interprets every operator of the fragment as a strictly monotone
function on `ℕ`.  If every rule of a list is *decreasing* (its right-hand
side weighs less than its left-hand side for every assignment of its
variables), then every step of `rewriteStep` strictly decreases the weight of
the whole expression, because substitution commutes with weighing and the
weight of a context is strictly monotone in the rewritten subterm.  Hence
`normalize` reaches a normal form within `weight e` steps (`normalize_normal`).

This is the classical method of monotone interpretations; the weight is a
reduction order for the rules, independent of their meaning.
-/

namespace OSR

/-- A monotone interpretation of the fragment into `ℕ`. -/
structure Weight where
  int : Int → Nat
  const : Const → Nat
  op1 : Op1 → Nat → Nat
  op2 : Op2 → Nat → Nat → Nat
  /-- Weight of `a ^ e` from the weights of `a` and `e`. -/
  pow : Nat → Nat → Nat
  mono1 : ∀ o a a', a < a' → op1 o a < op1 o a'
  mono2l : ∀ o a a' b, a < a' → op2 o a b < op2 o a' b
  mono2r : ∀ o a b b', b < b' → op2 o a b < op2 o a b'
  monoPowl : ∀ a a' b, a < a' → pow a b < pow a' b
  monoPowr : ∀ a b b', b < b' → pow a b < pow a b'

namespace Weight

/-- The weight of an expression under an assignment of its variables. -/
def eval (W : Weight) (env : String → Nat) : Expr → Nat
  | .var n => env n
  | .int z => W.int z
  | .const c => W.const c
  | .app1 o a => W.op1 o (W.eval env a)
  | .app2 o a b => W.op2 o (W.eval env a) (W.eval env b)
  | .pow a b => W.pow (W.eval env a) (W.eval env b)

/-- A rule is decreasing when its right-hand side weighs strictly less than its
left-hand side, whatever the weights of its variables. -/
def Decreases (W : Weight) (r : Rule) : Prop :=
  ∀ env, W.eval env r.rhs < W.eval env r.lhs

theorem eval_subst (W : Weight) (env : String → Nat) (σ : Subst) :
    ∀ e : Expr, W.eval env (e.subst σ) = W.eval (fun n => W.eval env (σ.apply n)) e
  | .var n => by simp [Expr.subst, eval]
  | .int z => by simp [Expr.subst, eval]
  | .const c => by simp [Expr.subst, eval]
  | .app1 o a => by simp [Expr.subst, eval, eval_subst W env σ a]
  | .app2 o a b => by simp [Expr.subst, eval, eval_subst W env σ a, eval_subst W env σ b]
  | .pow a b => by simp [Expr.subst, eval, eval_subst W env σ a, eval_subst W env σ b]

variable (W : Weight) (env : String → Nat)

/-- The engine only applies unconditional rules, so only they must decrease. -/
def RulesDecrease (W : Weight) (rules : List Rule) : Prop :=
  ∀ r ∈ rules, r.conditions.isEmpty → W.Decreases r

theorem rootRewrite_lt : ∀ (rules : List Rule) (e : Expr) (s : String × Expr),
    W.RulesDecrease rules → rootRewrite rules e = some s →
      W.eval env s.2 < W.eval env e
  | [], _, _, _, h => by simp [rootRewrite] at h
  | r :: rs, e, s, hr, h => by
    have hrs : W.RulesDecrease rs := fun r' h' => hr r' (List.mem_cons_of_mem _ h')
    unfold rootRewrite at h
    split at h
    · rename_i hempty
      split at h
      · rename_i σ hm
        simp only [Option.some.injEq] at h
        subst h
        have hd := hr r List.mem_cons_self hempty (fun n => W.eval env (σ.apply n))
        rw [← matchExpr_subst hm, eval_subst, eval_subst]
        exact hd
      · exact rootRewrite_lt rs e s hrs h
    · exact rootRewrite_lt rs e s hrs h

theorem rewriteStep_lt (rules : List Rule) (hr : W.RulesDecrease rules) :
    ∀ (e : Expr) (s : String × Expr), rewriteStep rules e = some s →
      W.eval env s.2 < W.eval env e
  | .var n, s, h => W.rootRewrite_lt env rules _ s hr (by simpa [rewriteStep] using h)
  | .int z, s, h => W.rootRewrite_lt env rules _ s hr (by simpa [rewriteStep] using h)
  | .const c, s, h => W.rootRewrite_lt env rules _ s hr (by simpa [rewriteStep] using h)
  | .app1 o a, s, h => by
    simp only [rewriteStep] at h
    split at h
    · rename_i s' hroot
      simp only [Option.some.injEq] at h
      subst h
      exact W.rootRewrite_lt env rules _ s' hr hroot
    · split at h
      · rename_i s' hs
        simp only [Option.some.injEq] at h
        subst h
        exact W.mono1 o _ _ (rewriteStep_lt rules hr a s' hs)
      · cases h
  | .app2 o a b, s, h => by
    simp only [rewriteStep] at h
    split at h
    · rename_i s' hroot
      simp only [Option.some.injEq] at h
      subst h
      exact W.rootRewrite_lt env rules _ s' hr hroot
    · split at h
      · rename_i s' hs
        simp only [Option.some.injEq] at h
        subst h
        exact W.mono2l o _ _ _ (rewriteStep_lt rules hr a s' hs)
      · split at h
        · rename_i s' hs
          simp only [Option.some.injEq] at h
          subst h
          exact W.mono2r o _ _ _ (rewriteStep_lt rules hr b s' hs)
        · cases h
  | .pow a b, s, h => by
    simp only [rewriteStep] at h
    split at h
    · rename_i s' hroot
      simp only [Option.some.injEq] at h
      subst h
      exact W.rootRewrite_lt env rules _ s' hr hroot
    · split at h
      · rename_i s' hs
        simp only [Option.some.injEq] at h
        subst h
        exact W.monoPowl _ _ _ (rewriteStep_lt rules hr a s' hs)
      · split at h
        · rename_i s' hs
          simp only [Option.some.injEq] at h
          subst h
          exact W.monoPowr _ _ _ (rewriteStep_lt rules hr b s' hs)
        · cases h

/-- **Termination.**  With decreasing rules, `normalize` reaches a normal form
as soon as the fuel is at least the weight of the input. -/
theorem normalize_normal (rules : List Rule) (hr : W.RulesDecrease rules) :
    ∀ (fuel : Nat) (e : Expr), W.eval env e ≤ fuel → (normalize rules fuel e).normal = true
  | 0, e, he => by
    simp only [normalize, Option.isNone_iff_eq_none]
    cases hs : rewriteStep rules e with
    | none => rfl
    | some s => have := W.rewriteStep_lt env rules hr e s hs; omega
  | fuel + 1, e, he => by
    simp only [normalize]
    split
    · rfl
    · rename_i id e' hs
      have := W.rewriteStep_lt env rules hr e (id, e') hs
      exact normalize_normal rules hr fuel e' (by simp at this; omega)

end Weight

/-- Normalizing any expression with `rules` reaches a normal form within the
`W`-weight of the expression (variables weigh `0`). -/
def Terminates (rules : List Rule) (W : Weight) : Prop :=
  ∀ e, (normalize rules (W.eval (fun _ => 0) e) e).normal = true

theorem Weight.terminates (W : Weight) (rules : List Rule) (hr : W.RulesDecrease rules) :
    Terminates rules W :=
  fun e => W.normalize_normal _ rules hr _ e le_rfl

end OSR
