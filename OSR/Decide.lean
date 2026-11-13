import OSR.Rewrite

/-!
# Deciding closed conditions

A condition of a rule mentions metavariables.  Once a match binds them to
closed expressions built from integer literals with `+`, `-`, `×`, `÷`,
unary minus and integer powers, the condition can be decided exactly: such an
expression denotes a rational number, computed by `Expr.ratEval?`, and is
defined wherever that computation succeeds (`ratEval?_sound`).

`Cond.decide?` returns `some b` only for such conditions; `none` means
"cannot decide", and an engine must then leave the rule alone.  A decided
`true` implies the condition in every interpretation of characteristic zero
whose order on rational values is the rational order (`decide?_sound`); the
real and complex interpretations of the registry are such interpretations
(`Interp.real_lt_rat`, `Interp.complex_lt_rat`).
-/

namespace OSR

/-- The rational value of a closed arithmetic expression, if it is defined. -/
def Expr.ratEval? : Expr → Option ℚ
  | .int z => some z
  | .app1 .neg a => (fun q => -q) <$> a.ratEval?
  | .app2 .add a b => do return (← a.ratEval?) + (← b.ratEval?)
  | .app2 .sub a b => do return (← a.ratEval?) - (← b.ratEval?)
  | .app2 .mul a b => do return (← a.ratEval?) * (← b.ratEval?)
  | .app2 .div a b => do
    let q ← a.ratEval?
    let r ← b.ratEval?
    if r = 0 then none else some (q / r)
  | .pow a e => do
    let q ← a.ratEval?
    let k ← e.ratEval?
    if k.den = 1 then
      if k.num < 0 ∧ q = 0 then none else some (q ^ k.num)
    else none
  | _ => none

section Sound

variable {α : Type} [Field α] [CharZero α]

omit [CharZero α] in
/-- A rational of denominator `1` is cast as its numerator. -/
theorem rat_cast_of_den_one {q : ℚ} (h : q.den = 1) : (q : α) = ((q.num : ℤ) : α) := by
  rw [← Rat.cast_intCast, (Rat.den_eq_one_iff q).mp h]

/-- **Soundness of the evaluation.**  A closed expression with a rational value
is defined in every interpretation and denotes that value. -/
theorem Expr.ratEval?_sound (I : Interp α) (env : String → α) :
    ∀ (e : Expr) (q : ℚ), e.ratEval? = some q → Defined I env e ∧ eval I env e = (q : α)
  | .int z, q, h => by
    simp only [Expr.ratEval?, Option.some.injEq] at h
    subst h; simp [Defined, eval]
  | .app1 .neg a, q, h => by
    simp only [Expr.ratEval?, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    obtain ⟨hd, hv⟩ := Expr.ratEval?_sound I env a r hr
    exact ⟨hd, by simp [eval, hv]⟩
  | .app2 .add a b, q, h => by
    simp only [Expr.ratEval?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, s, hs, rfl⟩ := h
    obtain ⟨hda, hva⟩ := Expr.ratEval?_sound I env a r hr
    obtain ⟨hdb, hvb⟩ := Expr.ratEval?_sound I env b s hs
    exact ⟨⟨hda, hdb⟩, by simp [eval, hva, hvb]⟩
  | .app2 .sub a b, q, h => by
    simp only [Expr.ratEval?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, s, hs, rfl⟩ := h
    obtain ⟨hda, hva⟩ := Expr.ratEval?_sound I env a r hr
    obtain ⟨hdb, hvb⟩ := Expr.ratEval?_sound I env b s hs
    exact ⟨⟨hda, hdb⟩, by simp [eval, hva, hvb]⟩
  | .app2 .mul a b, q, h => by
    simp only [Expr.ratEval?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, s, hs, rfl⟩ := h
    obtain ⟨hda, hva⟩ := Expr.ratEval?_sound I env a r hr
    obtain ⟨hdb, hvb⟩ := Expr.ratEval?_sound I env b s hs
    exact ⟨⟨hda, hdb⟩, by simp [eval, hva, hvb]⟩
  | .app2 .div a b, q, h => by
    simp only [Expr.ratEval?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, s, hs, h⟩ := h
    split at h
    · cases h
    · rename_i hs0
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hda, hva⟩ := Expr.ratEval?_sound I env a r hr
      obtain ⟨hdb, hvb⟩ := Expr.ratEval?_sound I env b s hs
      refine ⟨⟨hda, hdb, by rw [hvb]; exact_mod_cast hs0⟩, by simp [eval, hva, hvb]⟩
  | .pow a e, q, h => by
    simp only [Expr.ratEval?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, k, hk, h⟩ := h
    split at h
    · rename_i hden
      split at h
      · cases h
      · rename_i hz
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hda, hva⟩ := Expr.ratEval?_sound I env a r hr
        obtain ⟨hde, hve⟩ := Expr.ratEval?_sound I env e k hk
        have hkint : (k : α) = ((k.num : ℤ) : α) := rat_cast_of_den_one hden
        have hint : I.toInt? (eval I env e) = some k.num := by
          rw [hve, hkint]; exact I.toInt?_cast _
        refine ⟨⟨hda, hde, k.num, hint, fun hneg => ?_⟩, ?_⟩
        · rw [hva]
          have : r ≠ 0 := fun h0 => hz ⟨hneg, h0⟩
          exact_mod_cast this
        · rw [eval_pow_of hint, hva]; push_cast; rfl
    · cases h

end Sound

/-- The decision of a closed condition: `some b` if both sides have rational
values, `none` otherwise. -/
def Cond.decide? : Cond → Option Bool
  | .ne a b => do return decide ((← a.ratEval?) ≠ (← b.ratEval?))
  | .gt a b => do return decide ((← b.ratEval?) < (← a.ratEval?))
  | .int a => do return decide ((← a.ratEval?).den = 1)

/-- **Soundness of the decision.**  A condition decided `true` holds, in every
interpretation of characteristic zero whose order on rational values is the
rational order. -/
theorem Cond.decide?_sound {α : Type} [Field α] [CharZero α] (I : Interp α)
    (hlt : ∀ q r : ℚ, I.lt (q : α) (r : α) ↔ q < r) (env : String → α) :
    ∀ c : Cond, c.decide? = some true → c.Holds I env
  | .ne a b, h => by
    simp only [Cond.decide?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, decide_eq_true_eq] at h
    obtain ⟨q, hq, r, hr, hne⟩ := h
    obtain ⟨hda, hva⟩ := Expr.ratEval?_sound I env a q hq
    obtain ⟨hdb, hvb⟩ := Expr.ratEval?_sound I env b r hr
    refine ⟨hda, hdb, ?_⟩
    rw [hva, hvb]; exact_mod_cast hne
  | .gt a b, h => by
    simp only [Cond.decide?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, decide_eq_true_eq] at h
    obtain ⟨r, hr, q, hq, hlt'⟩ := h
    obtain ⟨hdb, hvb⟩ := Expr.ratEval?_sound I env b r hr
    obtain ⟨hda, hva⟩ := Expr.ratEval?_sound I env a q hq
    refine ⟨hda, hdb, ?_⟩
    rw [hva, hvb]; exact (hlt r q).2 hlt'
  | .int a, h => by
    simp only [Cond.decide?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, decide_eq_true_eq] at h
    obtain ⟨q, hq, hden⟩ := h
    obtain ⟨hda, hva⟩ := Expr.ratEval?_sound I env a q hq
    refine ⟨hda, q.num, ?_⟩
    rw [hva, rat_cast_of_den_one hden]
    exact I.toInt?_cast _

theorem Interp.real_lt_rat : ∀ q r : ℚ, Interp.real.lt (q : ℝ) (r : ℝ) ↔ q < r := by
  intro q r; simp only [Interp.real]; exact_mod_cast Iff.rfl

theorem Interp.complex_lt_rat : ∀ q r : ℚ, Interp.complex.lt (q : ℂ) (r : ℂ) ↔ q < r := by
  intro q r
  simp only [Interp.complex, Complex.ratCast_im, Complex.ratCast_re, true_and]
  exact_mod_cast Iff.rfl

/-- Substitution in a condition. -/
def Cond.subst (σ : Subst) : Cond → Cond
  | .ne a b => .ne (a.subst σ) (b.subst σ)
  | .gt a b => .gt (a.subst σ) (b.subst σ)
  | .int a => .int (a.subst σ)

/-- A substituted condition that holds gives the condition under the
assignment induced by the substitution. -/
theorem Cond.holds_subst {α : Type} [Field α] (I : Interp α) (env : String → α) (σ : Subst) :
    ∀ c : Cond, (c.subst σ).Holds I env → c.Holds I (σ.env I env)
  | .ne a b, ⟨ha, hb, hv⟩ => by
    refine ⟨((defined_subst I env σ a).1 ha).1, ((defined_subst I env σ b).1 hb).1, ?_⟩
    rwa [eval_subst, eval_subst] at hv
  | .gt a b, ⟨ha, hb, hv⟩ => by
    refine ⟨((defined_subst I env σ a).1 ha).1, ((defined_subst I env σ b).1 hb).1, ?_⟩
    rwa [eval_subst, eval_subst] at hv
  | .int a, ⟨ha, n, hn⟩ => by
    refine ⟨((defined_subst I env σ a).1 ha).1, n, ?_⟩
    rwa [eval_subst] at hn

end OSR
