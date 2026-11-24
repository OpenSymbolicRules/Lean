import OSRTest.PositivePower

/-! Test-only recursive real-power interpreter. It is not an OSR mapping. -/

namespace OSRTest.RecursiveRealPower

open OSR OSRTest.PositivePower

noncomputable def evalCandidate (env : String → ℝ) : Expr → ℝ
  | .var n => env n
  | .int z => (z : ℝ)
  | .const .pi => Interp.real.pi
  | .app1 .neg a => -evalCandidate env a
  | .app1 .sin a => Interp.real.sin (evalCandidate env a)
  | .app1 .cos a => Interp.real.cos (evalCandidate env a)
  | .app1 .tan a => Interp.real.tan (evalCandidate env a)
  | .app1 .arctan a => Interp.real.arctan (evalCandidate env a)
  | .app1 .exp a => Interp.real.exp (evalCandidate env a)
  | .app1 .ln a => Interp.real.ln (evalCandidate env a)
  | .app1 o a => Interp.real.fn o (evalCandidate env a)
  | .app2 .add a b => evalCandidate env a + evalCandidate env b
  | .app2 .sub a b => evalCandidate env a - evalCandidate env b
  | .app2 .mul a b => evalCandidate env a * evalCandidate env b
  | .app2 .div a b => evalCandidate env a / evalCandidate env b
  | .app2 .root a b => Interp.real.root (evalCandidate env a) (evalCandidate env b)
  | .pow a e => Real.rpow (evalCandidate env a) (evalCandidate env e)

noncomputable def definedCandidate (env : String → ℝ) : Expr → Prop
  | .var _ => True
  | .int _ => True
  | .const _ => True
  | .app1 .tan a => definedCandidate env a ∧ Interp.real.tanDefined (evalCandidate env a)
  | .app1 .arctan a => definedCandidate env a ∧ Interp.real.arctanDefined (evalCandidate env a)
  | .app1 .ln a => definedCandidate env a ∧ Interp.real.lnDefined (evalCandidate env a)
  | .app1 .exp a => definedCandidate env a
  | .app1 .neg a => definedCandidate env a
  | .app1 .sin a => definedCandidate env a
  | .app1 .cos a => definedCandidate env a
  | .app1 o a => definedCandidate env a ∧ Interp.real.fnDefined o (evalCandidate env a)
  | .app2 .div a b => definedCandidate env a ∧ definedCandidate env b ∧ evalCandidate env b ≠ 0
  | .app2 .root a b => definedCandidate env a ∧ definedCandidate env b ∧
      Interp.real.rootDefined (evalCandidate env a) (evalCandidate env b)
  | .app2 .add a b => definedCandidate env a ∧ definedCandidate env b
  | .app2 .sub a b => definedCandidate env a ∧ definedCandidate env b
  | .app2 .mul a b => definedCandidate env a ∧ definedCandidate env b
  | .pow a e => definedCandidate env a ∧ definedCandidate env e ∧
      candidatePowerDefined (evalCandidate env a) (evalCandidate env e)

/-- Existing defined expressions keep their definedness and value. -/
theorem old_recursive_compatibility (env : String → ℝ) (e : Expr) :
    Defined Interp.real env e →
      definedCandidate env e ∧ evalCandidate env e = eval Interp.real env e := by
  induction e with
  | var n => simp [Defined, definedCandidate, evalCandidate, eval]
  | int n => simp [Defined, definedCandidate, evalCandidate, eval]
  | const c => cases c; simp [Defined, definedCandidate, evalCandidate, eval]
  | app1 op a ih =>
      cases op <;> simp only [Defined, definedCandidate, evalCandidate, eval] at * <;> aesop
  | app2 op a b iha ihb =>
      cases op <;> simp only [Defined, definedCandidate, evalCandidate, eval] at * <;> aesop
  | pow a e iha ihe =>
      intro h
      obtain ⟨ha, he, n, hn, hne⟩ := h
      obtain ⟨hca, hva⟩ := iha ha
      obtain ⟨hce, hve⟩ := ihe he
      have hv := (intValue?_eq _ _).1 hn
      constructor
      · exact ⟨hca, hce, Or.inr ⟨n, hve.trans hv, fun hnneg => by
          rw [hva]; exact hne hnneg⟩⟩
      · change Real.rpow (evalCandidate env a) (evalCandidate env e) = _
        rw [hva, hve, hv]
        calc
          _ = eval Interp.real env a ^ n := Real.rpow_intCast _ _
          _ = _ := (eval_pow_of hn).symm

/-- A nested fractional power, with no component expansion. -/
def nestedPower : Expr :=
  .pow (.pow (.int 2) (.app2 .div (.int 1) (.int 2))) (.int 2)

theorem nested_fractional_power_defined : definedCandidate (fun _ => 0) nestedPower := by
  simp only [nestedPower, definedCandidate, evalCandidate]
  refine ⟨⟨trivial, ⟨trivial, trivial, by norm_num⟩, Or.inl (by norm_num)⟩,
    trivial, Or.inl ?_⟩
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem nested_fractional_power_positive : 0 < evalCandidate (fun _ => 0) nestedPower := by
  simp only [nestedPower, evalCandidate]
  exact Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _

end OSRTest.RecursiveRealPower
