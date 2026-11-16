import OSR.IntegrationRec27

/-!
# Integration (RUBI): the last branch-cut refutation

RUBI 4.16.1 3.2.3 #5 rewrites `∫ log(e (f (a+b x)^p (c+d x)^q)^r)²/(g+h x)` as
`I₁ + B(x) (2 I₂ + I₃)`, where `B = log(e (…)^r) - log((a+b x)^(p r)) -
log((c+d x)^(q r))`.  At `e = -1`, `b = c = f = h = p = r = 1` and the other
metavariables `0`, the integrand `log(-x)²/x` is defined near `x = -1`, and
`B(x) = log(-x) - log x` jumps across the cut there.  The antiderivatives of
the residual integrands are free up to a constant: choosing them linear, with
`2 Φ₂ + Φ₃ = 2` at `-1`, a continuous result would make `B` continuous at `-1`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec28

open OSR OSR.Calculus OSR.IntegrationRec26 OSR.IntegrationRec14 Filter Topology

section Witness
variable {α : Type} [Field α] [CharZero α]
private theorem iv0 : intValue? (0 : α) = some 0 := by simpa using intValue?_intCast (α := α) 0
private theorem iv1 : intValue? (1 : α) = some 1 := by simpa using intValue?_intCast (α := α) 1
private theorem iv2 : intValue? (2 : α) = some 2 := by simpa using intValue?_intCast (α := α) 2
private theorem ivm1 : intValue? (-1 : α) = some (-1) := by
  simpa using intValue?_intCast (α := α) (-1)
end Witness

private abbrev env₀ : String → ℂ := fun s =>
  if s = "e" then -1 else if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "h" ∨ s = "p" ∨ s = "r" then 1
  else 0

theorem rubi323r5_counterexample_complex : ¬ rubi323r5.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi323r5.conditions rubi323r5.body rubi323r5.result
    rubi323r5.integrals
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : String → ℂ → ℂ, Φ = fun h w =>
      (w + 1) * (((rubi323r5.integrals.lookup h).map
        (eval Interp.complex (Function.update env₀ "x" (-1)))).getD 0) +
        (if h = "I2" then 1 else 0) := ⟨_, rfl⟩
  refine not_antiderivRecHolds_discont env₀ (-1) ?_ ?_ Φ ?_ ?_
  · simp [rubi323r5, Cond.Holds, Defined, eval, Interp.complex, env₀, iv0, iv1, iv2, ivm1]
  · filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [rubi323r5, Defined, eval, Interp.complex, env₀, iv0, iv1, iv2, ivm1, hv]
  · simp only [rubi323r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hΦd] <;>
      exact ((((hasDerivAt_id' _).add_const 1).mul_const _).add_const _).congr_deriv (by simp [rubi323r5, List.lookup])
  · intro hcont
    have hR : ∀ w, eval Interp.complex (recEnv env₀ (rubi323r5.integrals.map (·.1)) Φ "x" w)
        rubi323r5.result = Φ "I1" w + (Complex.log (-w) - Complex.log w) *
          (2 * Φ "I2" w + Φ "I3" w) := by
      intro w
      simp [rubi323r5, eval, recEnv, Interp.complex, env₀, iv0, iv1, iv2, ivm1]
      left; ring
    have hS : ContinuousAt (fun w => 2 * Φ "I2" w + Φ "I3" w) (-1) := by
      simp only [hΦd]; fun_prop
    have hS0 : 2 * Φ "I2" (-1) + Φ "I3" (-1) ≠ 0 := by
      simp [hΦd]
    have h1 : ContinuousAt (fun w => Φ "I1" w) (-1) := by simp only [hΦd]; fun_prop
    have hB : ContinuousAt (fun w => Complex.log (-w) - Complex.log w) (-1) := by
      refine ((hcont.sub h1).div hS hS0).congr ?_
      filter_upwards [hS.eventually_ne hS0] with w hw
      simp only [Pi.sub_apply, Pi.div_apply]
      rw [hR w]
      field_simp
      ring
    have hΨ : ContinuousAt (fun p : ℂ × ℂ => Complex.log (-p.1) - p.2)
        (-1, -(Real.pi * Complex.I)) :=
      (continuousAt_fst.neg.clog (by simp)).sub continuousAt_snd
    exact not_continuous_clog (fun w l => Complex.log (-w) - l) hΨ (by
      intro h
      apply mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero
      linear_combination (-1 / 2 : ℂ) * h) hB

end OSR.IntegrationRec28
