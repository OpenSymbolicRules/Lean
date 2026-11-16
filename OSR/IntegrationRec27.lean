import OSR.IntegrationRec26

/-!
# Integration (RUBI): more branch-cut refutations over ℂ

By-parts rules whose result is `x F(x)` plus residual integrals: at witnesses
where `F` contains `log x`, the result jumps across the cut at `x = -1`
(`OSR.IntegrationRec26.not_continuous_clog`), while the residual
antiderivatives, chosen linear, are continuous.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec27

open OSR OSR.Calculus OSR.IntegrationRec26 Filter Topology

section Witness
variable {α : Type} [Field α] [CharZero α]
private theorem iv0 : intValue? (0 : α) = some 0 := by simpa using intValue?_intCast (α := α) 0
private theorem iv1 : intValue? (1 : α) = some 1 := by simpa using intValue?_intCast (α := α) 1
private theorem iv2 : intValue? (2 : α) = some 2 := by simpa using intValue?_intCast (α := α) 2
private theorem ivm1 : intValue? (-1 : α) = some (-1) := by
  simpa using intValue?_intCast (α := α) (-1)
private theorem ivs : intValue? ((2 : ℂ) + -1) = some 1 := by
  rw [show (2 : ℂ) + -1 = 1 by norm_num]; exact iv1
end Witness

private theorem csin_pi_I : Complex.sin (Real.pi * Complex.I) ≠ 0 := by
  rw [Complex.sin_mul_I, ← Complex.ofReal_sinh]
  exact mul_ne_zero (by exact_mod_cast (Real.sinh_pos_iff.2 Real.pi_pos).ne') Complex.I_ne_zero

private theorem ccos_pi_I : Complex.cos (Real.pi * Complex.I) ≠ 0 := by
  rw [Complex.cos_mul_I, ← Complex.ofReal_cosh]
  exact_mod_cast (Real.cosh_pos Real.pi).ne'

private theorem hne_log :
    (fun (_ l : ℂ) => l) (-1) (Real.pi * Complex.I) ≠ (fun (_ l : ℂ) => l) (-1) (-(Real.pi * Complex.I)) := by
  intro h; have := congrArg Complex.im h; simp at this; linarith [Real.pi_pos]

/-- The discontinuity survives the addition of a continuous function. -/
theorem not_continuous_clog_add (Ψ : ℂ → ℂ → ℂ)
    (hΨ : ContinuousAt (fun p : ℂ × ℂ => Ψ p.1 p.2) (-1, -(Real.pi * Complex.I)))
    (hne : Ψ (-1) (Real.pi * Complex.I) ≠ Ψ (-1) (-(Real.pi * Complex.I)))
    (g : ℂ → ℂ) (hg : ContinuousAt g (-1)) :
    ¬ ContinuousAt (fun w => Ψ w (Complex.log w) + g w) (-1) := by
  intro h
  apply not_continuous_clog Ψ hΨ hne
  convert h.sub hg using 1
  funext w
  simp

theorem logLinPow_counterexample_complex : ¬ OSR.IntegrationRec.logLinPow.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" OSR.IntegrationRec.logLinPow.conditions OSR.IntegrationRec.logLinPow.body OSR.IntegrationRec.logLinPow.result
    OSR.IntegrationRec.logLinPow.integrals
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : String → ℂ → ℂ, Φ = fun h w =>
      w * (((OSR.IntegrationRec.logLinPow.integrals.lookup h).map
        (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "n" ∨ s = "p" then 1 else 0 : String → ℂ) "x" (-1)))).getD 0) := ⟨_, rfl⟩
  refine not_antiderivRecHolds_discont (fun s => if s = "b" ∨ s = "c" ∨ s = "n" ∨ s = "p" then 1 else 0 : String → ℂ) (-1) ?_ ?_ Φ ?_ ?_
  · norm_num [OSR.IntegrationRec.logLinPow, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1]
  · filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [OSR.IntegrationRec.logLinPow, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1, hv]
  · simp only [OSR.IntegrationRec.logLinPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [hΦd, List.lookup]; exact hasDerivAt_mul_const _)
  · have hfun : (fun v => eval Interp.complex (recEnv (fun s => if s = "b" ∨ s = "c" ∨ s = "n" ∨ s = "p" then 1 else 0 : String → ℂ)
        (OSR.IntegrationRec.logLinPow.integrals.map (·.1)) Φ "x" v) OSR.IntegrationRec.logLinPow.result) = fun w => (fun w l => w * l) w (Complex.log w) + (fun w => -Φ "I1" w) w := by
      funext w
      simp [OSR.IntegrationRec.logLinPow, eval, recEnv, Interp.complex, iv0, iv1, iv2, ivm1, ivs]
      try ring
    rw [hfun]
    exact not_continuous_clog_add (fun w l => w * l) (by fun_prop) (by intro h; have := congrArg Complex.im h; simp at this; linarith [Real.pi_pos])
      (fun w => -Φ "I1" w) (by simp only [hΦd]; fun_prop)

theorem logPowLogPow_counterexample_complex : ¬ OSR.IntegrationRec7.logPowLogPow.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" OSR.IntegrationRec7.logPowLogPow.conditions OSR.IntegrationRec7.logPowLogPow.body OSR.IntegrationRec7.logPowLogPow.result
    OSR.IntegrationRec7.logPowLogPow.integrals
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : String → ℂ → ℂ, Φ = fun h w =>
      w * (((OSR.IntegrationRec7.logPowLogPow.integrals.lookup h).map
        (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "n" ∨ s = "p" ∨ s = "d" ∨ s = "f" ∨ s = "r" ∨ s = "q" then 1 else 0 : String → ℂ) "x" (-1)))).getD 0) := ⟨_, rfl⟩
  refine not_antiderivRecHolds_discont (fun s => if s = "b" ∨ s = "c" ∨ s = "n" ∨ s = "p" ∨ s = "d" ∨ s = "f" ∨ s = "r" ∨ s = "q" then 1 else 0 : String → ℂ) (-1) ?_ ?_ Φ ?_ ?_
  · norm_num [OSR.IntegrationRec7.logPowLogPow, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1]
  · filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [OSR.IntegrationRec7.logPowLogPow, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1, hv]
  · simp only [OSR.IntegrationRec7.logPowLogPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [hΦd, List.lookup]; exact hasDerivAt_mul_const _)
  · have hfun : (fun v => eval Interp.complex (recEnv (fun s => if s = "b" ∨ s = "c" ∨ s = "n" ∨ s = "p" ∨ s = "d" ∨ s = "f" ∨ s = "r" ∨ s = "q" then 1 else 0 : String → ℂ)
        (OSR.IntegrationRec7.logPowLogPow.integrals.map (·.1)) Φ "x" v) OSR.IntegrationRec7.logPowLogPow.result) = fun w => (fun w l => w * l) w (Complex.log w) + (fun w => -Φ "I2" w) w := by
      funext w
      simp [OSR.IntegrationRec7.logPowLogPow, eval, recEnv, Interp.complex, iv0, iv1, iv2, ivm1, ivs]
      try ring
    rw [hfun]
    exact not_continuous_clog_add (fun w l => w * l) (by fun_prop) (by intro h; have := congrArg Complex.im h; simp at this; linarith [Real.pi_pos])
      (fun w => -Φ "I2" w) (by simp only [hΦd]; fun_prop)

theorem quadPowLog_counterexample_complex : ¬ OSR.IntegrationRec7.quadPowLog.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" OSR.IntegrationRec7.quadPowLog.conditions OSR.IntegrationRec7.quadPowLog.body OSR.IntegrationRec7.quadPowLog.result
    OSR.IntegrationRec7.quadPowLog.integrals
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : String → ℂ → ℂ, Φ = fun h w =>
      w * (((OSR.IntegrationRec7.quadPowLog.integrals.lookup h).map
        (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "q" ∨ s = "b" ∨ s = "c" ∨ s = "n" then 1 else 0 : String → ℂ) "x" (-1)))).getD 0) := ⟨_, rfl⟩
  refine not_antiderivRecHolds_discont (fun s => if s = "d" ∨ s = "q" ∨ s = "b" ∨ s = "c" ∨ s = "n" then 1 else 0 : String → ℂ) (-1) ?_ ?_ Φ ?_ ?_
  · norm_num [OSR.IntegrationRec7.quadPowLog, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1]
  · filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [OSR.IntegrationRec7.quadPowLog, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1, hv]
  · simp only [OSR.IntegrationRec7.quadPowLog, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [hΦd, List.lookup]; exact hasDerivAt_mul_const _)
  · have hfun : (fun v => eval Interp.complex (recEnv (fun s => if s = "d" ∨ s = "q" ∨ s = "b" ∨ s = "c" ∨ s = "n" then 1 else 0 : String → ℂ)
        (OSR.IntegrationRec7.quadPowLog.integrals.map (·.1)) Φ "x" v) OSR.IntegrationRec7.quadPowLog.result) = fun w => (fun w l => w * l * (2 + 1)⁻¹) w (Complex.log w) + (fun w => -((2 + 1)⁻¹ * Φ "I1" w) + 2 * (2 + 1)⁻¹ * Φ "I2" w) w := by
      funext w
      simp [OSR.IntegrationRec7.quadPowLog, eval, recEnv, Interp.complex, iv0, iv1, iv2, ivm1, ivs]
      try ring
    rw [hfun]
    exact not_continuous_clog_add (fun w l => w * l * (2 + 1)⁻¹) (by fun_prop) (by
      intro h
      apply mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero
      linear_combination (-3 / 2 : ℂ) * h)
      (fun w => -((2 + 1)⁻¹ * Φ "I1" w) + 2 * (2 + 1)⁻¹ * Φ "I2" w) (by simp only [hΦd]; fun_prop)

theorem sinPowLog_counterexample_complex : ¬ OSR.IntegrationRec7.sinPowLog.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" OSR.IntegrationRec7.sinPowLog.conditions OSR.IntegrationRec7.sinPowLog.body OSR.IntegrationRec7.sinPowLog.result
    OSR.IntegrationRec7.sinPowLog.integrals
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : String → ℂ → ℂ, Φ = fun h w =>
      w * (((OSR.IntegrationRec7.sinPowLog.integrals.lookup h).map
        (eval Interp.complex (Function.update (fun s => if s = "p" then 2 else if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0 : String → ℂ) "x" (-1)))).getD 0) := ⟨_, rfl⟩
  refine not_antiderivRecHolds_discont (fun s => if s = "p" then 2 else if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0 : String → ℂ) (-1) ?_ ?_ Φ ?_ ?_
  · norm_num [OSR.IntegrationRec7.sinPowLog, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1]
  · filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [OSR.IntegrationRec7.sinPowLog, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1, hv]
  · simp only [OSR.IntegrationRec7.sinPowLog, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [hΦd, List.lookup]; exact hasDerivAt_mul_const _)
  · have hfun : (fun v => eval Interp.complex (recEnv (fun s => if s = "p" then 2 else if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0 : String → ℂ)
        (OSR.IntegrationRec7.sinPowLog.integrals.map (·.1)) Φ "x" v) OSR.IntegrationRec7.sinPowLog.result) = fun w => (fun w l => w * Complex.sin l ^ 2 * (2 ^ 2 + 1)⁻¹ - 2 * w * Complex.cos l * Complex.sin l * (2 ^ 2 + 1)⁻¹) w (Complex.log w) + (fun w => 2 * (2 + -1) * (2 ^ 2 + 1)⁻¹ * Φ "I1" w) w := by
      funext w
      simp [OSR.IntegrationRec7.sinPowLog, eval, recEnv, Interp.complex, iv0, iv1, iv2, ivm1, ivs]
      try ring
    rw [hfun]
    exact not_continuous_clog_add (fun w l => w * Complex.sin l ^ 2 * (2 ^ 2 + 1)⁻¹ - 2 * w * Complex.cos l * Complex.sin l * (2 ^ 2 + 1)⁻¹) (by fun_prop) (by intro h; apply mul_ne_zero ccos_pi_I csin_pi_I; simp [Complex.sin_neg, Complex.cos_neg] at h; linear_combination (5 / 4 : ℂ) * h)
      (fun w => 2 * (2 + -1) * (2 ^ 2 + 1)⁻¹ * Φ "I1" w) (by simp only [hΦd]; fun_prop)

theorem cosPowLog_counterexample_complex : ¬ OSR.IntegrationRec7.cosPowLog.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" OSR.IntegrationRec7.cosPowLog.conditions OSR.IntegrationRec7.cosPowLog.body OSR.IntegrationRec7.cosPowLog.result
    OSR.IntegrationRec7.cosPowLog.integrals
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : String → ℂ → ℂ, Φ = fun h w =>
      w * (((OSR.IntegrationRec7.cosPowLog.integrals.lookup h).map
        (eval Interp.complex (Function.update (fun s => if s = "p" then 2 else if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0 : String → ℂ) "x" (-1)))).getD 0) := ⟨_, rfl⟩
  refine not_antiderivRecHolds_discont (fun s => if s = "p" then 2 else if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0 : String → ℂ) (-1) ?_ ?_ Φ ?_ ?_
  · norm_num [OSR.IntegrationRec7.cosPowLog, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1]
  · filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [OSR.IntegrationRec7.cosPowLog, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1, hv]
  · simp only [OSR.IntegrationRec7.cosPowLog, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [hΦd, List.lookup]; exact hasDerivAt_mul_const _)
  · have hfun : (fun v => eval Interp.complex (recEnv (fun s => if s = "p" then 2 else if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0 : String → ℂ)
        (OSR.IntegrationRec7.cosPowLog.integrals.map (·.1)) Φ "x" v) OSR.IntegrationRec7.cosPowLog.result) = fun w => (fun w l => w * Complex.cos l ^ 2 * (2 ^ 2 + 1)⁻¹ + 2 * w * Complex.cos l * Complex.sin l * (2 ^ 2 + 1)⁻¹) w (Complex.log w) + (fun w => 2 * (2 + -1) * (2 ^ 2 + 1)⁻¹ * Φ "I1" w) w := by
      funext w
      simp [OSR.IntegrationRec7.cosPowLog, eval, recEnv, Interp.complex, iv0, iv1, iv2, ivm1, ivs]
      try ring
    rw [hfun]
    exact not_continuous_clog_add (fun w l => w * Complex.cos l ^ 2 * (2 ^ 2 + 1)⁻¹ + 2 * w * Complex.cos l * Complex.sin l * (2 ^ 2 + 1)⁻¹) (by fun_prop) (by intro h; apply mul_ne_zero ccos_pi_I csin_pi_I; simp [Complex.sin_neg, Complex.cos_neg] at h; linear_combination (-5 / 4 : ℂ) * h)
      (fun w => 2 * (2 + -1) * (2 ^ 2 + 1)⁻¹ * Φ "I1" w) (by simp only [hΦd]; fun_prop)

theorem rubi33r40_counterexample_complex : ¬ OSR.IntegrationRec14.rubi33r40.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" OSR.IntegrationRec14.rubi33r40.conditions OSR.IntegrationRec14.rubi33r40.body OSR.IntegrationRec14.rubi33r40.result
    OSR.IntegrationRec14.rubi33r40.integrals
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : String → ℂ → ℂ, Φ = fun h w =>
      w * (((OSR.IntegrationRec14.rubi33r40.integrals.lookup h).map
        (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "f" ∨ s = "c" ∨ s = "d" ∨ s = "h" ∨ s = "i" then 1 else 0 : String → ℂ) "x" (-1)))).getD 0) := ⟨_, rfl⟩
  refine not_antiderivRecHolds_discont (fun s => if s = "a" ∨ s = "f" ∨ s = "c" ∨ s = "d" ∨ s = "h" ∨ s = "i" then 1 else 0 : String → ℂ) (-1) ?_ ?_ Φ ?_ ?_
  · simp [OSR.IntegrationRec14.rubi33r40, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1]
  · filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [OSR.IntegrationRec14.rubi33r40, Defined, eval, Interp.complex, iv0, iv1, iv2, ivm1, hv]
  · simp only [OSR.IntegrationRec14.rubi33r40, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [hΦd, List.lookup]; exact hasDerivAt_mul_const _)
  · have hfun : (fun v => eval Interp.complex (recEnv (fun s => if s = "a" ∨ s = "f" ∨ s = "c" ∨ s = "d" ∨ s = "h" ∨ s = "i" then 1 else 0 : String → ℂ)
        (OSR.IntegrationRec14.rubi33r40.integrals.map (·.1)) Φ "x" v) OSR.IntegrationRec14.rubi33r40.result) = fun w => Complex.log w := by
      funext w
      simp [OSR.IntegrationRec14.rubi33r40, eval, recEnv, Interp.complex, iv0, iv1, iv2, ivm1]
    rw [hfun]
    exact not_continuous_clog (fun _ l => l) (by fun_prop) hne_log

end OSR.IntegrationRec27
