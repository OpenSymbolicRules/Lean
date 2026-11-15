import OSR.IntegrationRec24

/-!
# Integration (RUBI): refutations carried to the other domain

Eight catalogue rules were refuted in one domain only, the witness of the
other being "not established".  The same witnesses refute them in the other
domain as well; where the integrand is only defined near the witness point
(over ℂ, for instance, `1 + x²` vanishes at `±i`), definedness near it
follows from continuity.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec25

open OSR OSR.Calculus OSR.IntegrationRec3 OSR.IntegrationRec11 OSR.IntegrationRec14 Filter Topology

private theorem clog2 : Complex.log 2 ≠ 0 := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
  exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

section
variable {α : Type} [Field α] [CharZero α]
private theorem iv0 : intValue? (0 : α) = some 0 := by simpa using intValue?_intCast (α := α) 0
private theorem iv1 : intValue? (1 : α) = some 1 := by simpa using intValue?_intCast (α := α) 1
private theorem iv2 : intValue? (2 : α) = some 2 := by simpa using intValue?_intCast (α := α) 2
private theorem iv3 : intValue? (3 : α) = some 3 := by simpa using intValue?_intCast (α := α) 3
private theorem iv4 : intValue? (4 : α) = some 4 := by simpa using intValue?_intCast (α := α) 4
private theorem ivm1 : intValue? (-1 : α) = some (-1) := by simpa using intValue?_intCast (α := α) (-1)
private theorem ivm2 : intValue? (-2 : α) = some (-2) := by simpa using intValue?_intCast (α := α) (-2)
private theorem ivm3 : intValue? (-3 : α) = some (-3) := by simpa using intValue?_intCast (α := α) (-3)
private theorem ivnat (n : ℕ) [n.AtLeastTwo] : intValue? (OfNat.ofNat n : α) = some (OfNat.ofNat n) := by
  simpa using intValue?_intCast (α := α) (OfNat.ofNat n : ℤ)
private theorem ivneg (n : ℕ) [n.AtLeastTwo] :
    intValue? (-(OfNat.ofNat n : α)) = some (-(OfNat.ofNat n)) := by
  simpa using intValue?_intCast (α := α) (-(OfNat.ofNat n : ℤ))
private theorem ivm6 : intValue? (-6 : α) = some (-6) := by simpa using intValue?_intCast (α := α) (-6)
private theorem ivex2 : ∃ n, intValue? (2 : α) = some n ∧ 0 ≤ n := ⟨2, iv2, by norm_num⟩
private theorem ivexInt (z : ℤ) : ∃ n, intValue? (z : α) = some n := ⟨z, intValue?_intCast z⟩
private theorem ivexm1 : ∃ n, intValue? (-1 : α) = some n := ⟨_, ivm1⟩
private theorem ivm4 : intValue? (-4 : α) = some (-4) := by simpa using intValue?_intCast (α := α) (-4)
private theorem ivexm4 : ∃ n, intValue? (-4 : α) = some n := ⟨_, ivm4⟩
private theorem ivexm6 : ∃ n, intValue? (-6 : α) = some n := ⟨_, ivm6⟩
end

-- from OSR.IntegrationRec3 (complex)
theorem rubi315r33_counterexample_real : ¬ rubi315r33.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi315r33.conditions rubi315r33.body rubi315r33.result rubi315r33.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "r" then 2 else 0) (1 : ℝ) (by simp [rubi315r33, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi315r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> exact ⟨lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (mul_ne_zero two_ne_zero (pow_ne_zero 2 hw)))), lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hw))⟩)
    (fun h w => w * (((rubi315r33.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "r" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi315r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

-- from OSR.IntegrationRec3 (real)
theorem rubi34r9_counterexample_complex : ¬ rubi34r9.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi34r9.conditions rubi34r9.body rubi34r9.result rubi34r9.integrals
  have hq : ∀ᶠ w in 𝓝 (1 : ℂ), 2 + 2 * w ^ 2 ≠ 0 := by
    have hc : ContinuousAt (fun w : ℂ => 2 + 2 * w ^ 2) 1 := by fun_prop
    exact hc.eventually_ne (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 2 else 0) (1 : ℂ) (by simp [rubi34r9, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [hq] with w hw2; simp [rubi34r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw2])
    (fun h w => w * (((rubi34r9.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi34r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi34r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

-- from OSR.IntegrationRec3 (real)
theorem rubi476r2_counterexample_complex : ¬ rubi476r2.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi476r2.conditions rubi476r2.body rubi476r2.result rubi476r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi476r2, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi476r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi476r2.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi476r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi476r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

-- from OSR.IntegrationRec11 (real)
theorem rubi1222r19_counterexample_complex : ¬ rubi1222r19.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1222r19.conditions rubi1222r19.body rubi1222r19.result rubi1222r19.integrals
  have hq : ∀ᶠ w in 𝓝 (1 : ℂ), 1 + w ^ 2 ≠ 0 := by
    have hc : ContinuousAt (fun w : ℂ => 1 + w ^ 2) 1 := by fun_prop
    exact hc.eventually_ne (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "d" then 1 else if s = "m" then 4 else 0) (1 : ℂ) (by simp [rubi1222r19, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [hq] with w hw2; simp [rubi1222r19, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw2])
    (fun h w => w * (((rubi1222r19.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "d" then 1 else if s = "m" then 4 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1222r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1222r19, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

-- from OSR.IntegrationRec14 (real)
theorem rubi35r14_counterexample_complex : ¬ rubi35r14.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi35r14.conditions rubi35r14.body rubi35r14.result rubi35r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "r" then 2 else if s = "q" then 3 else 0) (1 : ℂ) (by simp [rubi35r14, Cond.Holds, Defined, eval, Interp.complex, clog2, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi35r14, Defined, eval, Interp.complex, clog2, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi35r14.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "r" then 2 else if s = "q" then 3 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi35r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi35r14, Defined, eval, Interp.complex, clog2, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

-- from OSR.IntegrationRec14 (real)
theorem rubi35r17_counterexample_complex : ¬ rubi35r17.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi35r17.conditions rubi35r17.body rubi35r17.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "m" ∨ s = "r" then 2 else if s = "q" then 3 else 0) (1 : ℂ) (by simp [rubi35r17, Cond.Holds, Defined, eval, Interp.complex, clog2, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi35r17, Defined, eval, Interp.complex, clog2, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi35r17, Defined, eval, Interp.complex, clog2, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

-- from OSR.IntegrationRec14 (real)
theorem rubi35r22_counterexample_complex : ¬ rubi35r22.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi35r22.conditions rubi35r22.body rubi35r22.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "q" then 1 else if s = "c" then 2 else 0) (1 : ℂ) (by simp [rubi35r22, Cond.Holds, Defined, eval, Interp.complex, clog2, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi35r22, Defined, eval, Interp.complex, clog2, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi35r22, Defined, eval, Interp.complex, clog2, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

-- from OSR.IntegrationRec14 (real)
theorem rubi35r23_counterexample_complex : ¬ rubi35r23.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi35r23.conditions rubi35r23.body rubi35r23.result rubi35r23.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then 1 else if s = "c" then 2 else 0) (1 : ℂ) (by simp [rubi35r23, Cond.Holds, Defined, eval, Interp.complex, clog2, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi35r23, Defined, eval, Interp.complex, clog2, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi35r23.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then 1 else if s = "c" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi35r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi35r23, Defined, eval, Interp.complex, clog2, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec25
