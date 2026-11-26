import OSR.IntegrationNum1

/-! # Strengthened algebraic variants: partial fractions

Proofs of RUBI rules of chapter 1 whose result is a combination of residual integrals with
constant coefficients: the integrands differ by partial fractions in which the square roots
are opaque factors. Rules containing `arith1#root` are proved over ℝ only. -/

namespace OSR.IntegrationRec256

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 1.1.3.5 #12 -/

theorem rubi1135r12Nondeg_real : rubi1135r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1135r12Nondeg.conditions rubi1135r12Nondeg.body
    rubi1135r12Nondeg.result rubi1135r12Nondeg.integrals
  intro env hc t hF
  have hW : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
      (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1135r12Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    intro h'; apply h; linear_combination h'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1135r12Nondeg.body →
      0 < env "e" + env "f" * w ^ 2 ∧ env "a" + env "b" * w ^ 2 ≠ 0 ∧ env "c" + env "d" *
          w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi1135r12Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h
    have hs : Real.sqrt (env "e" + env "f" * w ^ 2) ≠ 0 := by tauto
    refine ⟨Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs)), ?_, ?_⟩ <;> tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1135r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      have hs := (Real.sqrt_pos.mpr h.1).ne'
      simp [Defined, eval, Interp.real, ivm1R, iv2R, h.1.le, hs] at h ⊢
      try tauto
  · filter_upwards with w
    simp [rubi1135r12Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R] at *
    try tauto
  · simp only [rubi1135r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1135r12Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1135r12Nondeg.result) = fun w => env "b" *
            (env "b" * env "c" + -(env "a" * env "d"))⁻¹ * Φ "I1" w + -(env "d") *
            (env "b" * env "c" + -(env "a" * env "d"))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1135r12Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    have h0 := hD t hF.self_of_nhds
    simp [rubi1135r12Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff] at h0 ⊢
    obtain ⟨hE0, hA0, hC0⟩ := h0
    have hS0 : Real.sqrt (env "e" + env "f" * t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hE0).ne'
    have hW' : env "b" * env "c" + -(env "a" * env "d") ≠ 0 := by
      intro h; apply hW; linear_combination h
    generalize Real.sqrt (env "e" + env "f" * t ^ 2) = S at hS0 ⊢
    field_simp
    ring

/-! ## RUBI 1.2.1.7 #29–#32 (over ℝ) -/

theorem rubi1217r29Nondeg_real : rubi1217r29Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1217r29Nondeg.conditions rubi1217r29Nondeg.body
    rubi1217r29Nondeg.result rubi1217r29Nondeg.integrals
  intro env hc t hF
  have hc : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi1217r29Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1217r29Nondeg.body →
      0 < env "d" + env "e" * w + env "f" * w ^ 2 ∧ env "a" + env "c" * w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi1217r29Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h
    have hs : Real.sqrt (env "d" + env "e" * w + env "f" * w ^ 2) ≠ 0 := by tauto
    refine ⟨Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs)), ?_⟩
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1217r29Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      have hs := (Real.sqrt_pos.mpr h.1).ne'
      simp [Defined, eval, Interp.real, ivm1R, iv2R, h.1.le, hs] at h ⊢
      try tauto
  · filter_upwards with w
    simp [rubi1217r29Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R] at *
    try tauto
  · simp only [rubi1217r29Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1217r29Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1217r29Nondeg.result) = fun w => env "C" * (env "c")⁻¹ * Φ "I1" w +
            (env "c")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1217r29Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    have h0 := hD t hF.self_of_nhds
    simp [rubi1217r29Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff] at h0 ⊢
    obtain ⟨hE0, hA0⟩ := h0
    have hS0 : Real.sqrt (env "d" + env "e" * t + env "f" * t ^ 2) ≠ 0 :=
        (Real.sqrt_pos.mpr hE0).ne'
    generalize Real.sqrt (env "d" + env "e" * t + env "f" * t ^ 2) = S at hS0 ⊢
    field_simp
    ring

theorem rubi1217r30Nondeg_real : rubi1217r30Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1217r30Nondeg.conditions rubi1217r30Nondeg.body
    rubi1217r30Nondeg.result rubi1217r30Nondeg.integrals
  intro env hc t hF
  have hc : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi1217r30Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1217r30Nondeg.body →
      0 < env "d" + env "e" * w + env "f" * w ^ 2 ∧ env "a" + env "c" * w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi1217r30Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h
    have hs : Real.sqrt (env "d" + env "e" * w + env "f" * w ^ 2) ≠ 0 := by tauto
    refine ⟨Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs)), ?_⟩
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1217r30Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      have hs := (Real.sqrt_pos.mpr h.1).ne'
      simp [Defined, eval, Interp.real, ivm1R, iv2R, h.1.le, hs] at h ⊢
      try tauto
  · filter_upwards with w
    simp [rubi1217r30Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R] at *
    try tauto
  · simp only [rubi1217r30Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1217r30Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1217r30Nondeg.result) = fun w => env "C" * (env "c")⁻¹ * Φ "I1" w +
            (env "A" * env "c" - env "a" * env "C") * (env "c")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1217r30Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    have h0 := hD t hF.self_of_nhds
    simp [rubi1217r30Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff] at h0 ⊢
    obtain ⟨hE0, hA0⟩ := h0
    have hS0 : Real.sqrt (env "d" + env "e" * t + env "f" * t ^ 2) ≠ 0 :=
        (Real.sqrt_pos.mpr hE0).ne'
    generalize Real.sqrt (env "d" + env "e" * t + env "f" * t ^ 2) = S at hS0 ⊢
    field_simp
    ring

theorem rubi1217r31Nondeg_real : rubi1217r31Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1217r31Nondeg.conditions rubi1217r31Nondeg.body
    rubi1217r31Nondeg.result rubi1217r31Nondeg.integrals
  intro env hc t hF
  have hc : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi1217r31Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1217r31Nondeg.body →
      0 < env "d" + env "f" * w ^ 2 ∧ env "a" + env "b" * w + env "c" * w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi1217r31Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h
    have hs : Real.sqrt (env "d" + env "f" * w ^ 2) ≠ 0 := by tauto
    refine ⟨Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs)), ?_⟩
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1217r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      have hs := (Real.sqrt_pos.mpr h.1).ne'
      simp [Defined, eval, Interp.real, ivm1R, iv2R, h.1.le, hs] at h ⊢
      try tauto
  · filter_upwards with w
    simp [rubi1217r31Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R] at *
    try tauto
  · simp only [rubi1217r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1217r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1217r31Nondeg.result) = fun w => env "C" * (env "c")⁻¹ * Φ "I1" w +
            (env "c")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1217r31Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    have h0 := hD t hF.self_of_nhds
    simp [rubi1217r31Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff] at h0 ⊢
    obtain ⟨hE0, hA0⟩ := h0
    have hS0 : Real.sqrt (env "d" + env "f" * t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hE0).ne'
    generalize Real.sqrt (env "d" + env "f" * t ^ 2) = S at hS0 ⊢
    field_simp
    ring

theorem rubi1217r32Nondeg_real : rubi1217r32Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1217r32Nondeg.conditions rubi1217r32Nondeg.body
    rubi1217r32Nondeg.result rubi1217r32Nondeg.integrals
  intro env hc t hF
  have hc : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi1217r32Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1217r32Nondeg.body →
      0 < env "d" + env "f" * w ^ 2 ∧ env "a" + env "b" * w + env "c" * w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi1217r32Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h
    have hs : Real.sqrt (env "d" + env "f" * w ^ 2) ≠ 0 := by tauto
    refine ⟨Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs)), ?_⟩
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1217r32Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      have hs := (Real.sqrt_pos.mpr h.1).ne'
      simp [Defined, eval, Interp.real, ivm1R, iv2R, h.1.le, hs] at h ⊢
      try tauto
  · filter_upwards with w
    simp [rubi1217r32Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R] at *
    try tauto
  · simp only [rubi1217r32Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1217r32Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1217r32Nondeg.result) = fun w => env "C" * (env "c")⁻¹ * Φ "I1" w +
            (env "c")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1217r32Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    have h0 := hD t hF.self_of_nhds
    simp [rubi1217r32Nondeg, eval, Interp.real, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff] at h0 ⊢
    obtain ⟨hE0, hA0⟩ := h0
    have hS0 : Real.sqrt (env "d" + env "f" * t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hE0).ne'
    generalize Real.sqrt (env "d" + env "f" * t ^ 2) = S at hS0 ⊢
    field_simp
    ring

/-! ## RUBI 1.1.1.4 #16 -/

theorem rubi1114r16Nondeg_real : rubi1114r16Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1114r16Nondeg.conditions rubi1114r16Nondeg.body
    rubi1114r16Nondeg.result rubi1114r16Nondeg.integrals
  intro env hc t hF
  have hW : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
      (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1114r16Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    intro h'; apply h; linear_combination h'
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1114r16Nondeg, Defined, eval, Interp.real, hkp] at h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1114r16Nondeg.body →
      (q < 0 → env "e" + env "f" * w ≠ 0) ∧ env "a" + env "b" * w ≠ 0 ∧ env "c" + env "d" *
          w ≠ 0 := by
    intro w h
    simp [rubi1114r16Nondeg, Defined, eval, Interp.real, hkp, ivm1R] at h
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1114r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, ivm1R, hkp] at h ⊢
      try tauto
  · filter_upwards with w
    simp [rubi1114r16Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp] at *
    try tauto
  · simp only [rubi1114r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1114r16Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1114r16Nondeg.result) = fun w => (env "b" * env "g" - env "a" * env "h") *
            (env "b" * env "c" - env "a" * env "d")⁻¹ * Φ "I1" w +
            -(env "d" * env "g" - env "c" * env "h") * (env "b" * env "c" - env "a" * env "d")⁻¹ *
            Φ "I2" w := by
      funext w
      simp [rubi1114r16Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    have h0 := hD t hF.self_of_nhds
    simp [rubi1114r16Nondeg, eval, Interp.real, ivm1R, hkp, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff] at h0 ⊢
    obtain ⟨-, hA0, hC0⟩ := h0
    have hW' : env "b" * env "c" + -(env "a" * env "d") ≠ 0 := by
      intro h; apply hW; linear_combination h
    generalize (env "e" + env "f" * t) ^ q = Q
    field_simp
    ring

theorem rubi1114r16Nondeg_complex : rubi1114r16Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1114r16Nondeg.conditions rubi1114r16Nondeg.body
    rubi1114r16Nondeg.result rubi1114r16Nondeg.integrals
  intro env hc t hF
  have hW : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
      (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1114r16Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    intro h'; apply h; linear_combination h'
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1114r16Nondeg, Defined, eval, Interp.complex, hkp] at h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1114r16Nondeg.body →
      (q < 0 → env "e" + env "f" * w ≠ 0) ∧ env "a" + env "b" * w ≠ 0 ∧ env "c" + env "d" *
          w ≠ 0 := by
    intro w h
    simp [rubi1114r16Nondeg, Defined, eval, Interp.complex, hkp, ivm1C] at h
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1114r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, ivm1C, hkp] at h ⊢
      try tauto
  · filter_upwards with w
    simp [rubi1114r16Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp] at *
    try tauto
  · simp only [rubi1114r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1114r16Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1114r16Nondeg.result) = fun w => (env "b" * env "g" - env "a" * env "h") *
            (env "b" * env "c" - env "a" * env "d")⁻¹ * Φ "I1" w +
            -(env "d" * env "g" - env "c" * env "h") * (env "b" * env "c" - env "a" * env "d")⁻¹ *
            Φ "I2" w := by
      funext w
      simp [rubi1114r16Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    have h0 := hD t hF.self_of_nhds
    simp [rubi1114r16Nondeg, eval, Interp.complex, ivm1C, hkp, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff] at h0 ⊢
    obtain ⟨-, hA0, hC0⟩ := h0
    have hW' : env "b" * env "c" + -(env "a" * env "d") ≠ 0 := by
      intro h; apply hW; linear_combination h
    generalize (env "e" + env "f" * t) ^ q = Q
    field_simp
    ring

/-! ## RUBI 1.1.3.5 #27 -/

theorem rubi1135r27Nondeg_real : rubi1135r27Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1135r27Nondeg.conditions rubi1135r27Nondeg.body
    rubi1135r27Nondeg.result rubi1135r27Nondeg.integrals
  intro env hc t hF
  have hW : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
      (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1135r27Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    intro h'; apply h; linear_combination h'
  rcases hkq : intValue? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r27Nondeg, Defined, eval, Interp.real, hkq] at h
  rcases hkr : intValue? (env "r") with _ | r
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r27Nondeg, Defined, eval, Interp.real, hkq, hkr] at h
  have hqle : env "q" ≤ -1 := by
    have h := hc (.ge (.int (-1)) (.var "q")) (by simp [rubi1135r27Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real] at h
    rcases h with h | h
    · exact h.le
    · rw [h]
  have hq : q ≤ -1 := by
    rw [(intValue?_eq _ _).1 hkq] at hqle
    exact_mod_cast hqle
  have hq0 : q < 0 := by omega
  have eq1 : intValue? (env "q" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1135r27Nondeg.body →
      env "c" + env "d" * w ^ 2 ≠ 0 ∧ (r < 0 → env "e" + env "f" * w ^ 2 ≠ 0) ∧ env "a" + env "b" *
          w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi1135r27Nondeg, Defined, eval, Interp.real, hkq, hkr, hq0, ivm1R, iv2R] at h
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1135r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, ivm1R, iv2R, hkq, hkr, eq1, hq0] at h ⊢
      try tauto
  · filter_upwards with w
    simp [rubi1135r27Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hkq, hkr, eq1,
        hq0] at *
    try tauto
  · simp only [rubi1135r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1135r27Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1135r27Nondeg.result) = fun w => -(env "d") *
            (env "b" * env "c" - env "a" * env "d")⁻¹ * Φ "I1" w + env "b" *
            (env "b" * env "c" - env "a" * env "d")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1135r27Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    have h0 := hD t hF.self_of_nhds
    simp [rubi1135r27Nondeg, eval, Interp.real, ivm1R, iv2R, hkq, hkr, eq1, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff] at h0 ⊢
    obtain ⟨hX0, -, hA0⟩ := h0
    rw [zpow_add_one₀ hX0]
    have hW' : env "b" * env "c" + -(env "a" * env "d") ≠ 0 := by
      intro h; apply hW; linear_combination h
    generalize (env "c" + env "d" * t ^ 2) ^ q = Q
    generalize (env "e" + env "f" * t ^ 2) ^ r = Q'
    have hW'' : -(env "d" * env "a") + env "b" * env "c" ≠ 0 := by
      intro h; apply hW; linear_combination h
    field_simp
    rw [div_eq_iff (by intro h; apply hW; linear_combination h)]
    ring

theorem rubi1135r27Nondeg_complex : rubi1135r27Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1135r27Nondeg.conditions rubi1135r27Nondeg.body
    rubi1135r27Nondeg.result rubi1135r27Nondeg.integrals
  intro env hc t hF
  have hW : env "b" * env "c" - env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
      (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1135r27Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    intro h'; apply h; linear_combination h'
  rcases hkq : intValue? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r27Nondeg, Defined, eval, Interp.complex, hkq] at h
  rcases hkr : intValue? (env "r") with _ | r
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1135r27Nondeg, Defined, eval, Interp.complex, hkq, hkr] at h
  have hqle : (env "q").re ≤ -1 := by
    have h := hc (.ge (.int (-1)) (.var "q")) (by simp [rubi1135r27Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    rcases h with h | h
    · exact h.2.le
    · rw [← h]; simp
  have hq : q ≤ -1 := by
    rw [(intValue?_eq _ _).1 hkq] at hqle
    have : (q : ℝ) ≤ -1 := by simpa using hqle
    exact_mod_cast this
  have hq0 : q < 0 := by omega
  have eq1 : intValue? (env "q" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1135r27Nondeg.body →
      env "c" + env "d" * w ^ 2 ≠ 0 ∧ (r < 0 → env "e" + env "f" * w ^ 2 ≠ 0) ∧ env "a" + env "b" *
          w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi1135r27Nondeg, Defined, eval, Interp.complex, hkq, hkr, hq0, ivm1C, iv2C] at h
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1135r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, ivm1C, iv2C, hkq, hkr, eq1, hq0] at h ⊢
      try tauto
  · filter_upwards with w
    simp [rubi1135r27Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hkq, hkr, eq1,
        hq0] at *
    try tauto
  · simp only [rubi1135r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1135r27Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1135r27Nondeg.result) = fun w => -(env "d") *
            (env "b" * env "c" - env "a" * env "d")⁻¹ * Φ "I1" w + env "b" *
            (env "b" * env "c" - env "a" * env "d")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1135r27Nondeg, eval, recEnv, Interp.complex, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      try ring
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    have h0 := hD t hF.self_of_nhds
    simp [rubi1135r27Nondeg, eval, Interp.complex, ivm1C, iv2C, hkq, hkr, eq1,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] at h0 ⊢
    obtain ⟨hX0, -, hA0⟩ := h0
    rw [zpow_add_one₀ hX0]
    have hW' : env "b" * env "c" + -(env "a" * env "d") ≠ 0 := by
      intro h; apply hW; linear_combination h
    generalize (env "c" + env "d" * t ^ 2) ^ q = Q
    generalize (env "e" + env "f" * t ^ 2) ^ r = Q'
    have hW'' : -(env "d" * env "a") + env "b" * env "c" ≠ 0 := by
      intro h; apply hW; linear_combination h
    field_simp
    rw [div_eq_iff (by intro h; apply hW; linear_combination h)]
    ring

end OSR.IntegrationRec256
