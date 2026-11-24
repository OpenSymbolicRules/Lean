import OSR.IntegrationNum1

open OSR OSR.Calculus Filter Topology
namespace OSR.IntegrationHyperbolicPower

private theorem zpow_succ_nonneg (A : ℝ) (k : ℤ) (h : 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  lift k to ℕ using h
  rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, pow_succ]

theorem sinhPower_real : IntegrationNum1.rubi6113r11Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" IntegrationNum1.rubi6113r11Nondeg.conditions
    IntegrationNum1.rubi6113r11Nondeg.body IntegrationNum1.rubi6113r11Nondeg.result IntegrationNum1.rubi6113r11Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hEq : env "b" * env "e" + (-1 * 2 * env "c" * env "d") = 0 := by
    have h := hcond (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e"))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hN : (2 : ℝ) * env "c" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [IntegrationNum1.rubi6113r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hgt : 1 < env "m" := by
    have h := hcond (.gt (.var "m") (.int 1)) (by simp [IntegrationNum1.rubi6113r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r11Nondeg, Defined, eval, Interp.real, Function.update, hk] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have hk2 : 2 ≤ k := by
    rw [hm] at hgt
    have h : (1 : ℤ) < k := by exact_mod_cast hgt
    omega
  have hk1 : intValue? (env "m" + (-1 : ℝ)) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkm2 : intValue? (env "m" + (-2 : ℝ)) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hc : env "c" ≠ 0 := (mul_ne_zero_iff.mp hN).2
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards with w
    simp [Defined, eval, Interp.real, Function.update, h2, hkm2]
    omega
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [IntegrationNum1.rubi6113r11Nondeg, Defined, eval, recEnv, Interp.real, h2, hm1, hk1, hN]
      omega
    · have hU : HasDerivAt (fun w : ℝ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℝ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k-1) (env "d" + env "e"*t) (Or.inr (by omega))).comp t hU
      have hT := (Real.hasDerivAt_cosh _).comp t hQ
      have hfun : (fun w => eval Interp.real (recEnv env (IntegrationNum1.rubi6113r11Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r11Nondeg.result) =
        (fun w : ℝ => env "e" * (env "d" + env "e"*w)^(k-1) * Real.cosh (env "a" + env "b"*w + env "c"*w^2) * (2*env "c")⁻¹ +
          (-env "e"^2 * (env "m"-1) * (2*env "c")⁻¹) * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r11Nondeg, eval, recEnv, Interp.real, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Interp.real, Function.update, h2, hkm2] at hΦ
      refine ((((hP.const_mul _).mul hT).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r11Nondeg, eval, Interp.real, Function.update, h2, hk]
      have hpow1 := zpow_succ_nonneg (env "d"+env "e"*t) (k-1) (by omega)
      have hpow2 := zpow_succ_nonneg (env "d"+env "e"*t) (k-2) (by omega)
      rw [show k - 1 + 1 = k by omega] at hpow1
      rw [show k - 2 + 1 = k - 1 by omega] at hpow2
      simp_rw [hpow1, hpow2]
      simp only [sub_sub]
      rw [hm]
      field_simp [hc]
      norm_num only
      linear_combination ((env "d" + env "e"*t) *
        (env "d" + env "e"*t)^(k-2) *
        Real.sinh (env "a" + t*env "b" + t^2*env "c")) * hEq

theorem coshPower_real : IntegrationNum1.rubi6113r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" IntegrationNum1.rubi6113r12Nondeg.conditions
    IntegrationNum1.rubi6113r12Nondeg.body IntegrationNum1.rubi6113r12Nondeg.result IntegrationNum1.rubi6113r12Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hEq : env "b" * env "e" + (-1 * 2 * env "c" * env "d") = 0 := by
    have h := hcond (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e"))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r12Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hN : (2 : ℝ) * env "c" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [IntegrationNum1.rubi6113r12Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hgt : 1 < env "m" := by
    have h := hcond (.gt (.var "m") (.int 1)) (by simp [IntegrationNum1.rubi6113r12Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r12Nondeg, Defined, eval, Interp.real, Function.update, hk] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have hk2 : 2 ≤ k := by
    rw [hm] at hgt
    have h : (1 : ℤ) < k := by exact_mod_cast hgt
    omega
  have hk1 : intValue? (env "m" + (-1 : ℝ)) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkm2 : intValue? (env "m" + (-2 : ℝ)) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hc : env "c" ≠ 0 := (mul_ne_zero_iff.mp hN).2
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards with w
    simp [Defined, eval, Interp.real, Function.update, h2, hkm2]
    omega
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [IntegrationNum1.rubi6113r12Nondeg, Defined, eval, recEnv, Interp.real, h2, hm1, hk1, hN]
      omega
    · have hU : HasDerivAt (fun w : ℝ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℝ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k-1) (env "d" + env "e"*t) (Or.inr (by omega))).comp t hU
      have hT := (Real.hasDerivAt_sinh _).comp t hQ
      have hfun : (fun w => eval Interp.real (recEnv env (IntegrationNum1.rubi6113r12Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r12Nondeg.result) =
        (fun w : ℝ => env "e" * (env "d" + env "e"*w)^(k-1) * Real.sinh (env "a" + env "b"*w + env "c"*w^2) * (2*env "c")⁻¹ +
          (-env "e"^2 * (env "m"-1) * (2*env "c")⁻¹) * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r12Nondeg, eval, recEnv, Interp.real, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Interp.real, Function.update, h2, hkm2] at hΦ
      refine ((((hP.const_mul _).mul hT).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r12Nondeg, eval, Interp.real, Function.update, h2, hk]
      have hpow1 := zpow_succ_nonneg (env "d"+env "e"*t) (k-1) (by omega)
      have hpow2 := zpow_succ_nonneg (env "d"+env "e"*t) (k-2) (by omega)
      rw [show k - 1 + 1 = k by omega] at hpow1
      rw [show k - 2 + 1 = k - 1 by omega] at hpow2
      simp_rw [hpow1, hpow2]
      simp only [sub_sub]
      rw [hm]
      field_simp [hc]
      norm_num only
      linear_combination ((env "d" + env "e"*t) *
        (env "d" + env "e"*t)^(k-2) *
        Real.cosh (env "a" + t*env "b" + t^2*env "c")) * hEq

theorem sinhPowerTwo_real : IntegrationNum1.rubi6113r13Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" IntegrationNum1.rubi6113r13Nondeg.conditions
    IntegrationNum1.rubi6113r13Nondeg.body IntegrationNum1.rubi6113r13Nondeg.result IntegrationNum1.rubi6113r13Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN : (2 : ℝ) * env "c" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [IntegrationNum1.rubi6113r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hgt : 1 < env "m" := by
    have h := hcond (.gt (.var "m") (.int 1)) (by simp [IntegrationNum1.rubi6113r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r13Nondeg, Defined, eval, Interp.real, Function.update, hk] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have hk2 : 2 ≤ k := by
    rw [hm] at hgt
    have h : (1 : ℤ) < k := by exact_mod_cast hgt
    omega
  have hk1 : intValue? (env "m" + (-1 : ℝ)) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkm2 : intValue? (env "m" + (-2 : ℝ)) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hc : env "c" ≠ 0 := (mul_ne_zero_iff.mp hN).2
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards with w <;>
      simp [Defined, eval, Interp.real, Function.update, h2, hk1, hkm2] <;> omega
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [IntegrationNum1.rubi6113r13Nondeg, Defined, eval, recEnv, Interp.real, h2, hm1, hk1, hN]
      omega
    · have hU : HasDerivAt (fun w : ℝ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℝ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k-1) (env "d" + env "e"*t) (Or.inr (by omega))).comp t hU
      have hT := (Real.hasDerivAt_cosh _).comp t hQ
      have hfun : (fun w => eval Interp.real (recEnv env (IntegrationNum1.rubi6113r13Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r13Nondeg.result) =
        (fun w : ℝ => env "e" * (env "d" + env "e"*w)^(k-1) * Real.cosh (env "a" + env "b"*w + env "c"*w^2) * (2*env "c")⁻¹ +
          (-(env "b"*env "e" - 2*env "c"*env "d") * (2*env "c")⁻¹) * Φ "I1" w +
          (-env "e"^2 * (env "m"-1) * (2*env "c")⁻¹) * Φ "I2" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r13Nondeg, eval, recEnv, Interp.real, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Interp.real, Function.update, h2, hk1] at hΦ1
      simp [eval, Interp.real, Function.update, h2, hkm2] at hΦ2
      refine (((((hP.const_mul _).mul hT).mul_const _).add (hΦ1.const_mul _)).add (hΦ2.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r13Nondeg, eval, Interp.real, Function.update, h2, hk]
      have hpow1 := zpow_succ_nonneg (env "d"+env "e"*t) (k-1) (by omega)
      have hpow2 := zpow_succ_nonneg (env "d"+env "e"*t) (k-2) (by omega)
      rw [show k - 1 + 1 = k by omega] at hpow1
      rw [show k - 2 + 1 = k - 1 by omega] at hpow2
      simp_rw [hpow1, hpow2]
      simp only [sub_sub]
      rw [hm]
      field_simp [hc]
      norm_num only
      ring

theorem coshPowerTwo_real : IntegrationNum1.rubi6113r14Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" IntegrationNum1.rubi6113r14Nondeg.conditions
    IntegrationNum1.rubi6113r14Nondeg.body IntegrationNum1.rubi6113r14Nondeg.result IntegrationNum1.rubi6113r14Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN : (2 : ℝ) * env "c" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [IntegrationNum1.rubi6113r14Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hgt : 1 < env "m" := by
    have h := hcond (.gt (.var "m") (.int 1)) (by simp [IntegrationNum1.rubi6113r14Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r14Nondeg, Defined, eval, Interp.real, Function.update, hk] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have hk2 : 2 ≤ k := by
    rw [hm] at hgt
    have h : (1 : ℤ) < k := by exact_mod_cast hgt
    omega
  have hk1 : intValue? (env "m" + (-1 : ℝ)) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkm2 : intValue? (env "m" + (-2 : ℝ)) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hc : env "c" ≠ 0 := (mul_ne_zero_iff.mp hN).2
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards with w <;>
      simp [Defined, eval, Interp.real, Function.update, h2, hk1, hkm2] <;> omega
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [IntegrationNum1.rubi6113r14Nondeg, Defined, eval, recEnv, Interp.real, h2, hm1, hk1, hN]
      omega
    · have hU : HasDerivAt (fun w : ℝ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℝ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k-1) (env "d" + env "e"*t) (Or.inr (by omega))).comp t hU
      have hT := (Real.hasDerivAt_sinh _).comp t hQ
      have hfun : (fun w => eval Interp.real (recEnv env (IntegrationNum1.rubi6113r14Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r14Nondeg.result) =
        (fun w : ℝ => env "e" * (env "d" + env "e"*w)^(k-1) * Real.sinh (env "a" + env "b"*w + env "c"*w^2) * (2*env "c")⁻¹ +
          (-(env "b"*env "e" - 2*env "c"*env "d") * (2*env "c")⁻¹) * Φ "I1" w +
          (-env "e"^2 * (env "m"-1) * (2*env "c")⁻¹) * Φ "I2" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r14Nondeg, eval, recEnv, Interp.real, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Interp.real, Function.update, h2, hk1] at hΦ1
      simp [eval, Interp.real, Function.update, h2, hkm2] at hΦ2
      refine (((((hP.const_mul _).mul hT).mul_const _).add (hΦ1.const_mul _)).add (hΦ2.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r14Nondeg, eval, Interp.real, Function.update, h2, hk]
      have hpow1 := zpow_succ_nonneg (env "d"+env "e"*t) (k-1) (by omega)
      have hpow2 := zpow_succ_nonneg (env "d"+env "e"*t) (k-2) (by omega)
      rw [show k - 1 + 1 = k by omega] at hpow1
      rw [show k - 2 + 1 = k - 1 by omega] at hpow2
      simp_rw [hpow1, hpow2]
      simp only [sub_sub]
      rw [hm]
      field_simp [hc]
      norm_num only
      ring

private theorem zpow_succ_nonneg_complex (A : ℂ) (k : ℤ) (h : 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  lift k to ℕ using h
  rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, pow_succ]

theorem sinhPower_complex : IntegrationNum1.rubi6113r11Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" IntegrationNum1.rubi6113r11Nondeg.conditions
    IntegrationNum1.rubi6113r11Nondeg.body IntegrationNum1.rubi6113r11Nondeg.result IntegrationNum1.rubi6113r11Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hEq : env "b" * env "e" + (-1 * 2 * env "c" * env "d") = 0 := by
    have h := hcond (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e"))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex] using h
  have hN : (2 : ℂ) * env "c" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [IntegrationNum1.rubi6113r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex] using h
  have hgt : 1 < (env "m").re := by
    have h := hcond (.gt (.var "m") (.int 1)) (by simp [IntegrationNum1.rubi6113r11Nondeg])
    have hh : (env "m").im = 0 ∧ 1 < (env "m").re := by
      simpa [Cond.Holds, Defined, eval, Interp.complex] using h
    exact hh.2
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r11Nondeg, Defined, eval, Interp.complex, Function.update, hk] at h
  have hm : env "m" = (k : ℂ) := (intValue?_eq _ _).1 hk
  have hk2 : 2 ≤ k := by
    rw [hm] at hgt
    simp only [Complex.intCast_re] at hgt
    have h : (1 : ℤ) < k := by exact_mod_cast hgt
    omega
  have hk1 : intValue? (env "m" + (-1 : ℂ)) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkm2 : intValue? (env "m" + (-2 : ℂ)) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hc : env "c" ≠ 0 := (mul_ne_zero_iff.mp hN).2
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards with w
    simp [Defined, eval, Interp.complex, Function.update, h2, hkm2]
    omega
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [IntegrationNum1.rubi6113r11Nondeg, Defined, eval, recEnv, Interp.complex, h2, hm1, hk1, hN]
      omega
    · have hU : HasDerivAt (fun w : ℂ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℂ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k-1) (env "d" + env "e"*t) (Or.inr (by omega))).comp t hU
      have hT := (Complex.hasDerivAt_cosh _).comp t hQ
      have hfun : (fun w => eval Interp.complex (recEnv env (IntegrationNum1.rubi6113r11Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r11Nondeg.result) =
        (fun w : ℂ => env "e" * (env "d" + env "e"*w)^(k-1) * Complex.cosh (env "a" + env "b"*w + env "c"*w^2) * (2*env "c")⁻¹ +
          (-env "e"^2 * (env "m"-1) * (2*env "c")⁻¹) * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r11Nondeg, eval, recEnv, Interp.complex, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Interp.complex, Function.update, h2, hkm2] at hΦ
      refine ((((hP.const_mul _).mul hT).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r11Nondeg, eval, Interp.complex, Function.update, h2, hk]
      have hpow1 := zpow_succ_nonneg_complex (env "d"+env "e"*t) (k-1) (by omega)
      have hpow2 := zpow_succ_nonneg_complex (env "d"+env "e"*t) (k-2) (by omega)
      rw [show k - 1 + 1 = k by omega] at hpow1
      rw [show k - 2 + 1 = k - 1 by omega] at hpow2
      simp_rw [hpow1, hpow2]
      simp only [sub_sub]
      rw [hm]
      field_simp [hc]
      norm_num only
      linear_combination ((env "d" + env "e"*t) *
        (env "d" + env "e"*t)^(k-2) *
        Complex.sinh (env "a" + t*env "b" + t^2*env "c")) * hEq

theorem coshPower_complex : IntegrationNum1.rubi6113r12Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" IntegrationNum1.rubi6113r12Nondeg.conditions
    IntegrationNum1.rubi6113r12Nondeg.body IntegrationNum1.rubi6113r12Nondeg.result IntegrationNum1.rubi6113r12Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hEq : env "b" * env "e" + (-1 * 2 * env "c" * env "d") = 0 := by
    have h := hcond (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e"))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r12Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex] using h
  have hN : (2 : ℂ) * env "c" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [IntegrationNum1.rubi6113r12Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex] using h
  have hgt : 1 < (env "m").re := by
    have h := hcond (.gt (.var "m") (.int 1)) (by simp [IntegrationNum1.rubi6113r12Nondeg])
    have hh : (env "m").im = 0 ∧ 1 < (env "m").re := by
      simpa [Cond.Holds, Defined, eval, Interp.complex] using h
    exact hh.2
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r12Nondeg, Defined, eval, Interp.complex, Function.update, hk] at h
  have hm : env "m" = (k : ℂ) := (intValue?_eq _ _).1 hk
  have hk2 : 2 ≤ k := by
    rw [hm] at hgt
    simp only [Complex.intCast_re] at hgt
    have h : (1 : ℤ) < k := by exact_mod_cast hgt
    omega
  have hk1 : intValue? (env "m" + (-1 : ℂ)) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkm2 : intValue? (env "m" + (-2 : ℂ)) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hc : env "c" ≠ 0 := (mul_ne_zero_iff.mp hN).2
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards with w
    simp [Defined, eval, Interp.complex, Function.update, h2, hkm2]
    omega
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [IntegrationNum1.rubi6113r12Nondeg, Defined, eval, recEnv, Interp.complex, h2, hm1, hk1, hN]
      omega
    · have hU : HasDerivAt (fun w : ℂ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℂ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k-1) (env "d" + env "e"*t) (Or.inr (by omega))).comp t hU
      have hT := (Complex.hasDerivAt_sinh _).comp t hQ
      have hfun : (fun w => eval Interp.complex (recEnv env (IntegrationNum1.rubi6113r12Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r12Nondeg.result) =
        (fun w : ℂ => env "e" * (env "d" + env "e"*w)^(k-1) * Complex.sinh (env "a" + env "b"*w + env "c"*w^2) * (2*env "c")⁻¹ +
          (-env "e"^2 * (env "m"-1) * (2*env "c")⁻¹) * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r12Nondeg, eval, recEnv, Interp.complex, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Interp.complex, Function.update, h2, hkm2] at hΦ
      refine ((((hP.const_mul _).mul hT).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r12Nondeg, eval, Interp.complex, Function.update, h2, hk]
      have hpow1 := zpow_succ_nonneg_complex (env "d"+env "e"*t) (k-1) (by omega)
      have hpow2 := zpow_succ_nonneg_complex (env "d"+env "e"*t) (k-2) (by omega)
      rw [show k - 1 + 1 = k by omega] at hpow1
      rw [show k - 2 + 1 = k - 1 by omega] at hpow2
      simp_rw [hpow1, hpow2]
      simp only [sub_sub]
      rw [hm]
      field_simp [hc]
      norm_num only
      linear_combination ((env "d" + env "e"*t) *
        (env "d" + env "e"*t)^(k-2) *
        Complex.cosh (env "a" + t*env "b" + t^2*env "c")) * hEq

theorem sinhPowerTwo_complex : IntegrationNum1.rubi6113r13Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" IntegrationNum1.rubi6113r13Nondeg.conditions
    IntegrationNum1.rubi6113r13Nondeg.body IntegrationNum1.rubi6113r13Nondeg.result IntegrationNum1.rubi6113r13Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN : (2 : ℂ) * env "c" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [IntegrationNum1.rubi6113r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex] using h
  have hgt : 1 < (env "m").re := by
    have h := hcond (.gt (.var "m") (.int 1)) (by simp [IntegrationNum1.rubi6113r13Nondeg])
    have hh : (env "m").im = 0 ∧ 1 < (env "m").re := by
      simpa [Cond.Holds, Defined, eval, Interp.complex] using h
    exact hh.2
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r13Nondeg, Defined, eval, Interp.complex, Function.update, hk] at h
  have hm : env "m" = (k : ℂ) := (intValue?_eq _ _).1 hk
  have hk2 : 2 ≤ k := by
    rw [hm] at hgt
    simp only [Complex.intCast_re] at hgt
    have h : (1 : ℤ) < k := by exact_mod_cast hgt
    omega
  have hk1 : intValue? (env "m" + (-1 : ℂ)) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkm2 : intValue? (env "m" + (-2 : ℂ)) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hc : env "c" ≠ 0 := (mul_ne_zero_iff.mp hN).2
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards with w <;>
      simp [Defined, eval, Interp.complex, Function.update, h2, hk1, hkm2] <;> omega
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [IntegrationNum1.rubi6113r13Nondeg, Defined, eval, recEnv, Interp.complex, h2, hm1, hk1, hN]
      omega
    · have hU : HasDerivAt (fun w : ℂ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℂ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k-1) (env "d" + env "e"*t) (Or.inr (by omega))).comp t hU
      have hT := (Complex.hasDerivAt_cosh _).comp t hQ
      have hfun : (fun w => eval Interp.complex (recEnv env (IntegrationNum1.rubi6113r13Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r13Nondeg.result) =
        (fun w : ℂ => env "e" * (env "d" + env "e"*w)^(k-1) * Complex.cosh (env "a" + env "b"*w + env "c"*w^2) * (2*env "c")⁻¹ +
          (-(env "b"*env "e" - 2*env "c"*env "d") * (2*env "c")⁻¹) * Φ "I1" w +
          (-env "e"^2 * (env "m"-1) * (2*env "c")⁻¹) * Φ "I2" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r13Nondeg, eval, recEnv, Interp.complex, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Interp.complex, Function.update, h2, hk1] at hΦ1
      simp [eval, Interp.complex, Function.update, h2, hkm2] at hΦ2
      refine (((((hP.const_mul _).mul hT).mul_const _).add (hΦ1.const_mul _)).add (hΦ2.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r13Nondeg, eval, Interp.complex, Function.update, h2, hk]
      have hpow1 := zpow_succ_nonneg_complex (env "d"+env "e"*t) (k-1) (by omega)
      have hpow2 := zpow_succ_nonneg_complex (env "d"+env "e"*t) (k-2) (by omega)
      rw [show k - 1 + 1 = k by omega] at hpow1
      rw [show k - 2 + 1 = k - 1 by omega] at hpow2
      simp_rw [hpow1, hpow2]
      simp only [sub_sub]
      rw [hm]
      field_simp [hc]
      norm_num only
      ring

theorem coshPowerTwo_complex : IntegrationNum1.rubi6113r14Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" IntegrationNum1.rubi6113r14Nondeg.conditions
    IntegrationNum1.rubi6113r14Nondeg.body IntegrationNum1.rubi6113r14Nondeg.result IntegrationNum1.rubi6113r14Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN : (2 : ℂ) * env "c" ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [IntegrationNum1.rubi6113r14Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex] using h
  have hgt : 1 < (env "m").re := by
    have h := hcond (.gt (.var "m") (.int 1)) (by simp [IntegrationNum1.rubi6113r14Nondeg])
    have hh : (env "m").im = 0 ∧ 1 < (env "m").re := by
      simpa [Cond.Holds, Defined, eval, Interp.complex] using h
    exact hh.2
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r14Nondeg, Defined, eval, Interp.complex, Function.update, hk] at h
  have hm : env "m" = (k : ℂ) := (intValue?_eq _ _).1 hk
  have hk2 : 2 ≤ k := by
    rw [hm] at hgt
    simp only [Complex.intCast_re] at hgt
    have h : (1 : ℤ) < k := by exact_mod_cast hgt
    omega
  have hk1 : intValue? (env "m" + (-1 : ℂ)) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkm2 : intValue? (env "m" + (-2 : ℂ)) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hc : env "c" ≠ 0 := (mul_ne_zero_iff.mp hN).2
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards with w <;>
      simp [Defined, eval, Interp.complex, Function.update, h2, hk1, hkm2] <;> omega
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [IntegrationNum1.rubi6113r14Nondeg, Defined, eval, recEnv, Interp.complex, h2, hm1, hk1, hN]
      omega
    · have hU : HasDerivAt (fun w : ℂ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℂ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k-1) (env "d" + env "e"*t) (Or.inr (by omega))).comp t hU
      have hT := (Complex.hasDerivAt_sinh _).comp t hQ
      have hfun : (fun w => eval Interp.complex (recEnv env (IntegrationNum1.rubi6113r14Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r14Nondeg.result) =
        (fun w : ℂ => env "e" * (env "d" + env "e"*w)^(k-1) * Complex.sinh (env "a" + env "b"*w + env "c"*w^2) * (2*env "c")⁻¹ +
          (-(env "b"*env "e" - 2*env "c"*env "d") * (2*env "c")⁻¹) * Φ "I1" w +
          (-env "e"^2 * (env "m"-1) * (2*env "c")⁻¹) * Φ "I2" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r14Nondeg, eval, recEnv, Interp.complex, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Interp.complex, Function.update, h2, hk1] at hΦ1
      simp [eval, Interp.complex, Function.update, h2, hkm2] at hΦ2
      refine (((((hP.const_mul _).mul hT).mul_const _).add (hΦ1.const_mul _)).add (hΦ2.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r14Nondeg, eval, Interp.complex, Function.update, h2, hk]
      have hpow1 := zpow_succ_nonneg_complex (env "d"+env "e"*t) (k-1) (by omega)
      have hpow2 := zpow_succ_nonneg_complex (env "d"+env "e"*t) (k-2) (by omega)
      rw [show k - 1 + 1 = k by omega] at hpow1
      rw [show k - 2 + 1 = k - 1 by omega] at hpow2
      simp_rw [hpow1, hpow2]
      simp only [sub_sub]
      rw [hm]
      field_simp [hc]
      norm_num only
      ring

theorem sinhNegative_real : IntegrationNum1.rubi6113r15Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" IntegrationNum1.rubi6113r15Nondeg.conditions
    IntegrationNum1.rubi6113r15Nondeg.body IntegrationNum1.rubi6113r15Nondeg.result IntegrationNum1.rubi6113r15Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hEq : env "b" * env "e" + (-1 * 2 * env "c" * env "d") = 0 := by
    have h := hcond (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e"))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r15Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hN : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r15Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have he : env "e" ≠ 0 := (mul_ne_zero_iff.mp hN).1
  have hM : env "m" + 1 ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have hN2 : env "e" ^ 2 * (env "m" + 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 he) hM
  have hlt : env "m" < -1 := by
    have h := hcond (.gt (.int (-1)) (.var "m")) (by simp [IntegrationNum1.rubi6113r15Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r15Nondeg, Defined, eval, Interp.real, Function.update, hk] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have hkneg : k < 0 := by
    rw [hm] at hlt
    have h : k < (-1 : ℤ) := by exact_mod_cast hlt
    omega
  have hk1 : intValue? (env "m" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hk2 : intValue? (env "m" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hbase : ∀ᶠ w in 𝓝 t, env "d" + env "e" * w ≠ 0 := by
    filter_upwards [hF] with w hw
    simp [IntegrationNum1.rubi6113r15Nondeg, Defined, eval, Interp.real, Function.update, hk, h2] at hw
    exact hw hkneg
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards [hbase] with w hw
    simp [Defined, eval, Interp.real, Function.update, h2, hk2, hw]
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [hbase] with w hw
      simp [IntegrationNum1.rubi6113r15Nondeg, Defined, eval, recEnv, Interp.real, h2, hm1, hk1, hN, hN2, hw]
    · have hz := hbase.self_of_nhds
      have hU : HasDerivAt (fun w : ℝ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℝ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k+1) (env "d" + env "e"*t) (Or.inl hz)).comp t hU
      have hT := (Real.hasDerivAt_sinh _).comp t hQ
      have hfun : (fun w => eval Interp.real (recEnv env (IntegrationNum1.rubi6113r15Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r15Nondeg.result) =
        (fun w : ℝ => (env "d" + env "e"*w)^(k+1) * Real.sinh (env "a" + env "b"*w + env "c"*w^2) * (env "e"*(env "m"+1))⁻¹ +
          (-2*env "c" * (env "e"^2*(env "m"+1))⁻¹) * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r15Nondeg, eval, recEnv, Interp.real, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      rw [hfun]
      simp [eval, Interp.real, Function.update, h2, hk2] at hΦ
      refine (((hP.mul hT).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r15Nondeg, eval, Interp.real, Function.update, h2, hk]
      have hpow1 := zpow_add_one₀ hz k
      have hpow2 := zpow_add_one₀ hz (k+1)
      rw [show k + 1 + 1 = k + 2 by omega] at hpow2
      simp_rw [hpow2, hpow1]
      have hM' : (k : ℝ) + 1 ≠ 0 := by simpa [hm] using hM
      rw [hm]
      generalize (env "d"+env "e"*t)^k = P
      generalize Real.sinh (env "a"+env "b"*t+env "c"*t^2) = S
      generalize Real.cosh (env "a"+env "b"*t+env "c"*t^2) = C
      field_simp [he, hM']
      linear_combination (P * (env "d"+env "e"*t) * C) * hEq

theorem coshNegative_real : IntegrationNum1.rubi6113r16Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" IntegrationNum1.rubi6113r16Nondeg.conditions
    IntegrationNum1.rubi6113r16Nondeg.body IntegrationNum1.rubi6113r16Nondeg.result IntegrationNum1.rubi6113r16Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hEq : env "b" * env "e" + (-1 * 2 * env "c" * env "d") = 0 := by
    have h := hcond (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e"))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r16Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hN : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r16Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have he : env "e" ≠ 0 := (mul_ne_zero_iff.mp hN).1
  have hM : env "m" + 1 ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have hN2 : env "e" ^ 2 * (env "m" + 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 he) hM
  have hlt : env "m" < -1 := by
    have h := hcond (.gt (.int (-1)) (.var "m")) (by simp [IntegrationNum1.rubi6113r16Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r16Nondeg, Defined, eval, Interp.real, Function.update, hk] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have hkneg : k < 0 := by
    rw [hm] at hlt
    have h : k < (-1 : ℤ) := by exact_mod_cast hlt
    omega
  have hk1 : intValue? (env "m" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hk2 : intValue? (env "m" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hbase : ∀ᶠ w in 𝓝 t, env "d" + env "e" * w ≠ 0 := by
    filter_upwards [hF] with w hw
    simp [IntegrationNum1.rubi6113r16Nondeg, Defined, eval, Interp.real, Function.update, hk, h2] at hw
    exact hw hkneg
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards [hbase] with w hw
    simp [Defined, eval, Interp.real, Function.update, h2, hk2, hw]
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [hbase] with w hw
      simp [IntegrationNum1.rubi6113r16Nondeg, Defined, eval, recEnv, Interp.real, h2, hm1, hk1, hN, hN2, hw]
    · have hz := hbase.self_of_nhds
      have hU : HasDerivAt (fun w : ℝ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℝ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k+1) (env "d" + env "e"*t) (Or.inl hz)).comp t hU
      have hT := (Real.hasDerivAt_cosh _).comp t hQ
      have hfun : (fun w => eval Interp.real (recEnv env (IntegrationNum1.rubi6113r16Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r16Nondeg.result) =
        (fun w : ℝ => (env "d" + env "e"*w)^(k+1) * Real.cosh (env "a" + env "b"*w + env "c"*w^2) * (env "e"*(env "m"+1))⁻¹ +
          (-2*env "c" * (env "e"^2*(env "m"+1))⁻¹) * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r16Nondeg, eval, recEnv, Interp.real, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      rw [hfun]
      simp [eval, Interp.real, Function.update, h2, hk2] at hΦ
      refine (((hP.mul hT).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r16Nondeg, eval, Interp.real, Function.update, h2, hk]
      have hpow1 := zpow_add_one₀ hz k
      have hpow2 := zpow_add_one₀ hz (k+1)
      rw [show k + 1 + 1 = k + 2 by omega] at hpow2
      simp_rw [hpow2, hpow1]
      have hM' : (k : ℝ) + 1 ≠ 0 := by simpa [hm] using hM
      rw [hm]
      generalize (env "d"+env "e"*t)^k = P
      generalize Real.sinh (env "a"+env "b"*t+env "c"*t^2) = S
      generalize Real.cosh (env "a"+env "b"*t+env "c"*t^2) = C
      field_simp [he, hM']
      linear_combination (P * (env "d"+env "e"*t) * S) * hEq

theorem sinhNegativeTwo_real : IntegrationNum1.rubi6113r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" IntegrationNum1.rubi6113r17Nondeg.conditions
    IntegrationNum1.rubi6113r17Nondeg.body IntegrationNum1.rubi6113r17Nondeg.result IntegrationNum1.rubi6113r17Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r17Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have he : env "e" ≠ 0 := (mul_ne_zero_iff.mp hN).1
  have hM : env "m" + 1 ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have hN2 : env "e" ^ 2 * (env "m" + 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 he) hM
  have hlt : env "m" < -1 := by
    have h := hcond (.gt (.int (-1)) (.var "m")) (by simp [IntegrationNum1.rubi6113r17Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r17Nondeg, Defined, eval, Interp.real, Function.update, hk] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have hkneg : k < 0 := by
    rw [hm] at hlt
    have h : k < (-1 : ℤ) := by exact_mod_cast hlt
    omega
  have hk1 : intValue? (env "m" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hk2 : intValue? (env "m" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hbase : ∀ᶠ w in 𝓝 t, env "d" + env "e" * w ≠ 0 := by
    filter_upwards [hF] with w hw
    simp [IntegrationNum1.rubi6113r17Nondeg, Defined, eval, Interp.real, Function.update, hk, h2] at hw
    exact hw hkneg
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hbase] with w hw <;>
      simp [Defined, eval, Interp.real, Function.update, h2, hk1, hk2, hw]
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [hbase] with w hw
      simp [IntegrationNum1.rubi6113r17Nondeg, Defined, eval, recEnv, Interp.real, h2, hm1, hk1, hN, hN2, hw]
    · have hz := hbase.self_of_nhds
      have hU : HasDerivAt (fun w : ℝ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℝ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k+1) (env "d" + env "e"*t) (Or.inl hz)).comp t hU
      have hT := (Real.hasDerivAt_sinh _).comp t hQ
      have hfun : (fun w => eval Interp.real (recEnv env (IntegrationNum1.rubi6113r17Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r17Nondeg.result) =
        (fun w : ℝ => (env "d" + env "e"*w)^(k+1) * Real.sinh (env "a" + env "b"*w + env "c"*w^2) * (env "e"*(env "m"+1))⁻¹ +
          (-(env "b"*env "e"-2*env "c"*env "d") * (env "e"^2*(env "m"+1))⁻¹) * Φ "I1" w +
          (-2*env "c" * (env "e"^2*(env "m"+1))⁻¹) * Φ "I2" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r17Nondeg, eval, recEnv, Interp.real, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Interp.real, Function.update, h2, hk1] at hΦ1
      simp [eval, Interp.real, Function.update, h2, hk2] at hΦ2
      refine ((((hP.mul hT).mul_const _).add (hΦ1.const_mul _)).add (hΦ2.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r17Nondeg, eval, Interp.real, Function.update, h2, hk]
      have hpow1 := zpow_add_one₀ hz k
      have hpow2 := zpow_add_one₀ hz (k+1)
      rw [show k + 1 + 1 = k + 2 by omega] at hpow2
      simp_rw [hpow2, hpow1]
      have hM' : (k : ℝ) + 1 ≠ 0 := by simpa [hm] using hM
      rw [hm]
      generalize (env "d"+env "e"*t)^k = P
      generalize Real.sinh (env "a"+env "b"*t+env "c"*t^2) = S
      generalize Real.cosh (env "a"+env "b"*t+env "c"*t^2) = C
      field_simp [he, hM']
      ring

theorem coshNegativeTwo_real : IntegrationNum1.rubi6113r18Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" IntegrationNum1.rubi6113r18Nondeg.conditions
    IntegrationNum1.rubi6113r18Nondeg.body IntegrationNum1.rubi6113r18Nondeg.result IntegrationNum1.rubi6113r18Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r18Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have he : env "e" ≠ 0 := (mul_ne_zero_iff.mp hN).1
  have hM : env "m" + 1 ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have hN2 : env "e" ^ 2 * (env "m" + 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 he) hM
  have hlt : env "m" < -1 := by
    have h := hcond (.gt (.int (-1)) (.var "m")) (by simp [IntegrationNum1.rubi6113r18Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r18Nondeg, Defined, eval, Interp.real, Function.update, hk] at h
  have hm : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have hkneg : k < 0 := by
    rw [hm] at hlt
    have h : k < (-1 : ℤ) := by exact_mod_cast hlt
    omega
  have hk1 : intValue? (env "m" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hk2 : intValue? (env "m" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hbase : ∀ᶠ w in 𝓝 t, env "d" + env "e" * w ≠ 0 := by
    filter_upwards [hF] with w hw
    simp [IntegrationNum1.rubi6113r18Nondeg, Defined, eval, Interp.real, Function.update, hk, h2] at hw
    exact hw hkneg
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hbase] with w hw <;>
      simp [Defined, eval, Interp.real, Function.update, h2, hk1, hk2, hw]
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [hbase] with w hw
      simp [IntegrationNum1.rubi6113r18Nondeg, Defined, eval, recEnv, Interp.real, h2, hm1, hk1, hN, hN2, hw]
    · have hz := hbase.self_of_nhds
      have hU : HasDerivAt (fun w : ℝ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℝ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k+1) (env "d" + env "e"*t) (Or.inl hz)).comp t hU
      have hT := (Real.hasDerivAt_cosh _).comp t hQ
      have hfun : (fun w => eval Interp.real (recEnv env (IntegrationNum1.rubi6113r18Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r18Nondeg.result) =
        (fun w : ℝ => (env "d" + env "e"*w)^(k+1) * Real.cosh (env "a" + env "b"*w + env "c"*w^2) * (env "e"*(env "m"+1))⁻¹ +
          (-(env "b"*env "e"-2*env "c"*env "d") * (env "e"^2*(env "m"+1))⁻¹) * Φ "I1" w +
          (-2*env "c" * (env "e"^2*(env "m"+1))⁻¹) * Φ "I2" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r18Nondeg, eval, recEnv, Interp.real, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Interp.real, Function.update, h2, hk1] at hΦ1
      simp [eval, Interp.real, Function.update, h2, hk2] at hΦ2
      refine ((((hP.mul hT).mul_const _).add (hΦ1.const_mul _)).add (hΦ2.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r18Nondeg, eval, Interp.real, Function.update, h2, hk]
      have hpow1 := zpow_add_one₀ hz k
      have hpow2 := zpow_add_one₀ hz (k+1)
      rw [show k + 1 + 1 = k + 2 by omega] at hpow2
      simp_rw [hpow2, hpow1]
      have hM' : (k : ℝ) + 1 ≠ 0 := by simpa [hm] using hM
      rw [hm]
      generalize (env "d"+env "e"*t)^k = P
      generalize Real.sinh (env "a"+env "b"*t+env "c"*t^2) = S
      generalize Real.cosh (env "a"+env "b"*t+env "c"*t^2) = C
      field_simp [he, hM']
      ring

theorem sinhNegative_complex : IntegrationNum1.rubi6113r15Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" IntegrationNum1.rubi6113r15Nondeg.conditions
    IntegrationNum1.rubi6113r15Nondeg.body IntegrationNum1.rubi6113r15Nondeg.result IntegrationNum1.rubi6113r15Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hEq : env "b" * env "e" + (-1 * 2 * env "c" * env "d") = 0 := by
    have h := hcond (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e"))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r15Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex] using h
  have hN : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r15Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex] using h
  have he : env "e" ≠ 0 := (mul_ne_zero_iff.mp hN).1
  have hM : env "m" + 1 ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have hN2 : env "e" ^ 2 * (env "m" + 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 he) hM
  have hlt : (env "m").re < -1 := by
    have h := hcond (.gt (.int (-1)) (.var "m")) (by simp [IntegrationNum1.rubi6113r15Nondeg])
    have hh : (env "m").im = 0 ∧ (env "m").re < -1 := by
      simpa [Cond.Holds, Defined, eval, Interp.complex] using h
    exact hh.2
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r15Nondeg, Defined, eval, Interp.complex, Function.update, hk] at h
  have hm : env "m" = (k : ℂ) := (intValue?_eq _ _).1 hk
  have hkneg : k < 0 := by
    rw [hm] at hlt
    simp only [Complex.intCast_re] at hlt
    have h : k < (-1 : ℤ) := by exact_mod_cast hlt
    omega
  have hk1 : intValue? (env "m" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hk2 : intValue? (env "m" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hbase : ∀ᶠ w in 𝓝 t, env "d" + env "e" * w ≠ 0 := by
    filter_upwards [hF] with w hw
    simp [IntegrationNum1.rubi6113r15Nondeg, Defined, eval, Interp.complex, Function.update, hk, h2] at hw
    exact hw hkneg
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards [hbase] with w hw
    simp [Defined, eval, Interp.complex, Function.update, h2, hk2, hw]
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [hbase] with w hw
      simp [IntegrationNum1.rubi6113r15Nondeg, Defined, eval, recEnv, Interp.complex, h2, hm1, hk1, hN, hN2, hw]
    · have hz := hbase.self_of_nhds
      have hU : HasDerivAt (fun w : ℂ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℂ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k+1) (env "d" + env "e"*t) (Or.inl hz)).comp t hU
      have hT := (Complex.hasDerivAt_sinh _).comp t hQ
      have hfun : (fun w => eval Interp.complex (recEnv env (IntegrationNum1.rubi6113r15Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r15Nondeg.result) =
        (fun w : ℂ => (env "d" + env "e"*w)^(k+1) * Complex.sinh (env "a" + env "b"*w + env "c"*w^2) * (env "e"*(env "m"+1))⁻¹ +
          (-2*env "c" * (env "e"^2*(env "m"+1))⁻¹) * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r15Nondeg, eval, recEnv, Interp.complex, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      rw [hfun]
      simp [eval, Interp.complex, Function.update, h2, hk2] at hΦ
      refine (((hP.mul hT).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r15Nondeg, eval, Interp.complex, Function.update, h2, hk]
      have hpow1 := zpow_add_one₀ hz k
      have hpow2 := zpow_add_one₀ hz (k+1)
      rw [show k + 1 + 1 = k + 2 by omega] at hpow2
      simp_rw [hpow2, hpow1]
      have hM' : (k : ℂ) + 1 ≠ 0 := by simpa [hm] using hM
      rw [hm]
      generalize (env "d"+env "e"*t)^k = P
      generalize Complex.sinh (env "a"+env "b"*t+env "c"*t^2) = S
      generalize Complex.cosh (env "a"+env "b"*t+env "c"*t^2) = C
      field_simp [he, hM']
      linear_combination (P * (env "d"+env "e"*t) * C) * hEq

theorem coshNegative_complex : IntegrationNum1.rubi6113r16Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" IntegrationNum1.rubi6113r16Nondeg.conditions
    IntegrationNum1.rubi6113r16Nondeg.body IntegrationNum1.rubi6113r16Nondeg.result IntegrationNum1.rubi6113r16Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hEq : env "b" * env "e" + (-1 * 2 * env "c" * env "d") = 0 := by
    have h := hcond (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e"))
      (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r16Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex] using h
  have hN : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r16Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex] using h
  have he : env "e" ≠ 0 := (mul_ne_zero_iff.mp hN).1
  have hM : env "m" + 1 ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have hN2 : env "e" ^ 2 * (env "m" + 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 he) hM
  have hlt : (env "m").re < -1 := by
    have h := hcond (.gt (.int (-1)) (.var "m")) (by simp [IntegrationNum1.rubi6113r16Nondeg])
    have hh : (env "m").im = 0 ∧ (env "m").re < -1 := by
      simpa [Cond.Holds, Defined, eval, Interp.complex] using h
    exact hh.2
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r16Nondeg, Defined, eval, Interp.complex, Function.update, hk] at h
  have hm : env "m" = (k : ℂ) := (intValue?_eq _ _).1 hk
  have hkneg : k < 0 := by
    rw [hm] at hlt
    simp only [Complex.intCast_re] at hlt
    have h : k < (-1 : ℤ) := by exact_mod_cast hlt
    omega
  have hk1 : intValue? (env "m" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hk2 : intValue? (env "m" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hbase : ∀ᶠ w in 𝓝 t, env "d" + env "e" * w ≠ 0 := by
    filter_upwards [hF] with w hw
    simp [IntegrationNum1.rubi6113r16Nondeg, Defined, eval, Interp.complex, Function.update, hk, h2] at hw
    exact hw hkneg
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    filter_upwards [hbase] with w hw
    simp [Defined, eval, Interp.complex, Function.update, h2, hk2, hw]
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [hbase] with w hw
      simp [IntegrationNum1.rubi6113r16Nondeg, Defined, eval, recEnv, Interp.complex, h2, hm1, hk1, hN, hN2, hw]
    · have hz := hbase.self_of_nhds
      have hU : HasDerivAt (fun w : ℂ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℂ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k+1) (env "d" + env "e"*t) (Or.inl hz)).comp t hU
      have hT := (Complex.hasDerivAt_cosh _).comp t hQ
      have hfun : (fun w => eval Interp.complex (recEnv env (IntegrationNum1.rubi6113r16Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r16Nondeg.result) =
        (fun w : ℂ => (env "d" + env "e"*w)^(k+1) * Complex.cosh (env "a" + env "b"*w + env "c"*w^2) * (env "e"*(env "m"+1))⁻¹ +
          (-2*env "c" * (env "e"^2*(env "m"+1))⁻¹) * Φ "I1" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r16Nondeg, eval, recEnv, Interp.complex, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      rw [hfun]
      simp [eval, Interp.complex, Function.update, h2, hk2] at hΦ
      refine (((hP.mul hT).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r16Nondeg, eval, Interp.complex, Function.update, h2, hk]
      have hpow1 := zpow_add_one₀ hz k
      have hpow2 := zpow_add_one₀ hz (k+1)
      rw [show k + 1 + 1 = k + 2 by omega] at hpow2
      simp_rw [hpow2, hpow1]
      have hM' : (k : ℂ) + 1 ≠ 0 := by simpa [hm] using hM
      rw [hm]
      generalize (env "d"+env "e"*t)^k = P
      generalize Complex.sinh (env "a"+env "b"*t+env "c"*t^2) = S
      generalize Complex.cosh (env "a"+env "b"*t+env "c"*t^2) = C
      field_simp [he, hM']
      linear_combination (P * (env "d"+env "e"*t) * S) * hEq

theorem sinhNegativeTwo_complex : IntegrationNum1.rubi6113r17Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" IntegrationNum1.rubi6113r17Nondeg.conditions
    IntegrationNum1.rubi6113r17Nondeg.body IntegrationNum1.rubi6113r17Nondeg.result IntegrationNum1.rubi6113r17Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r17Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex] using h
  have he : env "e" ≠ 0 := (mul_ne_zero_iff.mp hN).1
  have hM : env "m" + 1 ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have hN2 : env "e" ^ 2 * (env "m" + 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 he) hM
  have hlt : (env "m").re < -1 := by
    have h := hcond (.gt (.int (-1)) (.var "m")) (by simp [IntegrationNum1.rubi6113r17Nondeg])
    have hh : (env "m").im = 0 ∧ (env "m").re < -1 := by
      simpa [Cond.Holds, Defined, eval, Interp.complex] using h
    exact hh.2
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r17Nondeg, Defined, eval, Interp.complex, Function.update, hk] at h
  have hm : env "m" = (k : ℂ) := (intValue?_eq _ _).1 hk
  have hkneg : k < 0 := by
    rw [hm] at hlt
    simp only [Complex.intCast_re] at hlt
    have h : k < (-1 : ℤ) := by exact_mod_cast hlt
    omega
  have hk1 : intValue? (env "m" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hk2 : intValue? (env "m" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hbase : ∀ᶠ w in 𝓝 t, env "d" + env "e" * w ≠ 0 := by
    filter_upwards [hF] with w hw
    simp [IntegrationNum1.rubi6113r17Nondeg, Defined, eval, Interp.complex, Function.update, hk, h2] at hw
    exact hw hkneg
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hbase] with w hw <;>
      simp [Defined, eval, Interp.complex, Function.update, h2, hk1, hk2, hw]
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [hbase] with w hw
      simp [IntegrationNum1.rubi6113r17Nondeg, Defined, eval, recEnv, Interp.complex, h2, hm1, hk1, hN, hN2, hw]
    · have hz := hbase.self_of_nhds
      have hU : HasDerivAt (fun w : ℂ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℂ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k+1) (env "d" + env "e"*t) (Or.inl hz)).comp t hU
      have hT := (Complex.hasDerivAt_sinh _).comp t hQ
      have hfun : (fun w => eval Interp.complex (recEnv env (IntegrationNum1.rubi6113r17Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r17Nondeg.result) =
        (fun w : ℂ => (env "d" + env "e"*w)^(k+1) * Complex.sinh (env "a" + env "b"*w + env "c"*w^2) * (env "e"*(env "m"+1))⁻¹ +
          (-(env "b"*env "e"-2*env "c"*env "d") * (env "e"^2*(env "m"+1))⁻¹) * Φ "I1" w +
          (-2*env "c" * (env "e"^2*(env "m"+1))⁻¹) * Φ "I2" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r17Nondeg, eval, recEnv, Interp.complex, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Interp.complex, Function.update, h2, hk1] at hΦ1
      simp [eval, Interp.complex, Function.update, h2, hk2] at hΦ2
      refine ((((hP.mul hT).mul_const _).add (hΦ1.const_mul _)).add (hΦ2.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r17Nondeg, eval, Interp.complex, Function.update, h2, hk]
      have hpow1 := zpow_add_one₀ hz k
      have hpow2 := zpow_add_one₀ hz (k+1)
      rw [show k + 1 + 1 = k + 2 by omega] at hpow2
      simp_rw [hpow2, hpow1]
      have hM' : (k : ℂ) + 1 ≠ 0 := by simpa [hm] using hM
      rw [hm]
      generalize (env "d"+env "e"*t)^k = P
      generalize Complex.sinh (env "a"+env "b"*t+env "c"*t^2) = S
      generalize Complex.cosh (env "a"+env "b"*t+env "c"*t^2) = C
      field_simp [he, hM']
      ring

theorem coshNegativeTwo_complex : IntegrationNum1.rubi6113r18Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" IntegrationNum1.rubi6113r18Nondeg.conditions
    IntegrationNum1.rubi6113r18Nondeg.body IntegrationNum1.rubi6113r18Nondeg.result IntegrationNum1.rubi6113r18Nondeg.integrals
  intro env hcond t hF
  have hm1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hN : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hcond (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [IntegrationNum1.rubi6113r18Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex] using h
  have he : env "e" ≠ 0 := (mul_ne_zero_iff.mp hN).1
  have hM : env "m" + 1 ≠ 0 := (mul_ne_zero_iff.mp hN).2
  have hN2 : env "e" ^ 2 * (env "m" + 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 he) hM
  have hlt : (env "m").re < -1 := by
    have h := hcond (.gt (.int (-1)) (.var "m")) (by simp [IntegrationNum1.rubi6113r18Nondeg])
    have hh : (env "m").im = 0 ∧ (env "m").re < -1 := by
      simpa [Cond.Holds, Defined, eval, Interp.complex] using h
    exact hh.2
  rcases hk : intValue? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [IntegrationNum1.rubi6113r18Nondeg, Defined, eval, Interp.complex, Function.update, hk] at h
  have hm : env "m" = (k : ℂ) := (intValue?_eq _ _).1 hk
  have hkneg : k < 0 := by
    rw [hm] at hlt
    simp only [Complex.intCast_re] at hlt
    have h : k < (-1 : ℤ) := by exact_mod_cast hlt
    omega
  have hk1 : intValue? (env "m" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hk2 : intValue? (env "m" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hbase : ∀ᶠ w in 𝓝 t, env "d" + env "e" * w ≠ 0 := by
    filter_upwards [hF] with w hw
    simp [IntegrationNum1.rubi6113r18Nondeg, Defined, eval, Interp.complex, Function.update, hk, h2] at hw
    exact hw hkneg
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [IntegrationNum1.rubi6113r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hbase] with w hw <;>
      simp [Defined, eval, Interp.complex, Function.update, h2, hk1, hk2, hw]
  · intro Φ hΦ
    simp only [IntegrationNum1.rubi6113r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards [hbase] with w hw
      simp [IntegrationNum1.rubi6113r18Nondeg, Defined, eval, recEnv, Interp.complex, h2, hm1, hk1, hN, hN2, hw]
    · have hz := hbase.self_of_nhds
      have hU : HasDerivAt (fun w : ℂ => env "d" + env "e"*w) (env "e") t := by
        simpa using (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))
      have hQ : HasDerivAt (fun w : ℂ => env "a" + env "b"*w + env "c"*w^2)
          (env "b" + env "c"*(2*t)) t := by
        convert (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
          ((hasDerivAt_pow 2 t).const_mul (env "c")) using 1
        simp
      have hP := (hasDerivAt_zpow (k+1) (env "d" + env "e"*t) (Or.inl hz)).comp t hU
      have hT := (Complex.hasDerivAt_cosh _).comp t hQ
      have hfun : (fun w => eval Interp.complex (recEnv env (IntegrationNum1.rubi6113r18Nondeg.integrals.map (·.1)) Φ "x" w) IntegrationNum1.rubi6113r18Nondeg.result) =
        (fun w : ℂ => (env "d" + env "e"*w)^(k+1) * Complex.cosh (env "a" + env "b"*w + env "c"*w^2) * (env "e"*(env "m"+1))⁻¹ +
          (-(env "b"*env "e"-2*env "c"*env "d") * (env "e"^2*(env "m"+1))⁻¹) * Φ "I1" w +
          (-2*env "c" * (env "e"^2*(env "m"+1))⁻¹) * Φ "I2" w) := by
        funext w
        simp [IntegrationNum1.rubi6113r18Nondeg, eval, recEnv, Interp.complex, h2, hm1, hk1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        ring
      rw [hfun]
      simp [eval, Interp.complex, Function.update, h2, hk1] at hΦ1
      simp [eval, Interp.complex, Function.update, h2, hk2] at hΦ2
      refine ((((hP.mul hT).mul_const _).add (hΦ1.const_mul _)).add (hΦ2.const_mul _)).congr_deriv ?_
      simp [IntegrationNum1.rubi6113r18Nondeg, eval, Interp.complex, Function.update, h2, hk]
      have hpow1 := zpow_add_one₀ hz k
      have hpow2 := zpow_add_one₀ hz (k+1)
      rw [show k + 1 + 1 = k + 2 by omega] at hpow2
      simp_rw [hpow2, hpow1]
      have hM' : (k : ℂ) + 1 ≠ 0 := by simpa [hm] using hM
      rw [hm]
      generalize (env "d"+env "e"*t)^k = P
      generalize Complex.sinh (env "a"+env "b"*t+env "c"*t^2) = S
      generalize Complex.cosh (env "a"+env "b"*t+env "c"*t^2) = C
      field_simp [he, hM']
      ring

end OSR.IntegrationHyperbolicPower
