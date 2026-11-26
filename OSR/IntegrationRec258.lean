import OSR.IntegrationNum1

/-! # Strengthened hyperbolic variants: even reductions of quotients

Proofs of RUBI 6.7.9 #9 and #10 over ℝ and ℂ: `(e + f x)^m yⁿ / (a + b z)` with `n > 1` splits
into three residual integrals with `y^(n - 2)` after `cosh² = sinh² + 1` or `sinh² = cosh² - 1`. -/

namespace OSR.IntegrationRec258

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem zpow_add_nat_of {𝕜 : Type} [Field 𝕜] (A : 𝕜) (j : ℤ) (n : ℕ) (h : 0 ≤ j) :
    A ^ (j + n) = A ^ j * A ^ n := by
  lift j to ℕ using h
  rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
    pow_add]

/-! ## rubi679r9Nondeg -/

theorem rubi679r9Nondeg_real : rubi679r9Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r9Nondeg.conditions rubi679r9Nondeg.body
    rubi679r9Nondeg.result rubi679r9Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi679r9Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r9Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r9Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r9Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 1 < k := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi679r9Nondeg])
    have h' : (1 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk2 : ¬ k - 2 < 0 := by omega
  have en2 : intValue? (env "n" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r9Nondeg.body → env "a" +
      env "b" * Real.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r9Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have hDw := hD w hw
      simp [Defined, eval, Interp.real, hkm, en2, hm0, hk2, ivm1R] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r9Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi679r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.cosh (env "c" + env "d" * t)) ^ (k - 2)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, en2]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.cosh (env "c" + env "d" * t)) ^ (k - 2) * Real.sinh (env "c" + env "d" * t)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en2]
    have hΦ3' : HasDerivAt (Φ "I3")
        ((env "e" + env "f" * t) ^ m * (Real.cosh (env "c" + env "d" * t)) ^ (k - 2) *
            (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ3 using 1
      simp [eval, Interp.real, hkm, en2, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r9Nondeg.result) = fun w => -(env "a" / env "b" ^ 2) * Φ "I1" w +
            Φ "I2" w / env "b" + (env "a" ^ 2 + env "b" ^ 2) / env "b" ^ 2 * Φ "I3" w := by
      funext w
      simp [rubi679r9Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
      ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r9Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.cosh (env "c" + env "d" * t)) ^ k *
            (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r9Nondeg, eval, Interp.real, hkm, hkk, ivm1R]
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.div_const _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    have hDt := hD t hF.self_of_nhds
    have eX : (Real.cosh (env "c" + env "d" * t)) ^ k =
        (Real.cosh (env "c" + env "d" * t)) ^ (k - 2) * (Real.cosh (env "c" + env "d" * t)) ^ 2 :=
        by
      have := zpow_add_nat_of (Real.cosh (env "c" + env "d" * t)) (k - 2) 2 (by omega)
      rwa [show k - 2 + ((2 : ℕ) : ℤ) = k by push_cast; ring] at this
    rw [eX, Real.cosh_sq]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.cosh (env "c" + env "d" * t)) ^ (k - 2) = QA
    generalize hE : env "a" + env "b" * Real.sinh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r9Nondeg_complex : rubi679r9Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r9Nondeg.conditions rubi679r9Nondeg.body
    rubi679r9Nondeg.result rubi679r9Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi679r9Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r9Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r9Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r9Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hkpos : 1 < k := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi679r9Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkk] at h'
    have h'' : (1 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk2 : ¬ k - 2 < 0 := by omega
  have en2 : intValue? (env "n" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi679r9Nondeg.body →
      env "a" + env "b" * Complex.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r9Nondeg, Defined, eval, Interp.complex, hkm, hkk, hm0, hk0, ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have hDw := hD w hw
      simp [Defined, eval, Interp.complex, hkm, en2, hm0, hk2, ivm1C] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r9Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb]
  · simp only [rubi679r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Complex.cosh (env "c" + env "d" * t)) ^ (k - 2)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, en2]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Complex.cosh (env "c" + env "d" * t)) ^ (k - 2) *
        Complex.sinh (env "c" + env "d" * t)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, en2]
    have hΦ3' : HasDerivAt (Φ "I3")
        ((env "e" + env "f" * t) ^ m * (Complex.cosh (env "c" + env "d" * t)) ^ (k - 2) *
            (env "a" + env "b" * Complex.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ3 using 1
      simp [eval, Interp.complex, hkm, en2, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r9Nondeg.result) = fun w => -(env "a" / env "b" ^ 2) * Φ "I1" w +
            Φ "I2" w / env "b" + (env "a" ^ 2 + env "b" ^ 2) / env "b" ^ 2 * Φ "I3" w := by
      funext w
      simp [rubi679r9Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C]
      ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi679r9Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Complex.cosh (env "c" + env "d" * t)) ^ k *
            (env "a" + env "b" * Complex.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r9Nondeg, eval, Interp.complex, hkm, hkk, ivm1C]
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.div_const _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    have hDt := hD t hF.self_of_nhds
    have eX : (Complex.cosh (env "c" + env "d" * t)) ^ k =
        (Complex.cosh (env "c" + env "d" * t)) ^ (k - 2) *
        (Complex.cosh (env "c" + env "d" * t)) ^ 2 := by
      have := zpow_add_nat_of (Complex.cosh (env "c" + env "d" * t)) (k - 2) 2 (by omega)
      rwa [show k - 2 + ((2 : ℕ) : ℤ) = k by push_cast; ring] at this
    rw [eX, Complex.cosh_sq]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Complex.cosh (env "c" + env "d" * t)) ^ (k - 2) = QA
    generalize hE : env "a" + env "b" * Complex.sinh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r10Nondeg -/

theorem rubi679r10Nondeg_real : rubi679r10Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r10Nondeg.conditions rubi679r10Nondeg.body
    rubi679r10Nondeg.result rubi679r10Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi679r10Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r10Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r10Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r10Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 1 < k := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi679r10Nondeg])
    have h' : (1 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk2 : ¬ k - 2 < 0 := by omega
  have en2 : intValue? (env "n" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r10Nondeg.body → env "a" +
      env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r10Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have hDw := hD w hw
      simp [Defined, eval, Interp.real, hkm, en2, hm0, hk2, ivm1R] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r10Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi679r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.sinh (env "c" + env "d" * t)) ^ (k - 2)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, en2]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.sinh (env "c" + env "d" * t)) ^ (k - 2) * Real.cosh (env "c" + env "d" * t)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en2]
    have hΦ3' : HasDerivAt (Φ "I3")
        ((env "e" + env "f" * t) ^ m * (Real.sinh (env "c" + env "d" * t)) ^ (k - 2) *
            (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ3 using 1
      simp [eval, Interp.real, hkm, en2, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r10Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r10Nondeg.result) = fun w => -(env "a" / env "b" ^ 2) * Φ "I1" w +
            Φ "I2" w / env "b" + (env "a" ^ 2 - env "b" ^ 2) / env "b" ^ 2 * Φ "I3" w := by
      funext w
      simp [rubi679r10Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
      ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r10Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.sinh (env "c" + env "d" * t)) ^ k *
            (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r10Nondeg, eval, Interp.real, hkm, hkk, ivm1R]
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.div_const _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    have hDt := hD t hF.self_of_nhds
    have eX : (Real.sinh (env "c" + env "d" * t)) ^ k =
        (Real.sinh (env "c" + env "d" * t)) ^ (k - 2) * (Real.sinh (env "c" + env "d" * t)) ^ 2 :=
        by
      have := zpow_add_nat_of (Real.sinh (env "c" + env "d" * t)) (k - 2) 2 (by omega)
      rwa [show k - 2 + ((2 : ℕ) : ℤ) = k by push_cast; ring] at this
    rw [eX, Real.sinh_sq]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.sinh (env "c" + env "d" * t)) ^ (k - 2) = QA
    generalize hE : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r10Nondeg_complex : rubi679r10Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r10Nondeg.conditions rubi679r10Nondeg.body
    rubi679r10Nondeg.result rubi679r10Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi679r10Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r10Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r10Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r10Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hkpos : 1 < k := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi679r10Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkk] at h'
    have h'' : (1 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk2 : ¬ k - 2 < 0 := by omega
  have en2 : intValue? (env "n" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi679r10Nondeg.body →
      env "a" + env "b" * Complex.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r10Nondeg, Defined, eval, Interp.complex, hkm, hkk, hm0, hk0, ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · filter_upwards [hF] with w hw
      have hDw := hD w hw
      simp [Defined, eval, Interp.complex, hkm, en2, hm0, hk2, ivm1C] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r10Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb]
  · simp only [rubi679r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Complex.sinh (env "c" + env "d" * t)) ^ (k - 2)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, en2]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Complex.sinh (env "c" + env "d" * t)) ^ (k - 2) *
        Complex.cosh (env "c" + env "d" * t)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, en2]
    have hΦ3' : HasDerivAt (Φ "I3")
        ((env "e" + env "f" * t) ^ m * (Complex.sinh (env "c" + env "d" * t)) ^ (k - 2) *
            (env "a" + env "b" * Complex.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ3 using 1
      simp [eval, Interp.complex, hkm, en2, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r10Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r10Nondeg.result) = fun w => -(env "a" / env "b" ^ 2) * Φ "I1" w +
            Φ "I2" w / env "b" + (env "a" ^ 2 - env "b" ^ 2) / env "b" ^ 2 * Φ "I3" w := by
      funext w
      simp [rubi679r10Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C]
      ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi679r10Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Complex.sinh (env "c" + env "d" * t)) ^ k *
            (env "a" + env "b" * Complex.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r10Nondeg, eval, Interp.complex, hkm, hkk, ivm1C]
    rw [hfun, hEF]
    refine (((hΦ1'.const_mul _).add (hΦ2'.div_const _)).add (hΦ3'.const_mul _)).congr_deriv ?_
    have hDt := hD t hF.self_of_nhds
    have eX : (Complex.sinh (env "c" + env "d" * t)) ^ k =
        (Complex.sinh (env "c" + env "d" * t)) ^ (k - 2) *
        (Complex.sinh (env "c" + env "d" * t)) ^ 2 := by
      have := zpow_add_nat_of (Complex.sinh (env "c" + env "d" * t)) (k - 2) 2 (by omega)
      rwa [show k - 2 + ((2 : ℕ) : ℤ) = k by push_cast; ring] at this
    rw [eX, Complex.sinh_sq]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Complex.sinh (env "c" + env "d" * t)) ^ (k - 2) = QA
    generalize hE : env "a" + env "b" * Complex.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

end OSR.IntegrationRec258
