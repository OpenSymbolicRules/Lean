import OSR.IntegrationNum1

/-! # Strengthened trigonometric and hyperbolic variants: three-factor quotients by `a + b z`

Proofs of RUBI 4.7.9 #28, #29, #31, #32 and 6.7.9 #23–#34, splitting
`(e + f x)^m y^p w^n / (a + b z)` into `(1/a) (e + f x)^m y^p w^n -
    (b/a) (e + f x)^m y^p' w^n' / (a + b z)`
or `(1/b) (e + f x)^m y^p' w^n' - (a/b) (e + f x)^m y^p' w^n' / (a + b z)` with shifted exponents
`p' = p ± 1`, `n' = n ± 1` and relations such as `coth · sinh = cosh`, `sech · sinh = tanh`. -/

namespace OSR.IntegrationRec257

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)

private theorem zpow_add_nat_of {𝕜 : Type} [Field 𝕜] (A : 𝕜) (j : ℤ) (n : ℕ) (h : 0 ≤ j) :
    A ^ (j + n) = A ^ j * A ^ n := by
  lift j to ℕ using h
  rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
    pow_add]

/-! ## rubi479r28Nondeg -/

theorem rubi479r28Nondeg_real : rubi479r28Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r28Nondeg.conditions rubi479r28Nondeg.body
    rubi479r28Nondeg.result rubi479r28Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi479r28Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r28Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r28Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r28Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r28Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi479r28Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r28Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r28Nondeg.body →
      Real.sin (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Real.cos (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r28Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r28Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨hsw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, ep1, en1, hm0, hk1, ivm1R, hsw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi479r28Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi479r28Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.sin (env "c" + env "d" * t)) ^ (q - 1) *
        (Real.cot (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, ep1, en1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.sin (env "c" + env "d" * t)) ^ (q - 1) *
        (Real.cot (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.cos (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, ep1, en1, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r28Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r28Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi479r28Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi479r28Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.sin (env "c" + env "d" * t)) ^ q *
        (Real.cot (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.cos (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r28Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hst, hDt⟩ := hD t hF.self_of_nhds
    have eA : (Real.sin (env "c" + env "d" * t)) ^ (q) =
        (Real.sin (env "c" + env "d" * t)) ^ (q - 1) * (Real.sin (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.sin (env "c" + env "d" * t)) (q - 1) 1 (by omega)
      rwa [show q - 1 + ((1 : ℕ) : ℤ) = q by push_cast; ring, pow_one] at this
    have eB : (Real.cot (env "c" + env "d" * t)) ^ (k) =
        (Real.cot (env "c" + env "d" * t)) ^ (k - 1) * (Real.cot (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.cot (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eA, eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.sin (env "c" + env "d" * t)) ^ (q - 1) = QA
    generalize (Real.cot (env "c" + env "d" * t)) ^ (k - 1) = QB
    simp only [Real.cot_eq_cos_div_sin]
    generalize hE : env "a" + env "b" * Real.cos (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi479r28Nondeg_complex : rubi479r28Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi479r28Nondeg.conditions rubi479r28Nondeg.body
    rubi479r28Nondeg.result rubi479r28Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi479r28Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r28Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r28Nondeg, Defined, eval, Interp.complex, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r28Nondeg, Defined, eval, Interp.complex, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r28Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi479r28Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkq] at h'
    have h'' : (0 : ℝ) < q := by simpa using h'
    exact_mod_cast h''
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r28Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkk] at h'
    have h'' : (0 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi479r28Nondeg.body →
      Complex.sin (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Complex.cos (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r28Nondeg, Defined, eval, Interp.complex, hkm, hkq, hkk, hm0, hq0, hk0,
        ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r28Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨hsw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.complex, hkm, ep1, en1, hm0, hk1, ivm1C, hsw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi479r28Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hl]
  · simp only [rubi479r28Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Complex.sin (env "c" + env "d" * t)) ^ (q - 1) *
        (Complex.cot (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, ep1, en1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Complex.sin (env "c" + env "d" * t)) ^ (q - 1) *
        (Complex.cot (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Complex.cos (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, ep1, en1, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi479r28Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r28Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi479r28Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi479r28Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Complex.sin (env "c" + env "d" * t)) ^ q *
        (Complex.cot (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Complex.cos (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r28Nondeg, eval, Interp.complex, hkm, hkq, hkk, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hst, hDt⟩ := hD t hF.self_of_nhds
    have eA : (Complex.sin (env "c" + env "d" * t)) ^ (q) =
        (Complex.sin (env "c" + env "d" * t)) ^ (q - 1) * (Complex.sin (env "c" + env "d" * t)) :=
        by
      have := zpow_add_nat_of (Complex.sin (env "c" + env "d" * t)) (q - 1) 1 (by omega)
      rwa [show q - 1 + ((1 : ℕ) : ℤ) = q by push_cast; ring, pow_one] at this
    have eB : (Complex.cot (env "c" + env "d" * t)) ^ (k) =
        (Complex.cot (env "c" + env "d" * t)) ^ (k - 1) * (Complex.cot (env "c" + env "d" * t)) :=
        by
      have := zpow_add_nat_of (Complex.cot (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eA, eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Complex.sin (env "c" + env "d" * t)) ^ (q - 1) = QA
    generalize (Complex.cot (env "c" + env "d" * t)) ^ (k - 1) = QB
    simp only [Complex.cot_eq_cos_div_sin]
    generalize hE : env "a" + env "b" * Complex.cos (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi479r29Nondeg -/

theorem rubi479r29Nondeg_real : rubi479r29Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r29Nondeg.conditions rubi479r29Nondeg.body
    rubi479r29Nondeg.result rubi479r29Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi479r29Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r29Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r29Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r29Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r29Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi479r29Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r29Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r29Nondeg.body →
      Real.sin (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Real.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r29Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r29Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨hsw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkq, hkk, en1, ep1', hm0, hq0, hk0, hk1, hq1', ivm1R,
          hsw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi479r29Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi479r29Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.cos (env "c" + env "d" * t)) ^ q * (Real.cot (env "c" + env "d" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkq, hkk]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.cos (env "c" + env "d" * t)) ^ (q + 1) *
        (Real.cot (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ep1', ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r29Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r29Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi479r29Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi479r29Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.cos (env "c" + env "d" * t)) ^ q *
        (Real.cot (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.sin (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r29Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hst, hDt⟩ := hD t hF.self_of_nhds
    have eA : (Real.cos (env "c" + env "d" * t)) ^ (q + 1) =
        (Real.cos (env "c" + env "d" * t)) ^ (q) * (Real.cos (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.cos (env "c" + env "d" * t)) (q) 1 (by omega)
      rwa [show q + ((1 : ℕ) : ℤ) = q + 1 by push_cast; ring, pow_one] at this
    have eB : (Real.cot (env "c" + env "d" * t)) ^ (k) =
        (Real.cot (env "c" + env "d" * t)) ^ (k - 1) * (Real.cot (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.cot (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eA, eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.cos (env "c" + env "d" * t)) ^ (q) = QA
    generalize (Real.cot (env "c" + env "d" * t)) ^ (k - 1) = QB
    simp only [Real.cot_eq_cos_div_sin]
    generalize hE : env "a" + env "b" * Real.sin (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi479r29Nondeg_complex : rubi479r29Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi479r29Nondeg.conditions rubi479r29Nondeg.body
    rubi479r29Nondeg.result rubi479r29Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi479r29Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r29Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r29Nondeg, Defined, eval, Interp.complex, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r29Nondeg, Defined, eval, Interp.complex, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r29Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi479r29Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkq] at h'
    have h'' : (0 : ℝ) < q := by simpa using h'
    exact_mod_cast h''
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r29Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkk] at h'
    have h'' : (0 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi479r29Nondeg.body →
      Complex.sin (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Complex.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r29Nondeg, Defined, eval, Interp.complex, hkm, hkq, hkk, hm0, hq0, hk0,
        ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r29Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨hsw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.complex, hkm, hkq, hkk, en1, ep1', hm0, hq0, hk0, hk1, hq1',
          ivm1C, hsw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi479r29Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hl]
  · simp only [rubi479r29Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Complex.cos (env "c" + env "d" * t)) ^ q * (Complex.cot (env "c" + env "d" * t)) ^ k) t :=
        by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, hkq, hkk]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Complex.cos (env "c" + env "d" * t)) ^ (q + 1) *
        (Complex.cot (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Complex.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, en1, ep1', ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi479r29Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r29Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi479r29Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi479r29Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Complex.cos (env "c" + env "d" * t)) ^ q *
        (Complex.cot (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Complex.sin (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r29Nondeg, eval, Interp.complex, hkm, hkq, hkk, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hst, hDt⟩ := hD t hF.self_of_nhds
    have eA : (Complex.cos (env "c" + env "d" * t)) ^ (q + 1) =
        (Complex.cos (env "c" + env "d" * t)) ^ (q) * (Complex.cos (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Complex.cos (env "c" + env "d" * t)) (q) 1 (by omega)
      rwa [show q + ((1 : ℕ) : ℤ) = q + 1 by push_cast; ring, pow_one] at this
    have eB : (Complex.cot (env "c" + env "d" * t)) ^ (k) =
        (Complex.cot (env "c" + env "d" * t)) ^ (k - 1) * (Complex.cot (env "c" + env "d" * t)) :=
        by
      have := zpow_add_nat_of (Complex.cot (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eA, eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Complex.cos (env "c" + env "d" * t)) ^ (q) = QA
    generalize (Complex.cot (env "c" + env "d" * t)) ^ (k - 1) = QB
    simp only [Complex.cot_eq_cos_div_sin]
    generalize hE : env "a" + env "b" * Complex.sin (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi479r31Nondeg -/

theorem rubi479r31Nondeg_real : rubi479r31Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r31Nondeg.conditions rubi479r31Nondeg.body
    rubi479r31Nondeg.result rubi479r31Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi479r31Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r31Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r31Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r31Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r31Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi479r31Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r31Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r31Nondeg.body →
      Real.sin (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Real.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r31Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R, Fn.csc]
        at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨hsw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkq, hkk, en1, hm0, hq0, ivm1R, Fn.csc, hsw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi479r31Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi479r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.cos (env "c" + env "d" * t)) ^ q * ((Real.sin (env "c" + env "d" * t))⁻¹) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkq, hkk, Fn.csc]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.cos (env "c" + env "d" * t)) ^ q * ((Real.sin (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        (env "a" + env "b" * Real.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, hkq, en1, ivm1R, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r31Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi479r31Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi479r31Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.cos (env "c" + env "d" * t)) ^ q *
        ((Real.sin (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.sin (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r31Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R, Fn.csc]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hst, hDt⟩ := hD t hF.self_of_nhds
    have eB : ((Real.sin (env "c" + env "d" * t))⁻¹) ^ (k) =
        ((Real.sin (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        ((Real.sin (env "c" + env "d" * t))⁻¹) := by
      have := zpow_add_nat_of ((Real.sin (env "c" + env "d" * t))⁻¹) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.cos (env "c" + env "d" * t)) ^ (q) = QA
    generalize ((Real.sin (env "c" + env "d" * t))⁻¹) ^ (k - 1) = QB
    generalize hE : env "a" + env "b" * Real.sin (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi479r32Nondeg -/

theorem rubi479r32Nondeg_real : rubi479r32Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r32Nondeg.conditions rubi479r32Nondeg.body
    rubi479r32Nondeg.result rubi479r32Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi479r32Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r32Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r32Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r32Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r32Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi479r32Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r32Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r32Nondeg.body →
      Real.cos (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Real.cos (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r32Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R, Fn.sec]
        at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r32Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨hcw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkq, hkk, en1, hm0, hq0, ivm1R, Fn.sec, hcw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi479r32Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi479r32Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.sin (env "c" + env "d" * t)) ^ q * ((Real.cos (env "c" + env "d" * t))⁻¹) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkq, hkk, Fn.sec]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.sin (env "c" + env "d" * t)) ^ q * ((Real.cos (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        (env "a" + env "b" * Real.cos (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, hkq, en1, ivm1R, Fn.sec]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r32Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r32Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi479r32Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi479r32Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.sin (env "c" + env "d" * t)) ^ q *
        ((Real.cos (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.cos (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r32Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R, Fn.sec]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hct, hDt⟩ := hD t hF.self_of_nhds
    have eB : ((Real.cos (env "c" + env "d" * t))⁻¹) ^ (k) =
        ((Real.cos (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        ((Real.cos (env "c" + env "d" * t))⁻¹) := by
      have := zpow_add_nat_of ((Real.cos (env "c" + env "d" * t))⁻¹) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.sin (env "c" + env "d" * t)) ^ (q) = QA
    generalize ((Real.cos (env "c" + env "d" * t))⁻¹) ^ (k - 1) = QB
    generalize hE : env "a" + env "b" * Real.cos (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r23Nondeg -/

theorem rubi679r23Nondeg_real : rubi679r23Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r23Nondeg.conditions rubi679r23Nondeg.body
    rubi679r23Nondeg.result rubi679r23Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r23Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r23Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r23Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r23Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r23Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r23Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r23Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r23Nondeg.body → env "a" +
      env "b" * Real.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r23Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r23Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain hDw := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkq, en1, hm0, hq0, hk1, ivm1R] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r23Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r23Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.cosh (env "c" + env "d" * t)) ^ q *
        (Real.sinh (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkq, en1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.cosh (env "c" + env "d" * t)) ^ q * (Real.sinh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, hkq, en1, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r23Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r23Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r23Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r23Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.cosh (env "c" + env "d" * t)) ^ q *
        (Real.sinh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r23Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain hDt := hD t hF.self_of_nhds
    have eB : (Real.sinh (env "c" + env "d" * t)) ^ (k) =
        (Real.sinh (env "c" + env "d" * t)) ^ (k - 1) * (Real.sinh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.sinh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.cosh (env "c" + env "d" * t)) ^ (q) = QA
    generalize (Real.sinh (env "c" + env "d" * t)) ^ (k - 1) = QB
    have hcz : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    generalize hE : env "a" + env "b" * Real.sinh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r23Nondeg_complex : rubi679r23Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r23Nondeg.conditions rubi679r23Nondeg.body
    rubi679r23Nondeg.result rubi679r23Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r23Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r23Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r23Nondeg, Defined, eval, Interp.complex, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r23Nondeg, Defined, eval, Interp.complex, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r23Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r23Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkq] at h'
    have h'' : (0 : ℝ) < q := by simpa using h'
    exact_mod_cast h''
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r23Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkk] at h'
    have h'' : (0 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi679r23Nondeg.body →
      env "a" + env "b" * Complex.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r23Nondeg, Defined, eval, Interp.complex, hkm, hkq, hkk, hm0, hq0, hk0,
        ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r23Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain hDw := hD w hw
      simp [Defined, eval, Interp.complex, hkm, hkq, en1, hm0, hq0, hk1, ivm1C] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r23Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hl]
  · simp only [rubi679r23Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Complex.cosh (env "c" + env "d" * t)) ^ q *
        (Complex.sinh (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, hkq, en1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Complex.cosh (env "c" + env "d" * t)) ^ q *
        (Complex.sinh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Complex.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, hkq, en1, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r23Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r23Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r23Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi679r23Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Complex.cosh (env "c" + env "d" * t)) ^ q *
        (Complex.sinh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Complex.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r23Nondeg, eval, Interp.complex, hkm, hkq, hkk, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain hDt := hD t hF.self_of_nhds
    have eB : (Complex.sinh (env "c" + env "d" * t)) ^ (k) =
        (Complex.sinh (env "c" + env "d" * t)) ^ (k - 1) *
        (Complex.sinh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Complex.sinh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Complex.cosh (env "c" + env "d" * t)) ^ (q) = QA
    generalize (Complex.sinh (env "c" + env "d" * t)) ^ (k - 1) = QB
    generalize hE : env "a" + env "b" * Complex.sinh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r24Nondeg -/

theorem rubi679r24Nondeg_real : rubi679r24Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r24Nondeg.conditions rubi679r24Nondeg.body
    rubi679r24Nondeg.result rubi679r24Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r24Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r24Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r24Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r24Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r24Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r24Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r24Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r24Nondeg.body → env "a" +
      env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r24Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r24Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain hDw := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkq, en1, hm0, hq0, hk1, ivm1R] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r24Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r24Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.sinh (env "c" + env "d" * t)) ^ q *
        (Real.cosh (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkq, en1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.sinh (env "c" + env "d" * t)) ^ q * (Real.cosh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, hkq, en1, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r24Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r24Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r24Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r24Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.sinh (env "c" + env "d" * t)) ^ q *
        (Real.cosh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r24Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain hDt := hD t hF.self_of_nhds
    have eB : (Real.cosh (env "c" + env "d" * t)) ^ (k) =
        (Real.cosh (env "c" + env "d" * t)) ^ (k - 1) * (Real.cosh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.cosh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.sinh (env "c" + env "d" * t)) ^ (q) = QA
    generalize (Real.cosh (env "c" + env "d" * t)) ^ (k - 1) = QB
    have hcz : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    generalize hE : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r24Nondeg_complex : rubi679r24Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r24Nondeg.conditions rubi679r24Nondeg.body
    rubi679r24Nondeg.result rubi679r24Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r24Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r24Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r24Nondeg, Defined, eval, Interp.complex, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r24Nondeg, Defined, eval, Interp.complex, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r24Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r24Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkq] at h'
    have h'' : (0 : ℝ) < q := by simpa using h'
    exact_mod_cast h''
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r24Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkk] at h'
    have h'' : (0 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi679r24Nondeg.body →
      env "a" + env "b" * Complex.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r24Nondeg, Defined, eval, Interp.complex, hkm, hkq, hkk, hm0, hq0, hk0,
        ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r24Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain hDw := hD w hw
      simp [Defined, eval, Interp.complex, hkm, hkq, en1, hm0, hq0, hk1, ivm1C] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r24Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hl]
  · simp only [rubi679r24Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Complex.sinh (env "c" + env "d" * t)) ^ q *
        (Complex.cosh (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, hkq, en1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Complex.sinh (env "c" + env "d" * t)) ^ q *
        (Complex.cosh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Complex.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, hkq, en1, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r24Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r24Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r24Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi679r24Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Complex.sinh (env "c" + env "d" * t)) ^ q *
        (Complex.cosh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Complex.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r24Nondeg, eval, Interp.complex, hkm, hkq, hkk, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain hDt := hD t hF.self_of_nhds
    have eB : (Complex.cosh (env "c" + env "d" * t)) ^ (k) =
        (Complex.cosh (env "c" + env "d" * t)) ^ (k - 1) *
        (Complex.cosh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Complex.cosh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Complex.sinh (env "c" + env "d" * t)) ^ (q) = QA
    generalize (Complex.cosh (env "c" + env "d" * t)) ^ (k - 1) = QB
    generalize hE : env "a" + env "b" * Complex.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r25Nondeg -/

theorem rubi679r25Nondeg_real : rubi679r25Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r25Nondeg.conditions rubi679r25Nondeg.body
    rubi679r25Nondeg.result rubi679r25Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r25Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r25Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r25Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r25Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r25Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r25Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r25Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r25Nondeg.body → env "a" +
      env "b" * Real.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r25Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r25Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain hDw := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkk, ep1, hm0, hk0, hq1, ivm1R] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r25Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r25Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.sinh (env "c" + env "d" * t)) ^ (q - 1) *
        (Real.tanh (env "c" + env "d" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkk, ep1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.sinh (env "c" + env "d" * t)) ^ (q - 1) * (Real.tanh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, hkk, ep1, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r25Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r25Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r25Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r25Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.sinh (env "c" + env "d" * t)) ^ q *
        (Real.tanh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r25Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain hDt := hD t hF.self_of_nhds
    have eA : (Real.sinh (env "c" + env "d" * t)) ^ (q) =
        (Real.sinh (env "c" + env "d" * t)) ^ (q - 1) * (Real.sinh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.sinh (env "c" + env "d" * t)) (q - 1) 1 (by omega)
      rwa [show q - 1 + ((1 : ℕ) : ℤ) = q by push_cast; ring, pow_one] at this
    rw [eA]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.sinh (env "c" + env "d" * t)) ^ (q - 1) = QA
    generalize (Real.tanh (env "c" + env "d" * t)) ^ (k) = QB
    have hcz : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    generalize hE : env "a" + env "b" * Real.sinh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r25Nondeg_complex : rubi679r25Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r25Nondeg.conditions rubi679r25Nondeg.body
    rubi679r25Nondeg.result rubi679r25Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r25Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r25Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r25Nondeg, Defined, eval, Interp.complex, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r25Nondeg, Defined, eval, Interp.complex, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r25Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r25Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkq] at h'
    have h'' : (0 : ℝ) < q := by simpa using h'
    exact_mod_cast h''
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r25Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkk] at h'
    have h'' : (0 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi679r25Nondeg.body →
      Complex.cosh (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Complex.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r25Nondeg, Defined, eval, Interp.complex, hkm, hkq, hkk, hm0, hq0, hk0,
        ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r25Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨hchw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.complex, hkm, hkk, ep1, hm0, hk0, hq1, ivm1C, hchw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r25Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hl]
  · simp only [rubi679r25Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Complex.sinh (env "c" + env "d" * t)) ^ (q - 1) *
        (Complex.tanh (env "c" + env "d" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, hkk, ep1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Complex.sinh (env "c" + env "d" * t)) ^ (q - 1) *
        (Complex.tanh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Complex.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, hkk, ep1, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r25Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r25Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r25Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi679r25Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Complex.sinh (env "c" + env "d" * t)) ^ q *
        (Complex.tanh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Complex.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r25Nondeg, eval, Interp.complex, hkm, hkq, hkk, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hcht, hDt⟩ := hD t hF.self_of_nhds
    have eA : (Complex.sinh (env "c" + env "d" * t)) ^ (q) =
        (Complex.sinh (env "c" + env "d" * t)) ^ (q - 1) *
        (Complex.sinh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Complex.sinh (env "c" + env "d" * t)) (q - 1) 1 (by omega)
      rwa [show q - 1 + ((1 : ℕ) : ℤ) = q by push_cast; ring, pow_one] at this
    rw [eA]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Complex.sinh (env "c" + env "d" * t)) ^ (q - 1) = QA
    generalize (Complex.tanh (env "c" + env "d" * t)) ^ (k) = QB
    generalize hE : env "a" + env "b" * Complex.sinh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r26Nondeg -/

theorem rubi679r26Nondeg_real : rubi679r26Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r26Nondeg.conditions rubi679r26Nondeg.body
    rubi679r26Nondeg.result rubi679r26Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r26Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r26Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r26Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r26Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r26Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r26Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r26Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r26Nondeg.body → env "c" +
      env "d" * w ≠ 0 ∧ env "a" + env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r26Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R,
        Fn.coth] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨huw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkk, ep1, hm0, hk0, hq1, ivm1R, Fn.coth, huw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r26Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.cosh (env "c" + env "d" * t)) ^ (q - 1) *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkk, ep1, Fn.coth]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.cosh (env "c" + env "d" * t)) ^ (q - 1) *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, hkk, ep1, ivm1R, Fn.coth]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r26Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r26Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r26Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r26Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.cosh (env "c" + env "d" * t)) ^ q *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r26Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R, Fn.coth]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hut, hDt⟩ := hD t hF.self_of_nhds
    have eA : (Real.cosh (env "c" + env "d" * t)) ^ (q) =
        (Real.cosh (env "c" + env "d" * t)) ^ (q - 1) * (Real.cosh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.cosh (env "c" + env "d" * t)) (q - 1) 1 (by omega)
      rwa [show q - 1 + ((1 : ℕ) : ℤ) = q by push_cast; ring, pow_one] at this
    rw [eA]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.cosh (env "c" + env "d" * t)) ^ (q - 1) = QA
    generalize ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k) = QB
    have hcz : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hsz : Real.sinh (env "c" + env "d" * t) ≠ 0 := fun h => hut (Real.sinh_eq_zero.mp h)
    generalize hE : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r27Nondeg -/

theorem rubi679r27Nondeg_real : rubi679r27Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r27Nondeg.conditions rubi679r27Nondeg.body
    rubi679r27Nondeg.result rubi679r27Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r27Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r27Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r27Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r27Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r27Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r27Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r27Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r27Nondeg.body → env "a" +
      env "b" * Real.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r27Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R,
        Fn.sech] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain hDw := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, ep1', hm0, hk1, hq1', ivm1R, Fn.sech] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r27Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (q + 1) *
        (Real.tanh (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, en1, ep1', Fn.sech]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (q + 1) *
        (Real.tanh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ep1', ivm1R, Fn.sech]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r27Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r27Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r27Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r27Nondeg.body =
        (env "e" + env "f" * t) ^ m * ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ q *
        (Real.tanh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r27Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R, Fn.sech]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain hDt := hD t hF.self_of_nhds
    have eA : ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (q + 1) =
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (q) * ((Real.cosh (env "c" + env "d" * t))⁻¹) :=
        by
      have := zpow_add_nat_of ((Real.cosh (env "c" + env "d" * t))⁻¹) (q) 1 (by omega)
      rwa [show q + ((1 : ℕ) : ℤ) = q + 1 by push_cast; ring, pow_one] at this
    have eB : (Real.tanh (env "c" + env "d" * t)) ^ (k) =
        (Real.tanh (env "c" + env "d" * t)) ^ (k - 1) * (Real.tanh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.tanh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eA, eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (q) = QA
    generalize (Real.tanh (env "c" + env "d" * t)) ^ (k - 1) = QB
    have hcz : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    simp only [Real.tanh_eq_sinh_div_cosh]
    generalize hE : env "a" + env "b" * Real.sinh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r28Nondeg -/

theorem rubi679r28Nondeg_real : rubi679r28Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r28Nondeg.conditions rubi679r28Nondeg.body
    rubi679r28Nondeg.result rubi679r28Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r28Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r28Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r28Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r28Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r28Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r28Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r28Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r28Nondeg.body → env "c" +
      env "d" * w ≠ 0 ∧ env "a" + env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r28Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R,
        Fn.coth, Fn.csch] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r28Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨huw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, ep1', hm0, hk1, ivm1R, Fn.coth, Fn.csch,
          huw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r28Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r28Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (q + 1) *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, en1, ep1', Fn.coth, Fn.csch]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (q + 1) *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ep1', ivm1R, Fn.coth, Fn.csch]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r28Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r28Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r28Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r28Nondeg.body =
        (env "e" + env "f" * t) ^ m * ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ q *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r28Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R, Fn.coth, Fn.csch]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hut, hDt⟩ := hD t hF.self_of_nhds
    have eA : ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (q + 1) =
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (q) * ((Real.sinh (env "c" + env "d" * t))⁻¹) :=
        by
      have := zpow_add_nat_of ((Real.sinh (env "c" + env "d" * t))⁻¹) (q) 1 (by omega)
      rwa [show q + ((1 : ℕ) : ℤ) = q + 1 by push_cast; ring, pow_one] at this
    have eB : ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k) =
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) := by
      have := zpow_add_nat_of ((Real.tanh (env "c" + env "d" * t))⁻¹) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eA, eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (q) = QA
    generalize ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1) = QB
    have hcz : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hsz : Real.sinh (env "c" + env "d" * t) ≠ 0 := fun h => hut (Real.sinh_eq_zero.mp h)
    simp only [Real.tanh_eq_sinh_div_cosh]
    generalize hE : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r29Nondeg -/

theorem rubi679r29Nondeg_real : rubi679r29Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r29Nondeg.conditions rubi679r29Nondeg.body
    rubi679r29Nondeg.result rubi679r29Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi679r29Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r29Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r29Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r29Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r29Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r29Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r29Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r29Nondeg.body → env "c" +
      env "d" * w ≠ 0 ∧ env "a" + env "b" * Real.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r29Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R,
        Fn.coth] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r29Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨huw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkq, hkk, en1, ep1', hm0, hq0, hk0, hk1, hq1', ivm1R,
          Fn.coth, huw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r29Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r29Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.cosh (env "c" + env "d" * t)) ^ q * ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k) t :=
        by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkq, hkk, Fn.coth]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.cosh (env "c" + env "d" * t)) ^ (q + 1) *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ep1', ivm1R, Fn.coth]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r29Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r29Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r29Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r29Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.cosh (env "c" + env "d" * t)) ^ q *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r29Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R, Fn.coth]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hut, hDt⟩ := hD t hF.self_of_nhds
    have eA : (Real.cosh (env "c" + env "d" * t)) ^ (q + 1) =
        (Real.cosh (env "c" + env "d" * t)) ^ (q) * (Real.cosh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.cosh (env "c" + env "d" * t)) (q) 1 (by omega)
      rwa [show q + ((1 : ℕ) : ℤ) = q + 1 by push_cast; ring, pow_one] at this
    have eB : ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k) =
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) := by
      have := zpow_add_nat_of ((Real.tanh (env "c" + env "d" * t))⁻¹) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eA, eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.cosh (env "c" + env "d" * t)) ^ (q) = QA
    generalize ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1) = QB
    have hcz : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hsz : Real.sinh (env "c" + env "d" * t) ≠ 0 := fun h => hut (Real.sinh_eq_zero.mp h)
    simp only [Real.tanh_eq_sinh_div_cosh]
    generalize hE : env "a" + env "b" * Real.sinh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r30Nondeg -/

theorem rubi679r30Nondeg_real : rubi679r30Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r30Nondeg.conditions rubi679r30Nondeg.body
    rubi679r30Nondeg.result rubi679r30Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi679r30Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r30Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r30Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r30Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r30Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r30Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r30Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r30Nondeg.body → env "a" +
      env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r30Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r30Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain hDw := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkq, hkk, en1, ep1', hm0, hq0, hk0, hk1, hq1', ivm1R]
          at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r30Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r30Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.sinh (env "c" + env "d" * t)) ^ q * (Real.tanh (env "c" + env "d" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkq, hkk]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.sinh (env "c" + env "d" * t)) ^ (q + 1) *
        (Real.tanh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ep1', ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r30Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r30Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r30Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r30Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.sinh (env "c" + env "d" * t)) ^ q *
        (Real.tanh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r30Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain hDt := hD t hF.self_of_nhds
    have eA : (Real.sinh (env "c" + env "d" * t)) ^ (q + 1) =
        (Real.sinh (env "c" + env "d" * t)) ^ (q) * (Real.sinh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.sinh (env "c" + env "d" * t)) (q) 1 (by omega)
      rwa [show q + ((1 : ℕ) : ℤ) = q + 1 by push_cast; ring, pow_one] at this
    have eB : (Real.tanh (env "c" + env "d" * t)) ^ (k) =
        (Real.tanh (env "c" + env "d" * t)) ^ (k - 1) * (Real.tanh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.tanh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eA, eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.sinh (env "c" + env "d" * t)) ^ (q) = QA
    generalize (Real.tanh (env "c" + env "d" * t)) ^ (k - 1) = QB
    have hcz : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    simp only [Real.tanh_eq_sinh_div_cosh]
    generalize hE : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r30Nondeg_complex : rubi679r30Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r30Nondeg.conditions rubi679r30Nondeg.body
    rubi679r30Nondeg.result rubi679r30Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi679r30Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r30Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r30Nondeg, Defined, eval, Interp.complex, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r30Nondeg, Defined, eval, Interp.complex, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r30Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r30Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkq] at h'
    have h'' : (0 : ℝ) < q := by simpa using h'
    exact_mod_cast h''
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r30Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkk] at h'
    have h'' : (0 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi679r30Nondeg.body →
      Complex.cosh (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Complex.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r30Nondeg, Defined, eval, Interp.complex, hkm, hkq, hkk, hm0, hq0, hk0,
        ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r30Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨hchw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.complex, hkm, hkq, hkk, en1, ep1', hm0, hq0, hk0, hk1, hq1',
          ivm1C, hchw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r30Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hl]
  · simp only [rubi679r30Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Complex.sinh (env "c" + env "d" * t)) ^ q *
        (Complex.tanh (env "c" + env "d" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, hkq, hkk]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Complex.sinh (env "c" + env "d" * t)) ^ (q + 1) *
        (Complex.tanh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Complex.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, en1, ep1', ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r30Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r30Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r30Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi679r30Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Complex.sinh (env "c" + env "d" * t)) ^ q *
        (Complex.tanh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Complex.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r30Nondeg, eval, Interp.complex, hkm, hkq, hkk, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hcht, hDt⟩ := hD t hF.self_of_nhds
    have eA : (Complex.sinh (env "c" + env "d" * t)) ^ (q + 1) =
        (Complex.sinh (env "c" + env "d" * t)) ^ (q) * (Complex.sinh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Complex.sinh (env "c" + env "d" * t)) (q) 1 (by omega)
      rwa [show q + ((1 : ℕ) : ℤ) = q + 1 by push_cast; ring, pow_one] at this
    have eB : (Complex.tanh (env "c" + env "d" * t)) ^ (k) =
        (Complex.tanh (env "c" + env "d" * t)) ^ (k - 1) *
        (Complex.tanh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Complex.tanh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eA, eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Complex.sinh (env "c" + env "d" * t)) ^ (q) = QA
    generalize (Complex.tanh (env "c" + env "d" * t)) ^ (k - 1) = QB
    simp only [Complex.tanh_eq_sinh_div_cosh]
    generalize hE : env "a" + env "b" * Complex.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r31Nondeg -/

theorem rubi679r31Nondeg_real : rubi679r31Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r31Nondeg.conditions rubi679r31Nondeg.body
    rubi679r31Nondeg.result rubi679r31Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi679r31Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r31Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r31Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r31Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r31Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r31Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r31Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r31Nondeg.body → env "c" +
      env "d" * w ≠ 0 ∧ env "a" + env "b" * Real.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r31Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R,
        Fn.coth, Fn.csch] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨huw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkq, hkk, ep1, hm0, hk0, ivm1R, Fn.coth, Fn.csch, huw]
          at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r31Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ q *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkq, hkk, Fn.coth, Fn.csch]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (q - 1) *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, hkk, ep1, ivm1R, Fn.coth, Fn.csch]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r31Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r31Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r31Nondeg.body =
        (env "e" + env "f" * t) ^ m * ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ q *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r31Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R, Fn.coth, Fn.csch]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hut, hDt⟩ := hD t hF.self_of_nhds
    have eA : ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (q) =
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (q - 1) *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) := by
      have := zpow_add_nat_of ((Real.sinh (env "c" + env "d" * t))⁻¹) (q - 1) 1 (by omega)
      rwa [show q - 1 + ((1 : ℕ) : ℤ) = q by push_cast; ring, pow_one] at this
    rw [eA]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (q - 1) = QA
    generalize ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k) = QB
    have hcz : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hsz : Real.sinh (env "c" + env "d" * t) ≠ 0 := fun h => hut (Real.sinh_eq_zero.mp h)
    generalize hE : env "a" + env "b" * Real.sinh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r32Nondeg -/

theorem rubi679r32Nondeg_real : rubi679r32Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r32Nondeg.conditions rubi679r32Nondeg.body
    rubi679r32Nondeg.result rubi679r32Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi679r32Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r32Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r32Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r32Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r32Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r32Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r32Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r32Nondeg.body → env "a" +
      env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r32Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R,
        Fn.sech] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r32Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain hDw := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkq, hkk, ep1, hm0, hq0, hk0, hq1, ivm1R,
          Fn.sech] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r32Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r32Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ q * (Real.tanh (env "c" + env "d" * t)) ^ k) t :=
        by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkq, hkk, Fn.sech]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (q - 1) *
        (Real.tanh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, hkk, ep1, ivm1R, Fn.sech]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r32Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r32Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r32Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r32Nondeg.body =
        (env "e" + env "f" * t) ^ m * ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ q *
        (Real.tanh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r32Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R, Fn.sech]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain hDt := hD t hF.self_of_nhds
    have eA : ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (q) =
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (q - 1) *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) := by
      have := zpow_add_nat_of ((Real.cosh (env "c" + env "d" * t))⁻¹) (q - 1) 1 (by omega)
      rwa [show q - 1 + ((1 : ℕ) : ℤ) = q by push_cast; ring, pow_one] at this
    rw [eA]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (q - 1) = QA
    generalize (Real.tanh (env "c" + env "d" * t)) ^ (k) = QB
    have hcz : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    generalize hE : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r33Nondeg -/

theorem rubi679r33Nondeg_real : rubi679r33Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r33Nondeg.conditions rubi679r33Nondeg.body
    rubi679r33Nondeg.result rubi679r33Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi679r33Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r33Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r33Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r33Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r33Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r33Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r33Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r33Nondeg.body → env "c" +
      env "d" * w ≠ 0 ∧ env "a" + env "b" * Real.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r33Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R,
        Fn.csch, Fn.sech] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r33Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨huw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkq, hkk, en1, hm0, hq0, ivm1R, Fn.csch, Fn.sech, huw]
          at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r33Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r33Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ q *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkq, hkk, Fn.csch, Fn.sech]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ q *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, hkq, en1, ivm1R, Fn.csch, Fn.sech]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r33Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r33Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r33Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r33Nondeg.body =
        (env "e" + env "f" * t) ^ m * ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ q *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r33Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R, Fn.csch, Fn.sech]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hut, hDt⟩ := hD t hF.self_of_nhds
    have eB : ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (k) =
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) := by
      have := zpow_add_nat_of ((Real.sinh (env "c" + env "d" * t))⁻¹) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (q) = QA
    generalize ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (k - 1) = QB
    have hcz : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hsz : Real.sinh (env "c" + env "d" * t) ≠ 0 := fun h => hut (Real.sinh_eq_zero.mp h)
    generalize hE : env "a" + env "b" * Real.sinh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r34Nondeg -/

theorem rubi679r34Nondeg_real : rubi679r34Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r34Nondeg.conditions rubi679r34Nondeg.body
    rubi679r34Nondeg.result rubi679r34Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi679r34Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r34Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkq : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r34Nondeg, Defined, eval, Interp.real, hkm, hkq] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r34Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r34Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hqpos : 0 < q := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi679r34Nondeg])
    have h' : (0 : ℝ) < env "p" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkq] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r34Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hq1' : ¬ q + 1 < 0 := by omega
  have hk1' : ¬ k + 1 < 0 := by omega
  have ep1 : intValue? (env "p" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have ep1' : intValue? (env "p" + 1) = some (q + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkq]; push_cast; ring)
  have en1' : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r34Nondeg.body → env "c" +
      env "d" * w ≠ 0 ∧ env "a" + env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r34Nondeg, Defined, eval, Interp.real, hkm, hkq, hkk, hm0, hq0, hk0, ivm1R,
        Fn.csch, Fn.sech] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r34Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨huw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkq, hkk, en1, hm0, hk0, hk1, ivm1R, Fn.csch, Fn.sech,
          huw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r34Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r34Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ q *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkq, hkk, Fn.csch, Fn.sech]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ q *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, hkq, en1, ivm1R, Fn.csch, Fn.sech]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r34Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r34Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r34Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r34Nondeg.body =
        (env "e" + env "f" * t) ^ m * ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ q *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r34Nondeg, eval, Interp.real, hkm, hkq, hkk, ivm1R, Fn.csch, Fn.sech]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hut, hDt⟩ := hD t hF.self_of_nhds
    have eB : ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (k) =
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) := by
      have := zpow_add_nat_of ((Real.cosh (env "c" + env "d" * t))⁻¹) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [eB]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (q) = QA
    generalize ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (k - 1) = QB
    have hcz : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hsz : Real.sinh (env "c" + env "d" * t) ≠ 0 := fun h => hut (Real.sinh_eq_zero.mp h)
    generalize hE : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

end OSR.IntegrationRec257
