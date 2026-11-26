import OSR.IntegrationNum1

/-! # Strengthened trigonometric and hyperbolic variants: quotients by `a + b z`

Proofs of RUBI 4.7.9 #21 and #22 and 6.7.9 #19 and #20 over ℝ (`csc`, `sec`, `csch`, `sech` have
no complex interpretation), splitting `(e + f x)^m (1/z)^n / (a + b z)` into
`(e + f x)^m (1/z)^n / a - (b / a) (e + f x)^m (1/z)^(n - 1) / (a + b z)`, and of 6.7.9 #1 and #2
over ℝ and ℂ, splitting `(e + f x)^m z^n / (a + b z)` into
`(e + f x)^m z^(n - 1) / b - (a / b) (e + f x)^m z^(n - 1) / (a + b z)` for `z = sinh, cosh`.
The mixed quotients 4.7.9 #13, #14, #15 and 6.7.9 #11–#14 use `y z = w` relations such as
`cot · sin = cos`, `tanh · cosh = sinh`, `sec · sin = tan` (over ℝ and ℂ for 4.7.9 #15 and
6.7.9 #14, over ℝ for the others). -/

namespace OSR.IntegrationRec255

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)

private theorem zpow_add_nat_of {𝕜 : Type} [Field 𝕜] (A : 𝕜) (j : ℤ) (n : ℕ) (h : 0 ≤ j) :
    A ^ (j + n) = A ^ j * A ^ n := by
  lift j to ℕ using h
  rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
    pow_add]

/-! ## rubi479r21Nondeg -/

theorem rubi479r21Nondeg_real : rubi479r21Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r21Nondeg.conditions rubi479r21Nondeg.body
    rubi479r21Nondeg.result rubi479r21Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi479r21Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r21Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r21Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r21Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r21Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r21Nondeg.body →
      Real.sin (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Real.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r21Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r21Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, hkm, hkk, hm0, Fn.csc, (hD w hw).1]
    · filter_upwards [hF] with w hw
      have h := (hD w hw).2
      simp [Defined, eval, Interp.real, hkm, en1, hm0, ivm1R, Fn.csc, (hD w hw).1] at h ⊢
      exact h
  · filter_upwards with w
    simp [rubi479r21Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi479r21Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        ((Real.sin (env "c" + env "d" * t))⁻¹) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkk, Fn.csc]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        ((Real.sin (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        (env "a" + env "b" * Real.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r21Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r21Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi479r21Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi479r21Nondeg.body =
        (env "e" + env "f" * t) ^ m * ((Real.sin (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.sin (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r21Nondeg, eval, Interp.real, hkm, hkk, ivm1R, Fn.csc]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hZ0 : Real.sin (env "c" + env "d" * t) ≠ 0 := (hD t hF.self_of_nhds).1
    have hD0 := (hD t hF.self_of_nhds).2
    have ek : ((Real.sin (env "c" + env "d" * t))⁻¹) ^ k =
        ((Real.sin (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        ((Real.sin (env "c" + env "d" * t))⁻¹) := by
      rw [← zpow_add_one₀ (inv_ne_zero hZ0), sub_add_cancel]
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize ((Real.sin (env "c" + env "d" * t))⁻¹) ^ (k - 1) = Q1
    generalize Real.sin (env "c" + env "d" * t) = z at hZ0 hD0 ⊢
    generalize hE : env "a" + env "b" * z = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi479r22Nondeg -/

theorem rubi479r22Nondeg_real : rubi479r22Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r22Nondeg.conditions rubi479r22Nondeg.body
    rubi479r22Nondeg.result rubi479r22Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi479r22Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r22Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r22Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r22Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r22Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r22Nondeg.body →
      Real.cos (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Real.cos (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r22Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R, Fn.sec] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r22Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, hkm, hkk, hm0, Fn.sec, (hD w hw).1]
    · filter_upwards [hF] with w hw
      have h := (hD w hw).2
      simp [Defined, eval, Interp.real, hkm, en1, hm0, ivm1R, Fn.sec, (hD w hw).1] at h ⊢
      exact h
  · filter_upwards with w
    simp [rubi479r22Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi479r22Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        ((Real.cos (env "c" + env "d" * t))⁻¹) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkk, Fn.sec]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        ((Real.cos (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        (env "a" + env "b" * Real.cos (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R, Fn.sec]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r22Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r22Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi479r22Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi479r22Nondeg.body =
        (env "e" + env "f" * t) ^ m * ((Real.cos (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.cos (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r22Nondeg, eval, Interp.real, hkm, hkk, ivm1R, Fn.sec]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hZ0 : Real.cos (env "c" + env "d" * t) ≠ 0 := (hD t hF.self_of_nhds).1
    have hD0 := (hD t hF.self_of_nhds).2
    have ek : ((Real.cos (env "c" + env "d" * t))⁻¹) ^ k =
        ((Real.cos (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        ((Real.cos (env "c" + env "d" * t))⁻¹) := by
      rw [← zpow_add_one₀ (inv_ne_zero hZ0), sub_add_cancel]
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize ((Real.cos (env "c" + env "d" * t))⁻¹) ^ (k - 1) = Q1
    generalize Real.cos (env "c" + env "d" * t) = z at hZ0 hD0 ⊢
    generalize hE : env "a" + env "b" * z = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r19Nondeg -/

theorem rubi679r19Nondeg_real : rubi679r19Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r19Nondeg.conditions rubi679r19Nondeg.body
    rubi679r19Nondeg.result rubi679r19Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi679r19Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r19Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r19Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r19Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r19Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r19Nondeg.body →
      Real.sinh (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Real.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r19Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R, Fn.csch] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, hkm, hkk, hm0, Fn.csch, (hD w hw).1,
          Real.sinh_eq_zero.not.mp (hD w hw).1]
    · filter_upwards [hF] with w hw
      have h := (hD w hw).2
      simp [Defined, eval, Interp.real, hkm, en1, hm0, ivm1R, Fn.csch, (hD w hw).1,
          Real.sinh_eq_zero.not.mp (hD w hw).1] at h ⊢
      exact h
  · filter_upwards with w
    simp [rubi679r19Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkk, Fn.csch]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R, Fn.csch]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r19Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r19Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r19Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r19Nondeg.body =
        (env "e" + env "f" * t) ^ m * ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r19Nondeg, eval, Interp.real, hkm, hkk, ivm1R, Fn.csch]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hZ0 : Real.sinh (env "c" + env "d" * t) ≠ 0 := (hD t hF.self_of_nhds).1
    have hD0 := (hD t hF.self_of_nhds).2
    have ek : ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ k =
        ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        ((Real.sinh (env "c" + env "d" * t))⁻¹) := by
      rw [← zpow_add_one₀ (inv_ne_zero hZ0), sub_add_cancel]
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize ((Real.sinh (env "c" + env "d" * t))⁻¹) ^ (k - 1) = Q1
    generalize Real.sinh (env "c" + env "d" * t) = z at hZ0 hD0 ⊢
    generalize hE : env "a" + env "b" * z = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r20Nondeg -/

theorem rubi679r20Nondeg_real : rubi679r20Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r20Nondeg.conditions rubi679r20Nondeg.body
    rubi679r20Nondeg.result rubi679r20Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi679r20Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r20Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r20Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r20Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r20Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r20Nondeg.body → env "a" +
      env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r20Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R, Fn.sech] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r20Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, hkm, hkk, hm0, hk0, Fn.sech]
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, ivm1R, Fn.sech] at h ⊢
      exact h
  · filter_upwards with w
    simp [rubi679r20Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r20Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkk, Fn.sech]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R, Fn.sech]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r20Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r20Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r20Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r20Nondeg.body =
        (env "e" + env "f" * t) ^ m * ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r20Nondeg, eval, Interp.real, hkm, hkk, ivm1R, Fn.sech]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hZ0 : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hD0 := hD t hF.self_of_nhds
    have ek : ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ k =
        ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        ((Real.cosh (env "c" + env "d" * t))⁻¹) := by
      rw [← zpow_add_one₀ (inv_ne_zero hZ0), sub_add_cancel]
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize ((Real.cosh (env "c" + env "d" * t))⁻¹) ^ (k - 1) = Q1
    generalize Real.cosh (env "c" + env "d" * t) = z at hZ0 hD0 ⊢
    generalize hE : env "a" + env "b" * z = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r1Nondeg -/

theorem rubi679r1Nondeg_real : rubi679r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r1Nondeg.conditions rubi679r1Nondeg.body
    rubi679r1Nondeg.result rubi679r1Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r1Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r1Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r1Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r1Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r1Nondeg.body → env "a" +
      env "b" * Real.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r1Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1]
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, ivm1R] at h ⊢
      exact h
  · filter_upwards with w
    simp [rubi679r1Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.sinh (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, en1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.sinh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r1Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r1Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r1Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.sinh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r1Nondeg, eval, Interp.real, hkm, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hD0 := hD t hF.self_of_nhds
    have ek : (Real.sinh (env "c" + env "d" * t)) ^ k =
        (Real.sinh (env "c" + env "d" * t)) ^ (k - 1) * (Real.sinh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.sinh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.sinh (env "c" + env "d" * t)) ^ (k - 1) = Q1
    generalize Real.sinh (env "c" + env "d" * t) = z at hD0 ⊢
    generalize hE : env "a" + env "b" * z = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r1Nondeg_complex : rubi679r1Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r1Nondeg.conditions rubi679r1Nondeg.body
    rubi679r1Nondeg.result rubi679r1Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r1Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r1Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkk] at h'
    have h'' : (0 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi679r1Nondeg.body →
      env "a" + env "b" * Complex.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r1Nondeg, Defined, eval, Interp.complex, hkm, hkk, hm0, hk0, ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.complex, hkm, en1, hm0, hk1]
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkm, en1, hm0, hk1, ivm1C] at h ⊢
      exact h
  · filter_upwards with w
    simp [rubi679r1Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hl]
  · simp only [rubi679r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Complex.sinh (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, en1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Complex.sinh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Complex.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, en1, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r1Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r1Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi679r1Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Complex.sinh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Complex.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r1Nondeg, eval, Interp.complex, hkm, hkk, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hD0 := hD t hF.self_of_nhds
    have ek : (Complex.sinh (env "c" + env "d" * t)) ^ k =
        (Complex.sinh (env "c" + env "d" * t)) ^ (k - 1) *
        (Complex.sinh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Complex.sinh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Complex.sinh (env "c" + env "d" * t)) ^ (k - 1) = Q1
    generalize Complex.sinh (env "c" + env "d" * t) = z at hD0 ⊢
    generalize hE : env "a" + env "b" * z = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## rubi679r2Nondeg -/

theorem rubi679r2Nondeg_real : rubi679r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r2Nondeg.conditions rubi679r2Nondeg.body
    rubi679r2Nondeg.result rubi679r2Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r2Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r2Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r2Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r2Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r2Nondeg.body → env "a" +
      env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r2Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1]
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, ivm1R] at h ⊢
      exact h
  · filter_upwards with w
    simp [rubi679r2Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.cosh (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, en1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.cosh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r2Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r2Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r2Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.cosh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r2Nondeg, eval, Interp.real, hkm, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hD0 := hD t hF.self_of_nhds
    have ek : (Real.cosh (env "c" + env "d" * t)) ^ k =
        (Real.cosh (env "c" + env "d" * t)) ^ (k - 1) * (Real.cosh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.cosh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.cosh (env "c" + env "d" * t)) ^ (k - 1) = Q1
    generalize Real.cosh (env "c" + env "d" * t) = z at hD0 ⊢
    generalize hE : env "a" + env "b" * z = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r2Nondeg_complex : rubi679r2Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r2Nondeg.conditions rubi679r2Nondeg.body
    rubi679r2Nondeg.result rubi679r2Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r2Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r2Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r2Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r2Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkk] at h'
    have h'' : (0 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi679r2Nondeg.body →
      env "a" + env "b" * Complex.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r2Nondeg, Defined, eval, Interp.complex, hkm, hkk, hm0, hk0, ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.complex, hkm, en1, hm0, hk1]
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, Interp.complex, hkm, en1, hm0, hk1, ivm1C] at h ⊢
      exact h
  · filter_upwards with w
    simp [rubi679r2Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hl]
  · simp only [rubi679r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Complex.cosh (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, en1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Complex.cosh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Complex.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, en1, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r2Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r2Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi679r2Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Complex.cosh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Complex.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r2Nondeg, eval, Interp.complex, hkm, hkk, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hD0 := hD t hF.self_of_nhds
    have ek : (Complex.cosh (env "c" + env "d" * t)) ^ k =
        (Complex.cosh (env "c" + env "d" * t)) ^ (k - 1) *
        (Complex.cosh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Complex.cosh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Complex.cosh (env "c" + env "d" * t)) ^ (k - 1) = Q1
    generalize Complex.cosh (env "c" + env "d" * t) = z at hD0 ⊢
    generalize hE : env "a" + env "b" * z = Dz at hD0 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## Mixed quotients -/

theorem rubi479r15Nondeg_real : rubi479r15Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r15Nondeg.conditions rubi479r15Nondeg.body
    rubi479r15Nondeg.result rubi479r15Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi479r15Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r15Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r15Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r15Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r15Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r15Nondeg.body →
      Real.sin (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Real.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r15Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨hsw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkk, hm0, hk0, hsw] at hDw ⊢
    · filter_upwards [hF] with w hw
      obtain ⟨hsw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, ivm1R, hsw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi479r15Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi479r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.cot (env "c" + env "d" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkk]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        Real.cos (env "c" + env "d" * t) * (Real.cot (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r15Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi479r15Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi479r15Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.cot (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.sin (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r15Nondeg, eval, Interp.real, hkm, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hst, hDt⟩ := hD t hF.self_of_nhds
    have ek : (Real.cot (env "c" + env "d" * t)) ^ k =
        (Real.cot (env "c" + env "d" * t)) ^ (k - 1) * (Real.cot (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.cot (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.cot (env "c" + env "d" * t)) ^ (k - 1) = Q1
    simp only [Real.cot_eq_cos_div_sin]
    generalize hE : env "a" + env "b" * Real.sin (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi479r15Nondeg_complex : rubi479r15Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi479r15Nondeg.conditions rubi479r15Nondeg.body
    rubi479r15Nondeg.result rubi479r15Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi479r15Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r15Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r15Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r15Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r15Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkk] at h'
    have h'' : (0 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi479r15Nondeg.body →
      Complex.sin (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Complex.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r15Nondeg, Defined, eval, Interp.complex, hkm, hkk, hm0, hk0, ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨hsw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.complex, hkm, hkk, hm0, hk0, hsw] at hDw ⊢
    · filter_upwards [hF] with w hw
      obtain ⟨hsw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.complex, hkm, en1, hm0, hk1, ivm1C, hsw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi479r15Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hl]
  · simp only [rubi479r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Complex.cot (env "c" + env "d" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, hkk]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        Complex.cos (env "c" + env "d" * t) * (Complex.cot (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Complex.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, en1, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi479r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r15Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi479r15Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi479r15Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Complex.cot (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Complex.sin (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r15Nondeg, eval, Interp.complex, hkm, hkk, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hst, hDt⟩ := hD t hF.self_of_nhds
    have ek : (Complex.cot (env "c" + env "d" * t)) ^ k =
        (Complex.cot (env "c" + env "d" * t)) ^ (k - 1) * (Complex.cot (env "c" + env "d" * t)) :=
        by
      have := zpow_add_nat_of (Complex.cot (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Complex.cot (env "c" + env "d" * t)) ^ (k - 1) = Q1
    simp only [Complex.cot_eq_cos_div_sin]
    generalize hE : env "a" + env "b" * Complex.sin (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r14Nondeg_real : rubi679r14Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r14Nondeg.conditions rubi679r14Nondeg.body
    rubi679r14Nondeg.result rubi679r14Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi679r14Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r14Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r14Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r14Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r14Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r14Nondeg.body → env "a" +
      env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r14Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain hDw := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkk, hm0, hk0] at hDw ⊢
    · filter_upwards [hF] with w hw
      obtain hDw := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, ivm1R] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r14Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.tanh (env "c" + env "d" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkk]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        Real.sinh (env "c" + env "d" * t) * (Real.tanh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r14Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r14Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r14Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.tanh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r14Nondeg, eval, Interp.real, hkm, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain hDt := hD t hF.self_of_nhds
    have ek : (Real.tanh (env "c" + env "d" * t)) ^ k =
        (Real.tanh (env "c" + env "d" * t)) ^ (k - 1) * (Real.tanh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.tanh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.tanh (env "c" + env "d" * t)) ^ (k - 1) = Q1
    have hz0 : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    simp only [Real.tanh_eq_sinh_div_cosh]
    generalize hE : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r14Nondeg_complex : rubi679r14Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r14Nondeg.conditions rubi679r14Nondeg.body
    rubi679r14Nondeg.result rubi679r14Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi679r14Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r14Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r14Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r14Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkm] at h'
    have h'' : (0 : ℝ) < m := by simpa using h'
    exact_mod_cast h''
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r14Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkk] at h'
    have h'' : (0 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi679r14Nondeg.body →
      Complex.cosh (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Complex.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r14Nondeg, Defined, eval, Interp.complex, hkm, hkk, hm0, hk0, ivm1C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨hcw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.complex, hkm, hkk, hm0, hk0, hcw] at hDw ⊢
    · filter_upwards [hF] with w hw
      obtain ⟨hcw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.complex, hkm, en1, hm0, hk1, ivm1C, hcw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r14Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hl]
  · simp only [rubi679r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Complex.tanh (env "c" + env "d" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkm, hkk]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        Complex.sinh (env "c" + env "d" * t) * (Complex.tanh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Complex.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, en1, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r14Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r14Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi679r14Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Complex.tanh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Complex.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r14Nondeg, eval, Interp.complex, hkm, hkk, ivm1C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hct, hDt⟩ := hD t hF.self_of_nhds
    have ek : (Complex.tanh (env "c" + env "d" * t)) ^ k =
        (Complex.tanh (env "c" + env "d" * t)) ^ (k - 1) *
        (Complex.tanh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Complex.tanh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Complex.tanh (env "c" + env "d" * t)) ^ (k - 1) = Q1
    simp only [Complex.tanh_eq_sinh_div_cosh]
    generalize hE : env "a" + env "b" * Complex.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r13Nondeg_real : rubi679r13Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r13Nondeg.conditions rubi679r13Nondeg.body
    rubi679r13Nondeg.result rubi679r13Nondeg.integrals
  intro env hc t hF
  have hl : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi679r13Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r13Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r13Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r13Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r13Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r13Nondeg.body → env "c" +
      env "d" * w ≠ 0 ∧ env "a" + env "b" * Real.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r13Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R, Fn.coth] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨huw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, hkk, hm0, hk0, Fn.coth, huw] at hDw ⊢
    · filter_upwards [hF] with w hw
      obtain ⟨huw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, ivm1R, Fn.coth, huw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r13Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, hkk, Fn.coth]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        Real.cosh (env "c" + env "d" * t) * ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R, Fn.coth]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r13Nondeg.result) = fun w => (env "a")⁻¹ * Φ "I1" w +
            -(env "b" * (env "a")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r13Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r13Nondeg.body =
        (env "e" + env "f" * t) ^ m * ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r13Nondeg, eval, Interp.real, hkm, hkk, ivm1R, Fn.coth]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hut, hDt⟩ := hD t hF.self_of_nhds
    have ek : ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k =
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) := by
      have := zpow_add_nat_of ((Real.tanh (env "c" + env "d" * t))⁻¹) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1) = Q1
    have hz0 : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hz1 : Real.sinh (env "c" + env "d" * t) ≠ 0 := fun h => hut (Real.sinh_eq_zero.mp h)
    simp only [Real.tanh_eq_sinh_div_cosh]
    generalize hE : env "a" + env "b" * Real.sinh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi479r13Nondeg_real : rubi479r13Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r13Nondeg.conditions rubi479r13Nondeg.body
    rubi479r13Nondeg.result rubi479r13Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi479r13Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r13Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r13Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r13Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r13Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r13Nondeg.body →
      Real.cos (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Real.sin (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r13Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨hcw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, hcw] at hDw ⊢
    · filter_upwards [hF] with w hw
      obtain ⟨hcw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, ivm1R, hcw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi479r13Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi479r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.cos (env "c" + env "d" * t))⁻¹ * (Real.tan (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, en1, Fn.sec]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.cos (env "c" + env "d" * t))⁻¹ * (Real.tan (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.sin (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R, Fn.sec]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r13Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi479r13Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi479r13Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.tan (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.sin (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r13Nondeg, eval, Interp.real, hkm, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hct, hDt⟩ := hD t hF.self_of_nhds
    have ek : (Real.tan (env "c" + env "d" * t)) ^ k =
        (Real.tan (env "c" + env "d" * t)) ^ (k - 1) * (Real.tan (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.tan (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.tan (env "c" + env "d" * t)) ^ (k - 1) = Q1
    simp only [Real.tan_eq_sin_div_cos]
    generalize hE : env "a" + env "b" * Real.sin (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi479r14Nondeg_real : rubi479r14Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r14Nondeg.conditions rubi479r14Nondeg.body
    rubi479r14Nondeg.result rubi479r14Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi479r14Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r14Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r14Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi479r14Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r14Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r14Nondeg.body →
      Real.sin (env "c" + env "d" * w) ≠ 0 ∧ env "a" + env "b" *
      Real.cos (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi479r14Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨hsw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, hsw] at hDw ⊢
    · filter_upwards [hF] with w hw
      obtain ⟨hsw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, ivm1R, hsw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi479r14Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi479r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.sin (env "c" + env "d" * t))⁻¹ * (Real.cot (env "c" + env "d" * t)) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, en1, Fn.csc]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.sin (env "c" + env "d" * t))⁻¹ * (Real.cot (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.cos (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi479r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi479r14Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi479r14Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi479r14Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.cot (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.cos (env "c" + env "d" * t))⁻¹ := by
      simp [rubi479r14Nondeg, eval, Interp.real, hkm, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hst, hDt⟩ := hD t hF.self_of_nhds
    have ek : (Real.cot (env "c" + env "d" * t)) ^ k =
        (Real.cot (env "c" + env "d" * t)) ^ (k - 1) * (Real.cot (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.cot (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.cot (env "c" + env "d" * t)) ^ (k - 1) = Q1
    simp only [Real.cot_eq_cos_div_sin]
    generalize hE : env "a" + env "b" * Real.cos (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r11Nondeg_real : rubi679r11Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r11Nondeg.conditions rubi679r11Nondeg.body
    rubi679r11Nondeg.result rubi679r11Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r11Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r11Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r11Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r11Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r11Nondeg.body → env "a" +
      env "b" * Real.sinh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r11Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain hDw := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1] at hDw ⊢
    · filter_upwards [hF] with w hw
      obtain hDw := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, ivm1R] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r11Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.cosh (env "c" + env "d" * t))⁻¹ * (Real.tanh (env "c" + env "d" * t)) ^ (k - 1)) t :=
        by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, en1, Fn.sech]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.cosh (env "c" + env "d" * t))⁻¹ * (Real.tanh (env "c" + env "d" * t)) ^ (k - 1) *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R, Fn.sech]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r11Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r11Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r11Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r11Nondeg.body =
        (env "e" + env "f" * t) ^ m * (Real.tanh (env "c" + env "d" * t)) ^ k *
        (env "a" + env "b" * Real.sinh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r11Nondeg, eval, Interp.real, hkm, hkk, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain hDt := hD t hF.self_of_nhds
    have ek : (Real.tanh (env "c" + env "d" * t)) ^ k =
        (Real.tanh (env "c" + env "d" * t)) ^ (k - 1) * (Real.tanh (env "c" + env "d" * t)) := by
      have := zpow_add_nat_of (Real.tanh (env "c" + env "d" * t)) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize (Real.tanh (env "c" + env "d" * t)) ^ (k - 1) = Q1
    have hz0 : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    simp only [Real.tanh_eq_sinh_div_cosh]
    generalize hE : env "a" + env "b" * Real.sinh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi679r12Nondeg_real : rubi679r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r12Nondeg.conditions rubi679r12Nondeg.body
    rubi679r12Nondeg.result rubi679r12Nondeg.integrals
  intro env hc t hF
  have hl : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi679r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r12Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi679r12Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hmpos : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi679r12Nondeg])
    have h' : (0 : ℝ) < env "m" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkm] at h'
    exact_mod_cast h'
  have hkpos : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi679r12Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkk] at h'
    exact_mod_cast h'
  have hm0 : ¬ m < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi679r12Nondeg.body → env "c" +
      env "d" * w ≠ 0 ∧ env "a" + env "b" * Real.cosh (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi679r12Nondeg, Defined, eval, Interp.real, hkm, hkk, hm0, hk0, ivm1R, Fn.coth] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      obtain ⟨huw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, Fn.coth, huw] at hDw ⊢
    · filter_upwards [hF] with w hw
      obtain ⟨huw, hDw⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkm, en1, hm0, hk1, ivm1R, Fn.coth, huw] at hDw ⊢
      try tauto
  · filter_upwards with w
    simp [rubi679r12Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hl]
  · simp only [rubi679r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ m *
        (Real.sinh (env "c" + env "d" * t))⁻¹ *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, en1, Fn.coth, Fn.csch]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "e" + env "f" * t) ^ m *
        (Real.sinh (env "c" + env "d" * t))⁻¹ * ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, en1, ivm1R, Fn.coth, Fn.csch]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r12Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi679r12Nondeg.result) = fun w => (env "b")⁻¹ * Φ "I1" w +
            -(env "a" * (env "b")⁻¹) * Φ "I2" w := by
      funext w
      simp [rubi679r12Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi679r12Nondeg.body =
        (env "e" + env "f" * t) ^ m * ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k *
        (env "a" + env "b" * Real.cosh (env "c" + env "d" * t))⁻¹ := by
      simp [rubi679r12Nondeg, eval, Interp.real, hkm, hkk, ivm1R, Fn.coth]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    obtain ⟨hut, hDt⟩ := hD t hF.self_of_nhds
    have ek : ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ k =
        ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1) *
        ((Real.tanh (env "c" + env "d" * t))⁻¹) := by
      have := zpow_add_nat_of ((Real.tanh (env "c" + env "d" * t))⁻¹) (k - 1) 1 (by omega)
      rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring, pow_one] at this
    rw [ek]
    generalize (env "e" + env "f" * t) ^ m = Q
    generalize ((Real.tanh (env "c" + env "d" * t))⁻¹) ^ (k - 1) = Q1
    have hz0 : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hz1 : Real.sinh (env "c" + env "d" * t) ≠ 0 := fun h => hut (Real.sinh_eq_zero.mp h)
    simp only [Real.tanh_eq_sinh_div_cosh]
    generalize hE : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) = Dz at hDt ⊢
    field_simp
    rw [← hE]
    ring

end OSR.IntegrationRec255
