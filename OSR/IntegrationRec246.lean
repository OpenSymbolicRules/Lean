import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants over ℝ and ℂ

Proofs over ℝ and ℂ of RUBI 4.1.10 #1 (the integration by parts of `(c + d x)^m sin(e + f x)`),
4.1.7 #3 (the split of `(A + B sin^2 u) / (a + b sin^2 u)`) and 4.3.1.1 #1 (the reduction of
`(b tan(c + d x))^n` for an integer `n > 1`). -/

namespace OSR.IntegrationRec246

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

/-! ## RUBI 4.1.10 #1 -/

theorem rubi4110r1Nondeg_real : rubi4110r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4110r1Nondeg.conditions rubi4110r1Nondeg.body
    rubi4110r1Nondeg.result rubi4110r1Nondeg.integrals
  intro env hc t hF
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi4110r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4110r1Nondeg, Defined, eval, Interp.real, hkm] at h
  have hm : env "m" = (j : _) := (intValue?_eq _ _).1 hkm
  have hgt : (0 : ℝ) < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi4110r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hjpos : 0 < j := by
    rw [hm] at hgt; exact_mod_cast hgt
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have em1 : intValue? (env "m" + -1) = some (j - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4110r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards with w
    simp [Defined, eval, Interp.real, em1, hj1]
  · filter_upwards with w
    simp [rubi4110r1Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkm, hj0, hf]
  · simp only [rubi4110r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "c" + env "d" * t) ^ (j - 1) *
        Real.cos (env "e" + env "f" * t)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4110r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4110r1Nondeg.result) =
        fun w => -(env "c" + env "d" * w) ^ j * Real.cos (env "e" + env "f" * w) * (env "f")⁻¹ +
          env "d" * env "m" * (env "f")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4110r1Nondeg, eval, recEnv, Interp.real, ivm1R, hkm]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4110r1Nondeg.body =
        (env "c" + env "d" * t) ^ j * Real.sin (env "e" + env "f" * t) := by
      simp [rubi4110r1Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hL : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
    have hL2 : HasDerivAt (fun w => env "e" + env "f" * w) (env "f") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "f")).const_add (env "e")
    have hP := (hasDerivAt_zpow j _ (Or.inr (by omega))).comp t hL
    have hC := (Real.hasDerivAt_cos _).comp t hL2
    refine ((((hP.neg).mul hC).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.neg_apply]
    rw [show ((j : ℤ) : _) = env "m" from hm.symm]
    field_simp
    ring

theorem rubi4110r1Nondeg_complex : rubi4110r1Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4110r1Nondeg.conditions rubi4110r1Nondeg.body
    rubi4110r1Nondeg.result rubi4110r1Nondeg.integrals
  intro env hc t hF
  have hf : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi4110r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4110r1Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hm : env "m" = (j : _) := (intValue?_eq _ _).1 hkm
  have hgt : (0 : ℝ) < (env "m").re := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi4110r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    exact h.2
  have hjpos : 0 < j := by
    rw [hm] at hgt; simpa using hgt
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have em1 : intValue? (env "m" + -1) = some (j - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4110r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards with w
    simp [Defined, eval, Interp.complex, em1, hj1]
  · filter_upwards with w
    simp [rubi4110r1Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkm, hj0, hf]
  · simp only [rubi4110r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "c" + env "d" * t) ^ (j - 1) *
        Complex.cos (env "e" + env "f" * t)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4110r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4110r1Nondeg.result) =
        fun w => -(env "c" + env "d" * w) ^ j * Complex.cos (env "e" + env "f" * w) * (env "f")⁻¹ +
          env "d" * env "m" * (env "f")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4110r1Nondeg, eval, recEnv, Interp.complex, ivm1C, hkm]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4110r1Nondeg.body =
        (env "c" + env "d" * t) ^ j * Complex.sin (env "e" + env "f" * t) := by
      simp [rubi4110r1Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hL : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
    have hL2 : HasDerivAt (fun w => env "e" + env "f" * w) (env "f") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "f")).const_add (env "e")
    have hP := (hasDerivAt_zpow j _ (Or.inr (by omega))).comp t hL
    have hC := (Complex.hasDerivAt_cos _).comp t hL2
    refine ((((hP.neg).mul hC).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.neg_apply]
    rw [show ((j : ℤ) : _) = env "m" from hm.symm]
    field_simp
    ring

/-! ## RUBI 4.1.7 #3 -/

theorem rubi417r3Nondeg_real : rubi417r3Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi417r3Nondeg.conditions rubi417r3Nondeg.body
    rubi417r3Nondeg.result rubi417r3Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi417r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi417r3Nondeg.body →
      env "a" + env "b" * Real.sin (env "e" + env "f" * w) ^ 2 ≠ 0 := by
    intro w h
    simpa [rubi417r3Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] using h
  have hq0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi417r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simpa [Defined, eval, Interp.real, ivm1R, iv2R] using hD w hw
  · filter_upwards with w
    simp [rubi417r3Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi417r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "a" + env "b" * Real.sin (env "e" + env "f" * t) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ivm1R, iv2R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi417r3Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi417r3Nondeg.result) =
        fun w => env "B" * w * (env "b")⁻¹ +
          (env "A" * env "b" - env "a" * env "B") * (env "b")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi417r3Nondeg, eval, recEnv, Interp.real, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi417r3Nondeg.body =
        (env "A" + env "B" * Real.sin (env "e" + env "f" * t) ^ 2) *
          (env "a" + env "b" * Real.sin (env "e" + env "f" * t) ^ 2)⁻¹ := by
      simp [rubi417r3Nondeg, eval, Interp.real, ivm1R, iv2R]
    rw [hfun, hEF]
    refine ((((hasDerivAt_id t).const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    generalize Real.sin (env "e" + env "f" * t) = S at hq0 ⊢
    generalize hE : env "a" + env "b" * S ^ 2 = D at hq0 ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi417r3Nondeg_complex : rubi417r3Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi417r3Nondeg.conditions rubi417r3Nondeg.body
    rubi417r3Nondeg.result rubi417r3Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi417r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi417r3Nondeg.body →
      env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ^ 2 ≠ 0 := by
    intro w h
    simpa [rubi417r3Nondeg, Defined, eval, Interp.complex, ivm1C, iv2C] using h
  have hq0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi417r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simpa [Defined, eval, Interp.complex, ivm1C, iv2C] using hD w hw
  · filter_upwards with w
    simp [rubi417r3Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hb]
  · simp only [rubi417r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, ivm1C, iv2C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi417r3Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi417r3Nondeg.result) =
        fun w => env "B" * w * (env "b")⁻¹ +
          (env "A" * env "b" - env "a" * env "B") * (env "b")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi417r3Nondeg, eval, recEnv, Interp.complex, ivm1C,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.complex (Function.update env "x" t) rubi417r3Nondeg.body =
        (env "A" + env "B" * Complex.sin (env "e" + env "f" * t) ^ 2) *
          (env "a" + env "b" * Complex.sin (env "e" + env "f" * t) ^ 2)⁻¹ := by
      simp [rubi417r3Nondeg, eval, Interp.complex, ivm1C, iv2C]
    rw [hfun, hEF]
    refine ((((hasDerivAt_id t).const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    generalize Complex.sin (env "e" + env "f" * t) = S at hq0 ⊢
    generalize hE : env "a" + env "b" * S ^ 2 = D at hq0 ⊢
    field_simp
    rw [← hE]
    ring

/-! ## RUBI 4.3.1.1 #1 -/

theorem rubi4311r1Nondeg_real : rubi4311r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4311r1Nondeg.conditions rubi4311r1Nondeg.body
    rubi4311r1Nondeg.result rubi4311r1Nondeg.integrals
  intro env hc t hF
  have hW : env "d" * (env "n" + -1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "n") (.app2 .mul (.int (-1))
      (.int 1)))) (.int 0)) (by simp [rubi4311r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hd, hn1⟩ := hW'
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4311r1Nondeg, Defined, eval, Interp.real, hkn] at h
  have hn : env "n" = (j : _) := (intValue?_eq _ _).1 hkn
  have hgt : (1 : ℝ) < env "n" := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi4311r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hjpos : 1 < j := by
    rw [hn] at hgt; exact_mod_cast hgt
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have hj2 : ¬ j - 2 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (j - 1) :=
    (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have en2 : intValue? (env "n" + -2) = some (j - 2) :=
    (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4311r1Nondeg.body →
      Real.cos (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi4311r1Nondeg, Defined, eval, Interp.real, hkn, hj0] at h
    exact h
  have hc0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4311r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [Defined, eval, Interp.real, en2, hj2, hD w hw]
  · filter_upwards [hF] with w hw
    simp [rubi4311r1Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, en1,
      hj1, hd, hn1, hD w hw]
  · simp only [rubi4311r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" * Real.tan (env "c" + env "d" * t)) ^ (j - 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, en2]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4311r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4311r1Nondeg.result) =
        fun w => env "b" * (env "b" * Real.tan (env "c" + env "d" * w)) ^ (j - 1) *
            (env "d" * (env "n" + -1))⁻¹ + -env "b" ^ 2 * Φ "I1" w := by
      funext w
      simp [rubi4311r1Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R, en1]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4311r1Nondeg.body =
        (env "b" * Real.tan (env "c" + env "d" * t)) ^ j := by
      simp [rubi4311r1Nondeg, eval, Interp.real, hkn]
    rw [hfun, hEF]
    have hL : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
    have hT := ((Real.hasDerivAt_tan hc0).comp t hL).const_mul (env "b")
    have hP := (hasDerivAt_zpow (j - 1) _ (Or.inr (by omega))).comp t hT
    refine (((hP.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    have e2 : (env "b" * Real.tan (env "c" + env "d" * t)) ^ j =
        (env "b" * Real.tan (env "c" + env "d" * t)) ^ (j - 2) *
          (env "b" * Real.tan (env "c" + env "d" * t)) ^ 2 := by
      have := zpow_add_nat_of (env "b" * Real.tan (env "c" + env "d" * t)) (j - 2) 2 (by omega)
      rwa [show j - 2 + ((2 : ℕ) : ℤ) = j by push_cast; ring] at this
    rw [e2, show j - 1 - 1 = j - 2 by ring]
    have hjr : ((j - 1 : ℤ) : _) = env "n" + -1 := by rw [hn]; push_cast; ring
    rw [hjr]
    have hsc := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    rw [Real.tan_eq_sin_div_cos]
    generalize (env "b" * (Real.sin (env "c" + env "d" * t) /
      Real.cos (env "c" + env "d" * t))) ^ (j - 2) = Q
    generalize Real.sin (env "c" + env "d" * t) = S at hsc ⊢
    generalize Real.cos (env "c" + env "d" * t) = C at hc0 hsc ⊢
    field_simp
    linear_combination (-(env "b" ^ 2 * Q)) * hsc

theorem rubi4311r1Nondeg_complex : rubi4311r1Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4311r1Nondeg.conditions rubi4311r1Nondeg.body
    rubi4311r1Nondeg.result rubi4311r1Nondeg.integrals
  intro env hc t hF
  have hW : env "d" * (env "n" + -1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "n") (.app2 .mul (.int (-1))
      (.int 1)))) (.int 0)) (by simp [rubi4311r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hd, hn1⟩ := hW'
  rcases hkn : intValue? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4311r1Nondeg, Defined, eval, Interp.complex, hkn] at h
  have hn : env "n" = (j : _) := (intValue?_eq _ _).1 hkn
  have hgt : (1 : ℝ) < (env "n").re := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi4311r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    exact h.2
  have hjpos : 1 < j := by
    rw [hn] at hgt
    have h1 : (1 : ℝ) < j := by simpa using hgt
    exact_mod_cast h1
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have hj2 : ¬ j - 2 < 0 := by omega
  have en1 : intValue? (env "n" + -1) = some (j - 1) :=
    (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have en2 : intValue? (env "n" + -2) = some (j - 2) :=
    (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4311r1Nondeg.body →
      Complex.cos (env "c" + env "d" * w) ≠ 0 := by
    intro w h
    simp [rubi4311r1Nondeg, Defined, eval, Interp.complex, hkn, hj0] at h
    exact h
  have hc0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4311r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [Defined, eval, Interp.complex, en2, hj2, hD w hw]
  · filter_upwards [hF] with w hw
    simp [rubi4311r1Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, en1,
      hj1, hd, hn1, hD w hw]
  · simp only [rubi4311r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" * Complex.tan (env "c" + env "d" * t)) ^ (j - 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, en2]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4311r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4311r1Nondeg.result) =
        fun w => env "b" * (env "b" * Complex.tan (env "c" + env "d" * w)) ^ (j - 1) *
            (env "d" * (env "n" + -1))⁻¹ + -env "b" ^ 2 * Φ "I1" w := by
      funext w
      simp [rubi4311r1Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C, en1]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4311r1Nondeg.body =
        (env "b" * Complex.tan (env "c" + env "d" * t)) ^ j := by
      simp [rubi4311r1Nondeg, eval, Interp.complex, hkn]
    rw [hfun, hEF]
    have hL : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
    have hT := ((Complex.hasDerivAt_tan hc0).comp t hL).const_mul (env "b")
    have hP := (hasDerivAt_zpow (j - 1) _ (Or.inr (by omega))).comp t hT
    refine (((hP.const_mul _).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    have e2 : (env "b" * Complex.tan (env "c" + env "d" * t)) ^ j =
        (env "b" * Complex.tan (env "c" + env "d" * t)) ^ (j - 2) *
          (env "b" * Complex.tan (env "c" + env "d" * t)) ^ 2 := by
      have := zpow_add_nat_of (env "b" * Complex.tan (env "c" + env "d" * t)) (j - 2) 2 (by omega)
      rwa [show j - 2 + ((2 : ℕ) : ℤ) = j by push_cast; ring] at this
    rw [e2, show j - 1 - 1 = j - 2 by ring]
    have hjr : ((j - 1 : ℤ) : _) = env "n" + -1 := by rw [hn]; push_cast; ring
    rw [hjr]
    have hsc := Complex.sin_sq_add_cos_sq (env "c" + env "d" * t)
    rw [Complex.tan_eq_sin_div_cos]
    generalize (env "b" * (Complex.sin (env "c" + env "d" * t) /
      Complex.cos (env "c" + env "d" * t))) ^ (j - 2) = Q
    generalize Complex.sin (env "c" + env "d" * t) = S at hsc ⊢
    generalize Complex.cos (env "c" + env "d" * t) = C at hc0 hsc ⊢
    field_simp
    linear_combination (-(env "b" ^ 2 * Q)) * hsc

/-! ## RUBI 4.7.9 #47 and #48 -/

theorem rubi479r47Nondeg_real : rubi479r47Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi479r47Nondeg.conditions
    rubi479r47Nondeg.body rubi479r47Nondeg.result rubi479r47Nondeg.integrals
    rubi479r47Nondeg.substs
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi479r47Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r47Nondeg, Defined, eval, Interp.real, hkn] at h
  have hk : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r47Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkn] at h'
    exact_mod_cast h'
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r47Nondeg.body →
      env "c" + env "d" * w ≠ 0 := by
    intro w h
    simp [rubi479r47Nondeg, Defined, eval, Interp.real, hkn, ivm1R] at h
    tauto
  have hL0 := hD t hF.self_of_nhds
  have hu0 : (env "c" + env "d" * t)⁻¹ ≠ 0 := inv_ne_zero hL0
  have hsub : substAt Interp.real env rubi479r47Nondeg.substs "x" "I1" t =
      (env "c" + env "d" * t)⁻¹ := by
    simp [rubi479r47Nondeg, substAt, eval, Interp.real, ivm1R]
  have hpos : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t)⁻¹, u ≠ 0 := eventually_ne_nhds hu0
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi479r47Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi479r47Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.real, ivm1R, hD w hw]
    · rw [hsub]
      filter_upwards [hpos] with u hu
      simp [Defined, eval, Interp.real, hkn, ivm1R, iv2R, hu, hk0]
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi479r47Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hd]
    · simp only [rubi479r47Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          (Real.sin (env "a" * (env "c" + env "d" * t)⁻¹) ^ k * ((env "c" + env "d" * t) ^ 2))
          (env "c" + env "d" * t)⁻¹ := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkn, ivm1R, iv2R]
      have hL : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
      have h := (hΦ'.comp t (hL.inv hL0)).const_mul (-(env "d")⁻¹)
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi479r47Nondeg.integrals.map (·.1))
            rubi479r47Nondeg.substs Φ "x" w) rubi479r47Nondeg.result) =
          fun w => -(env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w)⁻¹ := by
        funext w
        simp [rubi479r47Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      refine h.congr_deriv ?_
      have hEF : eval Interp.real (Function.update env "x" t) rubi479r47Nondeg.body =
          Real.sin (env "a" * (env "c" + env "d" * t)⁻¹) ^ k := by
        simp [rubi479r47Nondeg, eval, Interp.real, hkn, ivm1R]
      rw [hEF]
      generalize Real.sin (env "a" * (env "c" + env "d" * t)⁻¹) ^ k = R
      field_simp

theorem rubi479r47Nondeg_complex : rubi479r47Nondeg.Holds .complex := by
  show AntiderivSubstHolds Interp.complex "x" rubi479r47Nondeg.conditions
    rubi479r47Nondeg.body rubi479r47Nondeg.result rubi479r47Nondeg.integrals
    rubi479r47Nondeg.substs
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi479r47Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r47Nondeg, Defined, eval, Interp.complex, hkn] at h
  have hk : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r47Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkn] at h'
    have h'' : (0 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi479r47Nondeg.body →
      env "c" + env "d" * w ≠ 0 := by
    intro w h
    simp [rubi479r47Nondeg, Defined, eval, Interp.complex, hkn, ivm1C] at h
    tauto
  have hL0 := hD t hF.self_of_nhds
  have hu0 : (env "c" + env "d" * t)⁻¹ ≠ 0 := inv_ne_zero hL0
  have hsub : substAt Interp.complex env rubi479r47Nondeg.substs "x" "I1" t =
      (env "c" + env "d" * t)⁻¹ := by
    simp [rubi479r47Nondeg, substAt, eval, Interp.complex, ivm1C]
  have hpos : ∀ᶠ u : ℂ in 𝓝 (env "c" + env "d" * t)⁻¹, u ≠ 0 := eventually_ne_nhds hu0
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi479r47Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi479r47Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.complex, ivm1C, hD w hw]
    · rw [hsub]
      filter_upwards [hpos] with u hu
      simp [Defined, eval, Interp.complex, hkn, ivm1C, iv2C, hu, hk0]
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi479r47Nondeg, Defined, eval, Interp.complex, substEnv, ivm1C, hd]
    · simp only [rubi479r47Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          (Complex.sin (env "a" * (env "c" + env "d" * t)⁻¹) ^ k * ((env "c" + env "d" * t) ^ 2))
          (env "c" + env "d" * t)⁻¹ := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.complex, hkn, ivm1C, iv2C]
      have hL : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
      have h := (hΦ'.comp t (hL.inv hL0)).const_mul (-(env "d")⁻¹)
      have hfun : (fun w => eval Interp.complex
          (substEnv Interp.complex env (rubi479r47Nondeg.integrals.map (·.1))
            rubi479r47Nondeg.substs Φ "x" w) rubi479r47Nondeg.result) =
          fun w => -(env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w)⁻¹ := by
        funext w
        simp [rubi479r47Nondeg, substEnv, substAt, eval, Interp.complex, ivm1C]
      rw [hfun]
      refine h.congr_deriv ?_
      have hEF : eval Interp.complex (Function.update env "x" t) rubi479r47Nondeg.body =
          Complex.sin (env "a" * (env "c" + env "d" * t)⁻¹) ^ k := by
        simp [rubi479r47Nondeg, eval, Interp.complex, hkn, ivm1C]
      rw [hEF]
      generalize Complex.sin (env "a" * (env "c" + env "d" * t)⁻¹) ^ k = R
      field_simp

theorem rubi479r48Nondeg_real : rubi479r48Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi479r48Nondeg.conditions
    rubi479r48Nondeg.body rubi479r48Nondeg.result rubi479r48Nondeg.integrals
    rubi479r48Nondeg.substs
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi479r48Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r48Nondeg, Defined, eval, Interp.real, hkn] at h
  have hk : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r48Nondeg])
    have h' : (0 : ℝ) < env "n" := by simpa [Cond.Holds, Defined, eval, Interp.real] using h
    rw [(intValue?_eq _ _).1 hkn] at h'
    exact_mod_cast h'
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi479r48Nondeg.body →
      env "c" + env "d" * w ≠ 0 := by
    intro w h
    simp [rubi479r48Nondeg, Defined, eval, Interp.real, hkn, ivm1R] at h
    tauto
  have hL0 := hD t hF.self_of_nhds
  have hu0 : (env "c" + env "d" * t)⁻¹ ≠ 0 := inv_ne_zero hL0
  have hsub : substAt Interp.real env rubi479r48Nondeg.substs "x" "I1" t =
      (env "c" + env "d" * t)⁻¹ := by
    simp [rubi479r48Nondeg, substAt, eval, Interp.real, ivm1R]
  have hpos : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t)⁻¹, u ≠ 0 := eventually_ne_nhds hu0
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi479r48Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi479r48Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.real, ivm1R, hD w hw]
    · rw [hsub]
      filter_upwards [hpos] with u hu
      simp [Defined, eval, Interp.real, hkn, ivm1R, iv2R, hu, hk0]
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi479r48Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hd]
    · simp only [rubi479r48Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          (Real.cos (env "a" * (env "c" + env "d" * t)⁻¹) ^ k * ((env "c" + env "d" * t) ^ 2))
          (env "c" + env "d" * t)⁻¹ := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkn, ivm1R, iv2R]
      have hL : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
      have h := (hΦ'.comp t (hL.inv hL0)).const_mul (-(env "d")⁻¹)
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi479r48Nondeg.integrals.map (·.1))
            rubi479r48Nondeg.substs Φ "x" w) rubi479r48Nondeg.result) =
          fun w => -(env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w)⁻¹ := by
        funext w
        simp [rubi479r48Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      refine h.congr_deriv ?_
      have hEF : eval Interp.real (Function.update env "x" t) rubi479r48Nondeg.body =
          Real.cos (env "a" * (env "c" + env "d" * t)⁻¹) ^ k := by
        simp [rubi479r48Nondeg, eval, Interp.real, hkn, ivm1R]
      rw [hEF]
      generalize Real.cos (env "a" * (env "c" + env "d" * t)⁻¹) ^ k = R
      field_simp

theorem rubi479r48Nondeg_complex : rubi479r48Nondeg.Holds .complex := by
  show AntiderivSubstHolds Interp.complex "x" rubi479r48Nondeg.conditions
    rubi479r48Nondeg.body rubi479r48Nondeg.result rubi479r48Nondeg.integrals
    rubi479r48Nondeg.substs
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi479r48Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi479r48Nondeg, Defined, eval, Interp.complex, hkn] at h
  have hk : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi479r48Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    have h' := h.2
    rw [(intValue?_eq _ _).1 hkn] at h'
    have h'' : (0 : ℝ) < k := by simpa using h'
    exact_mod_cast h''
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi479r48Nondeg.body →
      env "c" + env "d" * w ≠ 0 := by
    intro w h
    simp [rubi479r48Nondeg, Defined, eval, Interp.complex, hkn, ivm1C] at h
    tauto
  have hL0 := hD t hF.self_of_nhds
  have hu0 : (env "c" + env "d" * t)⁻¹ ≠ 0 := inv_ne_zero hL0
  have hsub : substAt Interp.complex env rubi479r48Nondeg.substs "x" "I1" t =
      (env "c" + env "d" * t)⁻¹ := by
    simp [rubi479r48Nondeg, substAt, eval, Interp.complex, ivm1C]
  have hpos : ∀ᶠ u : ℂ in 𝓝 (env "c" + env "d" * t)⁻¹, u ≠ 0 := eventually_ne_nhds hu0
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi479r48Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi479r48Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.complex, ivm1C, hD w hw]
    · rw [hsub]
      filter_upwards [hpos] with u hu
      simp [Defined, eval, Interp.complex, hkn, ivm1C, iv2C, hu, hk0]
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi479r48Nondeg, Defined, eval, Interp.complex, substEnv, ivm1C, hd]
    · simp only [rubi479r48Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          (Complex.cos (env "a" * (env "c" + env "d" * t)⁻¹) ^ k * ((env "c" + env "d" * t) ^ 2))
          (env "c" + env "d" * t)⁻¹ := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.complex, hkn, ivm1C, iv2C]
      have hL : HasDerivAt (fun w => env "c" + env "d" * w) (env "d") t := by
        simpa using ((hasDerivAt_id t).const_mul (env "d")).const_add (env "c")
      have h := (hΦ'.comp t (hL.inv hL0)).const_mul (-(env "d")⁻¹)
      have hfun : (fun w => eval Interp.complex
          (substEnv Interp.complex env (rubi479r48Nondeg.integrals.map (·.1))
            rubi479r48Nondeg.substs Φ "x" w) rubi479r48Nondeg.result) =
          fun w => -(env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w)⁻¹ := by
        funext w
        simp [rubi479r48Nondeg, substEnv, substAt, eval, Interp.complex, ivm1C]
      rw [hfun]
      refine h.congr_deriv ?_
      have hEF : eval Interp.complex (Function.update env "x" t) rubi479r48Nondeg.body =
          Complex.cos (env "a" * (env "c" + env "d" * t)⁻¹) ^ k := by
        simp [rubi479r48Nondeg, eval, Interp.complex, hkn, ivm1C]
      rw [hEF]
      generalize Complex.cos (env "a" * (env "c" + env "d" * t)⁻¹) ^ k = R
      field_simp

end OSR.IntegrationRec246
