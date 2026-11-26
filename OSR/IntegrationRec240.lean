import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic sine rules over `sqrt(d + e x^2)`

Proofs over ℝ of RUBI 7.1.3 #2 (`∫ (a + b arsinh(c x))^n / sqrt(d + e x^2) dx` in closed form
when `e = c^2 d`, where `sqrt(1 + c^2 x^2) / sqrt(d + e x^2) = 1 / sqrt d` because the domain
forces `d > 0`), 7.1.4 #23 (the integration by parts of `x (d + e x^2)^p (a + b arsinh(c x))`)
and 7.1.5 #11 (the integration by parts of
`(f + g x)^m (a + b arsinh(c x))^n / sqrt(d + e x^2)` for `n < -1`). The complex statements are
vacuous (no complex interpretation of `transc1#arcsinh` or `arith1#root`) and stay unproved. -/

namespace OSR.IntegrationRec240

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin (a b t : ℝ) : HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

private theorem hasDerivAt_quad0 (d e t : ℝ) :
    HasDerivAt (fun w => d + e * w ^ 2) (e * (2 * t)) t := by
  have := ((hasDerivAt_pow 2 t).const_mul e).const_add d
  simpa using this

/-- `arsinh (c x)` has derivative `c / sqrt(1 + c^2 x^2)`. -/
private theorem hasDerivAt_arsinh_mul (c t : ℝ) :
    HasDerivAt (fun w => Real.arsinh (c * w)) (c * (Real.sqrt (1 + c ^ 2 * t ^ 2))⁻¹) t := by
  have h := (Real.hasDerivAt_arsinh (c * t)).comp t ((hasDerivAt_id' t).const_mul c)
  refine h.congr_deriv ?_
  rw [mul_pow]; ring

/-- With `e = c^2 d` and `d ≥ 0`, `sqrt(d + e x^2) = sqrt d sqrt(1 + c^2 x^2)`. -/
private theorem sqrt_factor {c d e : ℝ} (hrel : e = c ^ 2 * d) (hd : 0 ≤ d) (w : ℝ) :
    Real.sqrt (d + e * w ^ 2) = Real.sqrt d * Real.sqrt (1 + c ^ 2 * w ^ 2) := by
  rw [← Real.sqrt_mul hd, hrel]
  congr 1
  ring

/-! ## RUBI 7.1.3 #2 -/

theorem rubi713r2Nondeg_real : rubi713r2Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi713r2Nondeg.conditions rubi713r2Nondeg.body
    rubi713r2Nondeg.result
  intro env hc t hF
  have hrel : env "e" = env "c" ^ 2 * env "d" := by
    have h := hc (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")))
      (by simp [rubi713r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hW : env "b" * env "c" * (env "n" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n")
      (.int 1))) (.int 0)) (by simp [rubi713r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨hb, hcz⟩, hn1⟩ := hW'
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi713r2Nondeg, Defined, eval, Interp.real, hkn] at h
  have hn : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hkn
  have en1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hk1' : k + 1 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi713r2Nondeg.body →
      (k < 0 → env "a" + env "b" * Real.arsinh (env "c" * w) ≠ 0) ∧
        0 < env "d" + env "e" * w ^ 2 := by
    intro w h
    simp [rubi713r2Nondeg, Defined, eval, Interp.real, hkn, ivm1R, iv2R] at h
    refine ⟨h.1, ?_⟩
    have hs : Real.sqrt (env "d" + env "e" * w ^ 2) ≠ 0 := by tauto
    exact Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs))
  obtain ⟨hA0, hT0⟩ := hD t hF.self_of_nhds
  have hdpos : 0 < env "d" := by
    have h1 : 0 < 1 + env "c" ^ 2 * t ^ 2 := by positivity
    have : env "d" + env "e" * t ^ 2 = env "d" * (1 + env "c" ^ 2 * t ^ 2) := by
      rw [hrel]; ring
    rw [this] at hT0
    exact pos_of_mul_pos_left hT0 h1.le
  have hsd : Real.sqrt (env "d") ≠ 0 := (Real.sqrt_pos.mpr hdpos).ne'
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    obtain ⟨hAw, hTw⟩ := hD w hw
    have hS : 0 < 1 + env "c" ^ 2 * w ^ 2 := by positivity
    simp [rubi713r2Nondeg, Defined, eval, Interp.real, en1, ivm1R, iv2R, hb, hcz, hn1, hS.le,
      hTw.le, hTw.ne']
    exact fun h => hAw (hk1' h)
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w) rubi713r2Nondeg.result) =
        fun w => (env "b" * env "c" * (env "n" + 1))⁻¹ * (Real.sqrt (env "d"))⁻¹ *
          (env "a" + env "b" * Real.arsinh (env "c" * w)) ^ (k + 1) := by
      funext w
      have hS0 : Real.sqrt (1 + env "c" ^ 2 * w ^ 2) ≠ 0 :=
        (Real.sqrt_pos.mpr (by positivity)).ne'
      simp [rubi713r2Nondeg, eval, Interp.real, en1, ivm1R, iv2R, sqrt_factor hrel hdpos.le w,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      field_simp
    rw [hfun]
    have hA := ((hasDerivAt_arsinh_mul (env "c") t).const_mul (env "b")).const_add (env "a")
    have hor : env "a" + env "b" * Real.arsinh (env "c" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases hk : k < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (k + 1) _ hor).comp t hA
    refine (hP.const_mul _).congr_deriv ?_
    have hEF : eval Interp.real (Function.update env "x" t) rubi713r2Nondeg.body =
        (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k *
          (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
      simp [rubi713r2Nondeg, eval, Interp.real, hkn, ivm1R, iv2R]
    rw [hEF, sqrt_factor hrel hdpos.le t, show k + 1 - 1 = k by ring]
    have hkr : ((k + 1 : ℤ) : ℝ) = env "n" + 1 := by rw [hn]; push_cast; ring
    rw [hkr]
    have hS0 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity)).ne'
    generalize (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k = R
    field_simp

/-! ## RUBI 7.1.4 #23 -/

theorem rubi714r23Nondeg_real : rubi714r23Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi714r23Nondeg.conditions rubi714r23Nondeg.body
    rubi714r23Nondeg.result rubi714r23Nondeg.integrals
  intro env hc t hF
  have hW : 2 * env "e" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p")
      (.int 1))) (.int 0)) (by simp [rubi714r23Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, true_and] at hW'
  obtain ⟨he, hp1⟩ := hW'
  rcases hkp : intValue? (env "p") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi714r23Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (j : ℝ) := (intValue?_eq _ _).1 hkp
  have ep1 : intValue? (env "p" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hj1' : j + 1 < 0 → j < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi714r23Nondeg.body →
      (j < 0 → env "d" + env "e" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi714r23Nondeg, Defined, eval, Interp.real, hkp, iv2R] at h
    exact h
  have hD0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi714r23Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hDw := hD w hw
    have hS : 0 < 1 + env "c" ^ 2 * w ^ 2 := by positivity
    simp [Defined, eval, Interp.real, ep1, ivm1R, iv2R, hS.le, hS.ne']
    exact fun h => hDw (hj1' h)
  · filter_upwards [hF] with w hw
    have hDw := hD w hw
    simp [rubi714r23Nondeg, Defined, eval, recEnv, Interp.real, ep1, ivm1R, iv2R, he, hp1]
    exact fun h => hDw (hj1' h)
  · simp only [rubi714r23Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ 2) ^ (j + 1) *
        (Real.sqrt (1 + env "c" ^ 2 * t ^ 2))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, ep1, ivm1R, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi714r23Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi714r23Nondeg.result) =
        fun w => (env "d" + env "e" * w ^ 2) ^ (j + 1) *
            (env "a" + env "b" * Real.arsinh (env "c" * w)) * (2 * env "e" * (env "p" + 1))⁻¹ +
          -(env "b" * env "c") * (2 * env "e" * (env "p" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi714r23Nondeg, eval, recEnv, Interp.real, ep1, ivm1R, iv2R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi714r23Nondeg.body =
        t * (env "d" + env "e" * t ^ 2) ^ j * (env "a" + env "b" * Real.arsinh (env "c" * t)) := by
      simp [rubi714r23Nondeg, eval, Interp.real, hkp, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_arsinh_mul (env "c") t).const_mul (env "b")).const_add (env "a")
    have hor : env "d" + env "e" * t ^ 2 ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases hj : j < 0
      · exact Or.inl (hD0 hj)
      · exact Or.inr (by omega)
    have hDq := (hasDerivAt_zpow (j + 1) _ hor).comp t (hasDerivAt_quad0 (env "d") (env "e") t)
    refine (((hDq.mul hA).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    rw [hjr]
    have hS0 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity)).ne'
    generalize (env "d" + env "e" * t ^ 2) ^ j = R
    generalize (env "d" + env "e" * t ^ 2) ^ (j + 1) = R1
    generalize env "a" + env "b" * Real.arsinh (env "c" * t) = A
    field_simp
    ring

/-! ## RUBI 7.1.5 #11 -/

private theorem zpow_add_nat_of (A : ℝ) (j : ℤ) (n : ℕ) (h : 0 ≤ j) :
    A ^ (j + n) = A ^ j * A ^ n := by
  lift j to ℕ using h
  rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
    pow_add]

theorem rubi715r11Nondeg_real : rubi715r11Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi715r11Nondeg.conditions rubi715r11Nondeg.body
    rubi715r11Nondeg.result rubi715r11Nondeg.integrals
  intro env hc t hF
  have hrel : env "e" = env "c" ^ 2 * env "d" := by
    have h := hc (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")))
      (by simp [rubi715r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hmpos : 0 < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi715r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hdpos : 0 < env "d" := by
    have h := hc (.gt (.var "d") (.int 0)) (by simp [rubi715r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hnlt : env "n" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi715r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW : env "b" * env "c" * Real.sqrt (env "d") * (env "n" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c"))
      (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int 0))
      (by simp [rubi715r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, hdpos.le] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨⟨hb, hcz⟩, hsd⟩, hn1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi715r11Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi715r11Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hn : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hkn
  have hj : 0 < j := by rw [hm] at hmpos; exact_mod_cast hmpos
  have hk : k < -1 := by
    have : (k : ℝ) < -1 := hn ▸ hnlt
    exact_mod_cast this
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have hj1' : ¬ j < 1 := by omega
  have hk0 : k < 0 := by omega
  have hk1 : k + 1 < 0 := by omega
  have em1 : intValue? (env "m" + -1) = some (j - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have en1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi715r11Nondeg.body →
      env "a" + env "b" * Real.arsinh (env "c" * w) ≠ 0 := by
    intro w h
    simp [rubi715r11Nondeg, Defined, eval, Interp.real, hkm, hkn, hj0, hk0, ivm1R, iv2R] at h
    tauto
  have hA0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi715r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hAw := hD w hw
    simp [Defined, eval, Interp.real, em1, en1, hj1, hAw]
  · filter_upwards [hF] with w hw
    have hAw := hD w hw
    simp [rubi715r11Nondeg, Defined, eval, recEnv, Interp.real, hkm, en1, ivm1R, iv2R, hb, hcz,
      hsd, hn1, hj0, hAw, hdpos.le]
  · simp only [rubi715r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" + env "g" * t) ^ (j - 1) *
        (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ (k + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, en1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi715r11Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi715r11Nondeg.result) =
        fun w => (env "f" + env "g" * w) ^ j *
            (env "a" + env "b" * Real.arsinh (env "c" * w)) ^ (k + 1) *
            (env "b" * env "c" * Real.sqrt (env "d") * (env "n" + 1))⁻¹ +
          -(env "g" * env "m") * (env "b" * env "c" * Real.sqrt (env "d") * (env "n" + 1))⁻¹ *
            Φ "I1" w := by
      funext w
      simp [rubi715r11Nondeg, eval, recEnv, Interp.real, hkm, en1, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi715r11Nondeg.body =
        (env "f" + env "g" * t) ^ j * (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k *
          (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
      simp [rubi715r11Nondeg, eval, Interp.real, hkm, hkn, ivm1R, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_arsinh_mul (env "c") t).const_mul (env "b")).const_add (env "a")
    have hP := (hasDerivAt_zpow j _ (Or.inr (by omega))).comp t
      (hasDerivAt_lin (env "f") (env "g") t)
    have hQ := (hasDerivAt_zpow (k + 1) _ (Or.inl hA0)).comp t hA
    refine (((hP.mul hQ).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show k + 1 - 1 = k by ring, sqrt_factor hrel hdpos.le t]
    have eP : (env "f" + env "g" * t) ^ j =
        (env "f" + env "g" * t) ^ (j - 1) * (env "f" + env "g" * t) := by
      have := zpow_add_nat_of (env "f" + env "g" * t) (j - 1) 1 (by omega)
      rwa [show j - 1 + ((1 : ℕ) : ℤ) = j by push_cast; ring, pow_one] at this
    have eA : (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ (k + 1) =
        (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k *
          (env "a" + env "b" * Real.arsinh (env "c" * t)) := zpow_add_one₀ hA0 k
    rw [eP, eA]
    have hjr : ((j : ℤ) : ℝ) = env "m" := hm.symm
    have hkr : ((k + 1 : ℤ) : ℝ) = env "n" + 1 := by rw [hn]; push_cast; ring
    rw [hjr, hkr]
    have hS0 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity)).ne'
    generalize (env "f" + env "g" * t) ^ (j - 1) = P
    generalize (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k = R
    generalize env "a" + env "b" * Real.arsinh (env "c" * t) = A
    field_simp
    ring

end OSR.IntegrationRec240
