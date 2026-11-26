import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: perfect-square trinomials with a factor

Proofs of the RUBI rules of 4.1.9, 4.3.9 and 4.5.9 (over ℝ and ℂ for `sin`, `cos`, `tan`, `cot`,
over ℝ only for `sec` and `csc`) that multiply a perfect-square trinomial by `(A + B y)` or by a
power `z^m`: when `b^2 = 4 a c`, `(a + b y^n + c y^(2 n))^p = (b + 2 c y^n)^(2 p) / (4^p c^p)`. -/

namespace OSR.IntegrationRec251

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## rubi419r29Nondeg -/

theorem rubi419r29Nondeg_real : rubi419r29Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi419r29Nondeg.conditions rubi419r29Nondeg.body
    rubi419r29Nondeg.result rubi419r29Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi419r29Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkp : intValue? (env "n") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r29Nondeg, Defined, eval, Interp.real, hkp] at h
  have e2p : intValue? (2 * env "n") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n")))
      (.int 0)) (by simp [rubi419r29Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi419r29Nondeg.body →
      (l < 0 → env "a" + env "b" * Real.sin (env "d" + env "e" * w) + env "c" *
          Real.sin (env "d" + env "e" * w) ^ 2 ≠ 0) := by
    intro w h
    simp [rubi419r29Nondeg, Defined, eval, Interp.real, hkp, iv2R] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * Real.sin (env "d" + env "e" * w)) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * Real.sin (env "d" + env "e" * w) + env "c" *
          Real.sin (env "d" + env "e" * w) ^ 2) := by
    intro w
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi419r29Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hQw := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * Real.sin (env "d" + env "e" * w) ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * Real.sin (env "d" + env "e" * w) + env "c" *
            Real.sin (env "d" + env "e" * w) ^ 2) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, e2p] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi419r29Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi419r29Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "A" + env "B" * Real.sin (env "d" + env "e" * t)) *
            (env "b" + 2 * env "c" * Real.sin (env "d" + env "e" * t)) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi419r29Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi419r29Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi419r29Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi419r29Nondeg.body =
        (env "A" + env "B" * Real.sin (env "d" + env "e" * t)) *
            (env "a" + env "b" * Real.sin (env "d" + env "e" * t) + env "c" *
            Real.sin (env "d" + env "e" * t) ^ 2) ^ l := by
      simp [rubi419r29Nondeg, eval, Interp.real, hkp, iv2R]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * Real.sin (env "d" + env "e" * t)) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * Real.sin (env "d" + env "e" * t) + env "c" *
            Real.sin (env "d" + env "e" * t) ^ 2)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

theorem rubi419r29Nondeg_complex : rubi419r29Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi419r29Nondeg.conditions rubi419r29Nondeg.body
    rubi419r29Nondeg.result rubi419r29Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi419r29Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkp : intValue? (env "n") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r29Nondeg, Defined, eval, Interp.complex, hkp] at h
  have e2p : intValue? (2 * env "n") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n")))
      (.int 0)) (by simp [rubi419r29Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi419r29Nondeg.body →
      (l < 0 → env "a" + env "b" * Complex.sin (env "d" + env "e" * w) + env "c" *
          Complex.sin (env "d" + env "e" * w) ^ 2 ≠ 0) := by
    intro w h
    simp [rubi419r29Nondeg, Defined, eval, Interp.complex, hkp, iv2C] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * Complex.sin (env "d" + env "e" * w)) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * Complex.sin (env "d" + env "e" * w) + env "c" *
          Complex.sin (env "d" + env "e" * w) ^ 2) := by
    intro w
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi419r29Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hQw := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * Complex.sin (env "d" + env "e" * w) ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℂ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * Complex.sin (env "d" + env "e" * w) + env "c" *
            Complex.sin (env "d" + env "e" * w) ^ 2) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.complex, e2p] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi419r29Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi419r29Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "A" + env "B" * Complex.sin (env "d" + env "e" * t)) *
            (env "b" + 2 * env "c" * Complex.sin (env "d" + env "e" * t)) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi419r29Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi419r29Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi419r29Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi419r29Nondeg.body =
        (env "A" + env "B" * Complex.sin (env "d" + env "e" * t)) *
            (env "a" + env "b" * Complex.sin (env "d" + env "e" * t) + env "c" *
            Complex.sin (env "d" + env "e" * t) ^ 2) ^ l := by
      simp [rubi419r29Nondeg, eval, Interp.complex, hkp, iv2C]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * Complex.sin (env "d" + env "e" * t)) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * Complex.sin (env "d" + env "e" * t) + env "c" *
            Complex.sin (env "d" + env "e" * t) ^ 2)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi419r30Nondeg -/

theorem rubi419r30Nondeg_real : rubi419r30Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi419r30Nondeg.conditions rubi419r30Nondeg.body
    rubi419r30Nondeg.result rubi419r30Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi419r30Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkp : intValue? (env "n") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r30Nondeg, Defined, eval, Interp.real, hkp] at h
  have e2p : intValue? (2 * env "n") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n")))
      (.int 0)) (by simp [rubi419r30Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi419r30Nondeg.body →
      (l < 0 → env "a" + env "b" * Real.cos (env "d" + env "e" * w) + env "c" *
          Real.cos (env "d" + env "e" * w) ^ 2 ≠ 0) := by
    intro w h
    simp [rubi419r30Nondeg, Defined, eval, Interp.real, hkp, iv2R] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * Real.cos (env "d" + env "e" * w)) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * Real.cos (env "d" + env "e" * w) + env "c" *
          Real.cos (env "d" + env "e" * w) ^ 2) := by
    intro w
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi419r30Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hQw := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * Real.cos (env "d" + env "e" * w) ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * Real.cos (env "d" + env "e" * w) + env "c" *
            Real.cos (env "d" + env "e" * w) ^ 2) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, e2p] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi419r30Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi419r30Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "A" + env "B" * Real.cos (env "d" + env "e" * t)) *
            (env "b" + 2 * env "c" * Real.cos (env "d" + env "e" * t)) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi419r30Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi419r30Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi419r30Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi419r30Nondeg.body =
        (env "A" + env "B" * Real.cos (env "d" + env "e" * t)) *
            (env "a" + env "b" * Real.cos (env "d" + env "e" * t) + env "c" *
            Real.cos (env "d" + env "e" * t) ^ 2) ^ l := by
      simp [rubi419r30Nondeg, eval, Interp.real, hkp, iv2R]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * Real.cos (env "d" + env "e" * t)) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * Real.cos (env "d" + env "e" * t) + env "c" *
            Real.cos (env "d" + env "e" * t) ^ 2)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

theorem rubi419r30Nondeg_complex : rubi419r30Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi419r30Nondeg.conditions rubi419r30Nondeg.body
    rubi419r30Nondeg.result rubi419r30Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi419r30Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkp : intValue? (env "n") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r30Nondeg, Defined, eval, Interp.complex, hkp] at h
  have e2p : intValue? (2 * env "n") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n")))
      (.int 0)) (by simp [rubi419r30Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi419r30Nondeg.body →
      (l < 0 → env "a" + env "b" * Complex.cos (env "d" + env "e" * w) + env "c" *
          Complex.cos (env "d" + env "e" * w) ^ 2 ≠ 0) := by
    intro w h
    simp [rubi419r30Nondeg, Defined, eval, Interp.complex, hkp, iv2C] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * Complex.cos (env "d" + env "e" * w)) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * Complex.cos (env "d" + env "e" * w) + env "c" *
          Complex.cos (env "d" + env "e" * w) ^ 2) := by
    intro w
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi419r30Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hQw := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * Complex.cos (env "d" + env "e" * w) ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℂ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * Complex.cos (env "d" + env "e" * w) + env "c" *
            Complex.cos (env "d" + env "e" * w) ^ 2) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.complex, e2p] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi419r30Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi419r30Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "A" + env "B" * Complex.cos (env "d" + env "e" * t)) *
            (env "b" + 2 * env "c" * Complex.cos (env "d" + env "e" * t)) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi419r30Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi419r30Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi419r30Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi419r30Nondeg.body =
        (env "A" + env "B" * Complex.cos (env "d" + env "e" * t)) *
            (env "a" + env "b" * Complex.cos (env "d" + env "e" * t) + env "c" *
            Complex.cos (env "d" + env "e" * t) ^ 2) ^ l := by
      simp [rubi419r30Nondeg, eval, Interp.complex, hkp, iv2C]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * Complex.cos (env "d" + env "e" * t)) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * Complex.cos (env "d" + env "e" * t) + env "c" *
            Complex.cos (env "d" + env "e" * t) ^ 2)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi439r19Nondeg -/

theorem rubi439r19Nondeg_real : rubi439r19Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi439r19Nondeg.conditions rubi439r19Nondeg.body
    rubi439r19Nondeg.result rubi439r19Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r19Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkp : intValue? (env "n") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r19Nondeg, Defined, eval, Interp.real, hkp] at h
  have e2p : intValue? (2 * env "n") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n")))
      (.int 0)) (by simp [rubi439r19Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi439r19Nondeg.body →
      Real.cos (env "d" + env "e" * w) ≠ 0 ∧
          (l < 0 → env "a" + env "b" * Real.tan (env "d" + env "e" * w) + env "c" *
          Real.tan (env "d" + env "e" * w) ^ 2 ≠ 0) := by
    intro w h
    simp [rubi439r19Nondeg, Defined, eval, Interp.real, hkp, iv2R] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * Real.tan (env "d" + env "e" * w)) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * Real.tan (env "d" + env "e" * w) + env "c" *
          Real.tan (env "d" + env "e" * w) ^ 2) := by
    intro w
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi439r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * Real.tan (env "d" + env "e" * w) ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * Real.tan (env "d" + env "e" * w) + env "c" *
            Real.tan (env "d" + env "e" * w) ^ 2) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, e2p, hx0w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi439r19Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "A" + env "B" * Real.tan (env "d" + env "e" * t)) *
            (env "b" + 2 * env "c" * Real.tan (env "d" + env "e" * t)) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi439r19Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r19Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r19Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi439r19Nondeg.body =
        (env "A" + env "B" * Real.tan (env "d" + env "e" * t)) *
            (env "a" + env "b" * Real.tan (env "d" + env "e" * t) + env "c" *
            Real.tan (env "d" + env "e" * t) ^ 2) ^ l := by
      simp [rubi439r19Nondeg, eval, Interp.real, hkp, iv2R]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * Real.tan (env "d" + env "e" * t)) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * Real.tan (env "d" + env "e" * t) + env "c" *
            Real.tan (env "d" + env "e" * t) ^ 2)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

theorem rubi439r19Nondeg_complex : rubi439r19Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi439r19Nondeg.conditions rubi439r19Nondeg.body
    rubi439r19Nondeg.result rubi439r19Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r19Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkp : intValue? (env "n") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r19Nondeg, Defined, eval, Interp.complex, hkp] at h
  have e2p : intValue? (2 * env "n") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n")))
      (.int 0)) (by simp [rubi439r19Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi439r19Nondeg.body →
      Complex.cos (env "d" + env "e" * w) ≠ 0 ∧
          (l < 0 → env "a" + env "b" * Complex.tan (env "d" + env "e" * w) + env "c" *
          Complex.tan (env "d" + env "e" * w) ^ 2 ≠ 0) := by
    intro w h
    simp [rubi439r19Nondeg, Defined, eval, Interp.complex, hkp, iv2C] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * Complex.tan (env "d" + env "e" * w)) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * Complex.tan (env "d" + env "e" * w) + env "c" *
          Complex.tan (env "d" + env "e" * w) ^ 2) := by
    intro w
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi439r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * Complex.tan (env "d" + env "e" * w) ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℂ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * Complex.tan (env "d" + env "e" * w) + env "c" *
            Complex.tan (env "d" + env "e" * w) ^ 2) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.complex, e2p, hx0w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi439r19Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "A" + env "B" * Complex.tan (env "d" + env "e" * t)) *
            (env "b" + 2 * env "c" * Complex.tan (env "d" + env "e" * t)) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi439r19Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r19Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r19Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi439r19Nondeg.body =
        (env "A" + env "B" * Complex.tan (env "d" + env "e" * t)) *
            (env "a" + env "b" * Complex.tan (env "d" + env "e" * t) + env "c" *
            Complex.tan (env "d" + env "e" * t) ^ 2) ^ l := by
      simp [rubi439r19Nondeg, eval, Interp.complex, hkp, iv2C]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * Complex.tan (env "d" + env "e" * t)) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * Complex.tan (env "d" + env "e" * t) + env "c" *
            Complex.tan (env "d" + env "e" * t) ^ 2)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi439r20Nondeg -/

theorem rubi439r20Nondeg_real : rubi439r20Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi439r20Nondeg.conditions rubi439r20Nondeg.body
    rubi439r20Nondeg.result rubi439r20Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r20Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkp : intValue? (env "n") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r20Nondeg, Defined, eval, Interp.real, hkp] at h
  have e2p : intValue? (2 * env "n") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n")))
      (.int 0)) (by simp [rubi439r20Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi439r20Nondeg.body →
      Real.sin (env "d" + env "e" * w) ≠ 0 ∧
          (l < 0 → env "a" + env "b" * Real.cot (env "d" + env "e" * w) + env "c" *
          Real.cot (env "d" + env "e" * w) ^ 2 ≠ 0) := by
    intro w h
    simp [rubi439r20Nondeg, Defined, eval, Interp.real, hkp, iv2R] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * Real.cot (env "d" + env "e" * w)) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * Real.cot (env "d" + env "e" * w) + env "c" *
          Real.cot (env "d" + env "e" * w) ^ 2) := by
    intro w
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi439r20Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * Real.cot (env "d" + env "e" * w) ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * Real.cot (env "d" + env "e" * w) + env "c" *
            Real.cot (env "d" + env "e" * w) ^ 2) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, e2p, hx0w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi439r20Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r20Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "A" + env "B" * Real.cot (env "d" + env "e" * t)) *
            (env "b" + 2 * env "c" * Real.cot (env "d" + env "e" * t)) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi439r20Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r20Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r20Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi439r20Nondeg.body =
        (env "A" + env "B" * Real.cot (env "d" + env "e" * t)) *
            (env "a" + env "b" * Real.cot (env "d" + env "e" * t) + env "c" *
            Real.cot (env "d" + env "e" * t) ^ 2) ^ l := by
      simp [rubi439r20Nondeg, eval, Interp.real, hkp, iv2R]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * Real.cot (env "d" + env "e" * t)) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * Real.cot (env "d" + env "e" * t) + env "c" *
            Real.cot (env "d" + env "e" * t) ^ 2)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

theorem rubi439r20Nondeg_complex : rubi439r20Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi439r20Nondeg.conditions rubi439r20Nondeg.body
    rubi439r20Nondeg.result rubi439r20Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r20Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkp : intValue? (env "n") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r20Nondeg, Defined, eval, Interp.complex, hkp] at h
  have e2p : intValue? (2 * env "n") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n")))
      (.int 0)) (by simp [rubi439r20Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi439r20Nondeg.body →
      Complex.sin (env "d" + env "e" * w) ≠ 0 ∧
          (l < 0 → env "a" + env "b" * Complex.cot (env "d" + env "e" * w) + env "c" *
          Complex.cot (env "d" + env "e" * w) ^ 2 ≠ 0) := by
    intro w h
    simp [rubi439r20Nondeg, Defined, eval, Interp.complex, hkp, iv2C] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * Complex.cot (env "d" + env "e" * w)) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * Complex.cot (env "d" + env "e" * w) + env "c" *
          Complex.cot (env "d" + env "e" * w) ^ 2) := by
    intro w
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi439r20Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * Complex.cot (env "d" + env "e" * w) ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℂ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * Complex.cot (env "d" + env "e" * w) + env "c" *
            Complex.cot (env "d" + env "e" * w) ^ 2) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.complex, e2p, hx0w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi439r20Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r20Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "A" + env "B" * Complex.cot (env "d" + env "e" * t)) *
            (env "b" + 2 * env "c" * Complex.cot (env "d" + env "e" * t)) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi439r20Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r20Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r20Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi439r20Nondeg.body =
        (env "A" + env "B" * Complex.cot (env "d" + env "e" * t)) *
            (env "a" + env "b" * Complex.cot (env "d" + env "e" * t) + env "c" *
            Complex.cot (env "d" + env "e" * t) ^ 2) ^ l := by
      simp [rubi439r20Nondeg, eval, Interp.complex, hkp, iv2C]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * Complex.cot (env "d" + env "e" * t)) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * Complex.cot (env "d" + env "e" * t) + env "c" *
            Complex.cot (env "d" + env "e" * t) ^ 2)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi459r11Nondeg -/

theorem rubi459r11Nondeg_real : rubi459r11Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi459r11Nondeg.conditions rubi459r11Nondeg.body
    rubi459r11Nondeg.result rubi459r11Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi459r11Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkp : intValue? (env "n") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r11Nondeg, Defined, eval, Interp.real, hkp] at h
  have e2p : intValue? (2 * env "n") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n")))
      (.int 0)) (by simp [rubi459r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi459r11Nondeg.body →
      Real.cos (env "d" + env "e" * w) ≠ 0 ∧
          (l < 0 → env "a" + env "b" * (Real.cos (env "d" + env "e" * w))⁻¹ + env "c" *
          (Real.cos (env "d" + env "e" * w))⁻¹ ^ 2 ≠ 0) := by
    intro w h
    simp [rubi459r11Nondeg, Defined, eval, Interp.real, hkp, iv2R, Fn.sec] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Real.cos (env "d" + env "e" * w))⁻¹) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Real.cos (env "d" + env "e" * w))⁻¹ + env "c" *
          (Real.cos (env "d" + env "e" * w))⁻¹ ^ 2) := by
    intro w
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi459r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Real.cos (env "d" + env "e" * w))⁻¹ ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Real.cos (env "d" + env "e" * w))⁻¹ + env "c" *
            (Real.cos (env "d" + env "e" * w))⁻¹ ^ 2) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, e2p, Fn.sec, hx0w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi459r11Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi459r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "A" + env "B" * (Real.cos (env "d" + env "e" * t))⁻¹) *
            (env "b" + 2 * env "c" * (Real.cos (env "d" + env "e" * t))⁻¹) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, e2p, Fn.sec]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi459r11Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi459r11Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi459r11Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi459r11Nondeg.body =
        (env "A" + env "B" * (Real.cos (env "d" + env "e" * t))⁻¹) *
            (env "a" + env "b" * (Real.cos (env "d" + env "e" * t))⁻¹ + env "c" *
            (Real.cos (env "d" + env "e" * t))⁻¹ ^ 2) ^ l := by
      simp [rubi459r11Nondeg, eval, Interp.real, hkp, iv2R, Fn.sec]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Real.cos (env "d" + env "e" * t))⁻¹) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Real.cos (env "d" + env "e" * t))⁻¹ + env "c" *
            (Real.cos (env "d" + env "e" * t))⁻¹ ^ 2)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi459r12Nondeg -/

theorem rubi459r12Nondeg_real : rubi459r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi459r12Nondeg.conditions rubi459r12Nondeg.body
    rubi459r12Nondeg.result rubi459r12Nondeg.integrals
  intro env hc t hF
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi459r12Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkp : intValue? (env "n") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r12Nondeg, Defined, eval, Interp.real, hkp] at h
  have e2p : intValue? (2 * env "n") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n")))
      (.int 0)) (by simp [rubi459r12Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi459r12Nondeg.body →
      Real.sin (env "d" + env "e" * w) ≠ 0 ∧
          (l < 0 → env "a" + env "b" * (Real.sin (env "d" + env "e" * w))⁻¹ + env "c" *
          (Real.sin (env "d" + env "e" * w))⁻¹ ^ 2 ≠ 0) := by
    intro w h
    simp [rubi459r12Nondeg, Defined, eval, Interp.real, hkp, iv2R, Fn.csc] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Real.sin (env "d" + env "e" * w))⁻¹) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Real.sin (env "d" + env "e" * w))⁻¹ + env "c" *
          (Real.sin (env "d" + env "e" * w))⁻¹ ^ 2) := by
    intro w
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi459r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Real.sin (env "d" + env "e" * w))⁻¹ ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Real.sin (env "d" + env "e" * w))⁻¹ + env "c" *
            (Real.sin (env "d" + env "e" * w))⁻¹ ^ 2) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, e2p, Fn.csc, hx0w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi459r12Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi459r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "A" + env "B" * (Real.sin (env "d" + env "e" * t))⁻¹) *
            (env "b" + 2 * env "c" * (Real.sin (env "d" + env "e" * t))⁻¹) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, e2p, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi459r12Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi459r12Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi459r12Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi459r12Nondeg.body =
        (env "A" + env "B" * (Real.sin (env "d" + env "e" * t))⁻¹) *
            (env "a" + env "b" * (Real.sin (env "d" + env "e" * t))⁻¹ + env "c" *
            (Real.sin (env "d" + env "e" * t))⁻¹ ^ 2) ^ l := by
      simp [rubi459r12Nondeg, eval, Interp.real, hkp, iv2R, Fn.csc]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Real.sin (env "d" + env "e" * t))⁻¹) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Real.sin (env "d" + env "e" * t))⁻¹ + env "c" *
            (Real.sin (env "d" + env "e" * t))⁻¹ ^ 2)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi419r5Nondeg -/

theorem rubi419r5Nondeg_real : rubi419r5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi419r5Nondeg.conditions rubi419r5Nondeg.body
    rubi419r5Nondeg.result rubi419r5Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi419r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi419r5Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r5Nondeg, Defined, eval, Interp.real, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r5Nondeg, Defined, eval, Interp.real, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r5Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r5Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi419r5Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi419r5Nondeg.body →
      (mm < 0 → Real.sin (env "d" + env "e" * w) ≠ 0) ∧
          (k < 0 → Real.sin (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Real.sin (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.sin (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi419r5Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Real.sin (env "d" + env "e" * w)) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Real.sin (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.sin (env "d" + env "e" * w)) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi419r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Real.sin (env "d" + env "e" * w)) ^ k ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Real.sin (env "d" + env "e" * w)) ^ k + env "c" *
            (Real.sin (env "d" + env "e" * w)) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, hkM, hkn, e2p] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi419r5Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi419r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((Real.sin (env "d" + env "e" * t)) ^ mm *
            (env "b" + 2 * env "c" * (Real.sin (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkM, hkn, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi419r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi419r5Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi419r5Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi419r5Nondeg.body =
        (Real.sin (env "d" + env "e" * t)) ^ mm *
            (env "a" + env "b" * (Real.sin (env "d" + env "e" * t)) ^ k + env "c" *
            (Real.sin (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi419r5Nondeg, eval, Interp.real, hkM, hkn, hkj, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Real.sin (env "d" + env "e" * t)) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Real.sin (env "d" + env "e" * t)) ^ k + env "c" *
            (Real.sin (env "d" + env "e" * t)) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

theorem rubi419r5Nondeg_complex : rubi419r5Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi419r5Nondeg.conditions rubi419r5Nondeg.body
    rubi419r5Nondeg.result rubi419r5Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi419r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi419r5Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r5Nondeg, Defined, eval, Interp.complex, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r5Nondeg, Defined, eval, Interp.complex, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r5Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r5Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi419r5Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi419r5Nondeg.body →
      (mm < 0 → Complex.sin (env "d" + env "e" * w) ≠ 0) ∧
          (k < 0 → Complex.sin (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Complex.sin (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.sin (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi419r5Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj, hkp] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Complex.sin (env "d" + env "e" * w)) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Complex.sin (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.sin (env "d" + env "e" * w)) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi419r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Complex.sin (env "d" + env "e" * w)) ^ k ≠ 0 :=
        by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℂ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Complex.sin (env "d" + env "e" * w)) ^ k + env "c" *
            (Complex.sin (env "d" + env "e" * w)) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.complex, hkM, hkn, e2p] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi419r5Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi419r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((Complex.sin (env "d" + env "e" * t)) ^ mm *
            (env "b" + 2 * env "c" * (Complex.sin (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkM, hkn, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi419r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi419r5Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi419r5Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi419r5Nondeg.body =
        (Complex.sin (env "d" + env "e" * t)) ^ mm *
            (env "a" + env "b" * (Complex.sin (env "d" + env "e" * t)) ^ k + env "c" *
            (Complex.sin (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi419r5Nondeg, eval, Interp.complex, hkM, hkn, hkj, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Complex.sin (env "d" + env "e" * t)) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Complex.sin (env "d" + env "e" * t)) ^ k + env "c" *
            (Complex.sin (env "d" + env "e" * t)) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi419r6Nondeg -/

theorem rubi419r6Nondeg_real : rubi419r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi419r6Nondeg.conditions rubi419r6Nondeg.body
    rubi419r6Nondeg.result rubi419r6Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi419r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi419r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r6Nondeg, Defined, eval, Interp.real, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r6Nondeg, Defined, eval, Interp.real, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r6Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r6Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi419r6Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi419r6Nondeg.body →
      (mm < 0 → Real.cos (env "d" + env "e" * w) ≠ 0) ∧
          (k < 0 → Real.cos (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Real.cos (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.cos (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi419r6Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Real.cos (env "d" + env "e" * w)) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Real.cos (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.cos (env "d" + env "e" * w)) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi419r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Real.cos (env "d" + env "e" * w)) ^ k ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Real.cos (env "d" + env "e" * w)) ^ k + env "c" *
            (Real.cos (env "d" + env "e" * w)) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, hkM, hkn, e2p] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi419r6Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi419r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((Real.cos (env "d" + env "e" * t)) ^ mm *
            (env "b" + 2 * env "c" * (Real.cos (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkM, hkn, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi419r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi419r6Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi419r6Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi419r6Nondeg.body =
        (Real.cos (env "d" + env "e" * t)) ^ mm *
            (env "a" + env "b" * (Real.cos (env "d" + env "e" * t)) ^ k + env "c" *
            (Real.cos (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi419r6Nondeg, eval, Interp.real, hkM, hkn, hkj, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Real.cos (env "d" + env "e" * t)) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Real.cos (env "d" + env "e" * t)) ^ k + env "c" *
            (Real.cos (env "d" + env "e" * t)) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

theorem rubi419r6Nondeg_complex : rubi419r6Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi419r6Nondeg.conditions rubi419r6Nondeg.body
    rubi419r6Nondeg.result rubi419r6Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi419r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi419r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r6Nondeg, Defined, eval, Interp.complex, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r6Nondeg, Defined, eval, Interp.complex, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r6Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r6Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi419r6Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi419r6Nondeg.body →
      (mm < 0 → Complex.cos (env "d" + env "e" * w) ≠ 0) ∧
          (k < 0 → Complex.cos (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Complex.cos (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.cos (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi419r6Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj, hkp] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Complex.cos (env "d" + env "e" * w)) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Complex.cos (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.cos (env "d" + env "e" * w)) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi419r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Complex.cos (env "d" + env "e" * w)) ^ k ≠ 0 :=
        by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℂ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Complex.cos (env "d" + env "e" * w)) ^ k + env "c" *
            (Complex.cos (env "d" + env "e" * w)) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.complex, hkM, hkn, e2p] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi419r6Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi419r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((Complex.cos (env "d" + env "e" * t)) ^ mm *
            (env "b" + 2 * env "c" * (Complex.cos (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkM, hkn, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi419r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi419r6Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi419r6Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi419r6Nondeg.body =
        (Complex.cos (env "d" + env "e" * t)) ^ mm *
            (env "a" + env "b" * (Complex.cos (env "d" + env "e" * t)) ^ k + env "c" *
            (Complex.cos (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi419r6Nondeg, eval, Interp.complex, hkM, hkn, hkj, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Complex.cos (env "d" + env "e" * t)) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Complex.cos (env "d" + env "e" * t)) ^ k + env "c" *
            (Complex.cos (env "d" + env "e" * t)) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi439r9Nondeg -/

theorem rubi439r9Nondeg_real : rubi439r9Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi439r9Nondeg.conditions rubi439r9Nondeg.body
    rubi439r9Nondeg.result rubi439r9Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi439r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r9Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r9Nondeg, Defined, eval, Interp.real, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r9Nondeg, Defined, eval, Interp.real, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r9Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r9Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi439r9Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi439r9Nondeg.body →
      Real.cos (env "d" + env "e" * w) ≠ 0 ∧ (mm < 0 → Real.tan (env "d" + env "e" * w) ≠ 0) ∧
          (k < 0 → Real.tan (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Real.tan (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.tan (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi439r9Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Real.tan (env "d" + env "e" * w)) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Real.tan (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.tan (env "d" + env "e" * w)) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi439r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Real.tan (env "d" + env "e" * w)) ^ k ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Real.tan (env "d" + env "e" * w)) ^ k + env "c" *
            (Real.tan (env "d" + env "e" * w)) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, hkM, hkn, e2p, hx0w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi439r9Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((Real.tan (env "d" + env "e" * t)) ^ mm *
            (env "b" + 2 * env "c" * (Real.tan (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkM, hkn, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi439r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r9Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r9Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi439r9Nondeg.body =
        (Real.tan (env "d" + env "e" * t)) ^ mm *
            (env "a" + env "b" * (Real.tan (env "d" + env "e" * t)) ^ k + env "c" *
            (Real.tan (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi439r9Nondeg, eval, Interp.real, hkM, hkn, hkj, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Real.tan (env "d" + env "e" * t)) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Real.tan (env "d" + env "e" * t)) ^ k + env "c" *
            (Real.tan (env "d" + env "e" * t)) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

theorem rubi439r9Nondeg_complex : rubi439r9Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi439r9Nondeg.conditions rubi439r9Nondeg.body
    rubi439r9Nondeg.result rubi439r9Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi439r9Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r9Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r9Nondeg, Defined, eval, Interp.complex, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r9Nondeg, Defined, eval, Interp.complex, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r9Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r9Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi439r9Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi439r9Nondeg.body →
      Complex.cos (env "d" + env "e" * w) ≠ 0 ∧
          (mm < 0 → Complex.tan (env "d" + env "e" * w) ≠ 0) ∧
          (k < 0 → Complex.tan (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Complex.tan (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.tan (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi439r9Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj, hkp] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Complex.tan (env "d" + env "e" * w)) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Complex.tan (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.tan (env "d" + env "e" * w)) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi439r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Complex.tan (env "d" + env "e" * w)) ^ k ≠ 0 :=
        by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℂ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Complex.tan (env "d" + env "e" * w)) ^ k + env "c" *
            (Complex.tan (env "d" + env "e" * w)) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.complex, hkM, hkn, e2p, hx0w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi439r9Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((Complex.tan (env "d" + env "e" * t)) ^ mm *
            (env "b" + 2 * env "c" * (Complex.tan (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkM, hkn, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi439r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r9Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r9Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi439r9Nondeg.body =
        (Complex.tan (env "d" + env "e" * t)) ^ mm *
            (env "a" + env "b" * (Complex.tan (env "d" + env "e" * t)) ^ k + env "c" *
            (Complex.tan (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi439r9Nondeg, eval, Interp.complex, hkM, hkn, hkj, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Complex.tan (env "d" + env "e" * t)) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Complex.tan (env "d" + env "e" * t)) ^ k + env "c" *
            (Complex.tan (env "d" + env "e" * t)) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi439r10Nondeg -/

theorem rubi439r10Nondeg_real : rubi439r10Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi439r10Nondeg.conditions rubi439r10Nondeg.body
    rubi439r10Nondeg.result rubi439r10Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi439r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r10Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r10Nondeg, Defined, eval, Interp.real, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r10Nondeg, Defined, eval, Interp.real, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r10Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r10Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi439r10Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi439r10Nondeg.body →
      Real.sin (env "d" + env "e" * w) ≠ 0 ∧ (mm < 0 → Real.cot (env "d" + env "e" * w) ≠ 0) ∧
          (k < 0 → Real.cot (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Real.cot (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.cot (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi439r10Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Real.cot (env "d" + env "e" * w)) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Real.cot (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.cot (env "d" + env "e" * w)) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi439r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Real.cot (env "d" + env "e" * w)) ^ k ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Real.cot (env "d" + env "e" * w)) ^ k + env "c" *
            (Real.cot (env "d" + env "e" * w)) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, hkM, hkn, e2p, hx0w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi439r10Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((Real.cot (env "d" + env "e" * t)) ^ mm *
            (env "b" + 2 * env "c" * (Real.cot (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkM, hkn, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi439r10Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r10Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r10Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi439r10Nondeg.body =
        (Real.cot (env "d" + env "e" * t)) ^ mm *
            (env "a" + env "b" * (Real.cot (env "d" + env "e" * t)) ^ k + env "c" *
            (Real.cot (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi439r10Nondeg, eval, Interp.real, hkM, hkn, hkj, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Real.cot (env "d" + env "e" * t)) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Real.cot (env "d" + env "e" * t)) ^ k + env "c" *
            (Real.cot (env "d" + env "e" * t)) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

theorem rubi439r10Nondeg_complex : rubi439r10Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi439r10Nondeg.conditions rubi439r10Nondeg.body
    rubi439r10Nondeg.result rubi439r10Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi439r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r10Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r10Nondeg, Defined, eval, Interp.complex, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r10Nondeg, Defined, eval, Interp.complex, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r10Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r10Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi439r10Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi439r10Nondeg.body →
      Complex.sin (env "d" + env "e" * w) ≠ 0 ∧
          (mm < 0 → Complex.cot (env "d" + env "e" * w) ≠ 0) ∧
          (k < 0 → Complex.cot (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Complex.cot (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.cot (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi439r10Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj, hkp] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Complex.cot (env "d" + env "e" * w)) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Complex.cot (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.cot (env "d" + env "e" * w)) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi439r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Complex.cot (env "d" + env "e" * w)) ^ k ≠ 0 :=
        by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℂ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Complex.cot (env "d" + env "e" * w)) ^ k + env "c" *
            (Complex.cot (env "d" + env "e" * w)) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.complex, hkM, hkn, e2p, hx0w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi439r10Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((Complex.cot (env "d" + env "e" * t)) ^ mm *
            (env "b" + 2 * env "c" * (Complex.cot (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkM, hkn, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi439r10Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r10Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r10Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi439r10Nondeg.body =
        (Complex.cot (env "d" + env "e" * t)) ^ mm *
            (env "a" + env "b" * (Complex.cot (env "d" + env "e" * t)) ^ k + env "c" *
            (Complex.cot (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi439r10Nondeg, eval, Interp.complex, hkM, hkn, hkj, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Complex.cot (env "d" + env "e" * t)) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Complex.cot (env "d" + env "e" * t)) ^ k + env "c" *
            (Complex.cot (env "d" + env "e" * t)) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi439r15Nondeg -/

theorem rubi439r15Nondeg_real : rubi439r15Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi439r15Nondeg.conditions rubi439r15Nondeg.body
    rubi439r15Nondeg.result rubi439r15Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi439r15Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r15Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r15Nondeg, Defined, eval, Interp.real, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r15Nondeg, Defined, eval, Interp.real, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r15Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r15Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi439r15Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi439r15Nondeg.body →
      Real.cos (env "d" + env "e" * w) ≠ 0 ∧ Real.sin (env "d" + env "e" * w) ≠ 0 ∧
          (mm < 0 → Real.cot (env "d" + env "e" * w) ≠ 0) ∧
          (k < 0 → Real.tan (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Real.tan (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.tan (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi439r15Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Real.tan (env "d" + env "e" * w)) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Real.tan (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.tan (env "d" + env "e" * w)) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi439r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hx1w, hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Real.tan (env "d" + env "e" * w)) ^ k ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Real.tan (env "d" + env "e" * w)) ^ k + env "c" *
            (Real.tan (env "d" + env "e" * w)) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, hkM, hkn, e2p, hx0w, hx1w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi439r15Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((Real.cot (env "d" + env "e" * t)) ^ mm *
            (env "b" + 2 * env "c" * (Real.tan (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkM, hkn, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi439r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r15Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r15Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi439r15Nondeg.body =
        (Real.cot (env "d" + env "e" * t)) ^ mm *
            (env "a" + env "b" * (Real.tan (env "d" + env "e" * t)) ^ k + env "c" *
            (Real.tan (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi439r15Nondeg, eval, Interp.real, hkM, hkn, hkj, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Real.tan (env "d" + env "e" * t)) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Real.tan (env "d" + env "e" * t)) ^ k + env "c" *
            (Real.tan (env "d" + env "e" * t)) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

theorem rubi439r15Nondeg_complex : rubi439r15Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi439r15Nondeg.conditions rubi439r15Nondeg.body
    rubi439r15Nondeg.result rubi439r15Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi439r15Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r15Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r15Nondeg, Defined, eval, Interp.complex, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r15Nondeg, Defined, eval, Interp.complex, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r15Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r15Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi439r15Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi439r15Nondeg.body →
      Complex.cos (env "d" + env "e" * w) ≠ 0 ∧ Complex.sin (env "d" + env "e" * w) ≠ 0 ∧
          (mm < 0 → Complex.cot (env "d" + env "e" * w) ≠ 0) ∧
          (k < 0 → Complex.tan (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Complex.tan (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.tan (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi439r15Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj, hkp] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Complex.tan (env "d" + env "e" * w)) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Complex.tan (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.tan (env "d" + env "e" * w)) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi439r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hx1w, hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Complex.tan (env "d" + env "e" * w)) ^ k ≠ 0 :=
        by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℂ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Complex.tan (env "d" + env "e" * w)) ^ k + env "c" *
            (Complex.tan (env "d" + env "e" * w)) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.complex, hkM, hkn, e2p, hx0w, hx1w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi439r15Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((Complex.cot (env "d" + env "e" * t)) ^ mm *
            (env "b" + 2 * env "c" * (Complex.tan (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkM, hkn, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi439r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r15Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r15Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi439r15Nondeg.body =
        (Complex.cot (env "d" + env "e" * t)) ^ mm *
            (env "a" + env "b" * (Complex.tan (env "d" + env "e" * t)) ^ k + env "c" *
            (Complex.tan (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi439r15Nondeg, eval, Interp.complex, hkM, hkn, hkj, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Complex.tan (env "d" + env "e" * t)) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Complex.tan (env "d" + env "e" * t)) ^ k + env "c" *
            (Complex.tan (env "d" + env "e" * t)) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi439r16Nondeg -/

theorem rubi439r16Nondeg_real : rubi439r16Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi439r16Nondeg.conditions rubi439r16Nondeg.body
    rubi439r16Nondeg.result rubi439r16Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi439r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r16Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r16Nondeg, Defined, eval, Interp.real, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r16Nondeg, Defined, eval, Interp.real, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r16Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r16Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi439r16Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi439r16Nondeg.body →
      Real.sin (env "d" + env "e" * w) ≠ 0 ∧ Real.cos (env "d" + env "e" * w) ≠ 0 ∧
          (mm < 0 → Real.tan (env "d" + env "e" * w) ≠ 0) ∧
          (k < 0 → Real.cot (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Real.cot (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.cot (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi439r16Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Real.cot (env "d" + env "e" * w)) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Real.cot (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.cot (env "d" + env "e" * w)) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi439r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hx1w, hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Real.cot (env "d" + env "e" * w)) ^ k ≠ 0 := by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Real.cot (env "d" + env "e" * w)) ^ k + env "c" *
            (Real.cot (env "d" + env "e" * w)) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, hkM, hkn, e2p, hx0w, hx1w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi439r16Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((Real.tan (env "d" + env "e" * t)) ^ mm *
            (env "b" + 2 * env "c" * (Real.cot (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkM, hkn, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi439r16Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r16Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r16Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi439r16Nondeg.body =
        (Real.tan (env "d" + env "e" * t)) ^ mm *
            (env "a" + env "b" * (Real.cot (env "d" + env "e" * t)) ^ k + env "c" *
            (Real.cot (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi439r16Nondeg, eval, Interp.real, hkM, hkn, hkj, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Real.cot (env "d" + env "e" * t)) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Real.cot (env "d" + env "e" * t)) ^ k + env "c" *
            (Real.cot (env "d" + env "e" * t)) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

theorem rubi439r16Nondeg_complex : rubi439r16Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi439r16Nondeg.conditions rubi439r16Nondeg.body
    rubi439r16Nondeg.result rubi439r16Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi439r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r16Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r16Nondeg, Defined, eval, Interp.complex, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r16Nondeg, Defined, eval, Interp.complex, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r16Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r16Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi439r16Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi439r16Nondeg.body →
      Complex.sin (env "d" + env "e" * w) ≠ 0 ∧ Complex.cos (env "d" + env "e" * w) ≠ 0 ∧
          (mm < 0 → Complex.tan (env "d" + env "e" * w) ≠ 0) ∧
          (k < 0 → Complex.cot (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Complex.cot (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.cot (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi439r16Nondeg, Defined, eval, Interp.complex, hkM, hkn, hkj, hkp] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * (Complex.cot (env "d" + env "e" * w)) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * (Complex.cot (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.cot (env "d" + env "e" * w)) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi439r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hx1w, hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * (Complex.cot (env "d" + env "e" * w)) ^ k ≠ 0 :=
        by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℂ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * (Complex.cot (env "d" + env "e" * w)) ^ k + env "c" *
            (Complex.cot (env "d" + env "e" * w)) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.complex, hkM, hkn, e2p, hx0w, hx1w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi439r16Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((Complex.tan (env "d" + env "e" * t)) ^ mm *
            (env "b" + 2 * env "c" * (Complex.cot (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkM, hkn, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi439r16Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r16Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r16Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi439r16Nondeg.body =
        (Complex.tan (env "d" + env "e" * t)) ^ mm *
            (env "a" + env "b" * (Complex.cot (env "d" + env "e" * t)) ^ k + env "c" *
            (Complex.cot (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi439r16Nondeg, eval, Interp.complex, hkM, hkn, hkj, hkp]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * (Complex.cot (env "d" + env "e" * t)) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * (Complex.cot (env "d" + env "e" * t)) ^ k + env "c" *
            (Complex.cot (env "d" + env "e" * t)) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi459r5Nondeg -/

theorem rubi459r5Nondeg_real : rubi459r5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi459r5Nondeg.conditions rubi459r5Nondeg.body
    rubi459r5Nondeg.result rubi459r5Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi459r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi459r5Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r5Nondeg, Defined, eval, Interp.real, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r5Nondeg, Defined, eval, Interp.real, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r5Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r5Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi459r5Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi459r5Nondeg.body →
      Real.cos (env "d" + env "e" * w) ≠ 0 ∧ (mm < 0 → (Real.cos (env "d" + env "e" * w))⁻¹ ≠ 0) ∧
          (k < 0 → (Real.cos (env "d" + env "e" * w))⁻¹ ≠ 0) ∧
          (l < 0 → env "a" + env "b" * ((Real.cos (env "d" + env "e" * w))⁻¹) ^ k + env "c" *
          ((Real.cos (env "d" + env "e" * w))⁻¹) ^ j ≠ 0) := by
    intro w h
    simp [rubi459r5Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp, Fn.sec] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * ((Real.cos (env "d" + env "e" * w))⁻¹) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * ((Real.cos (env "d" + env "e" * w))⁻¹) ^ k + env "c" *
          ((Real.cos (env "d" + env "e" * w))⁻¹) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi459r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * ((Real.cos (env "d" + env "e" * w))⁻¹) ^ k ≠ 0 :=
        by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * ((Real.cos (env "d" + env "e" * w))⁻¹) ^ k + env "c" *
            ((Real.cos (env "d" + env "e" * w))⁻¹) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, hkM, hkn, e2p, Fn.sec, hx0w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi459r5Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi459r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        (((Real.cos (env "d" + env "e" * t))⁻¹) ^ mm *
            (env "b" + 2 * env "c" * ((Real.cos (env "d" + env "e" * t))⁻¹) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkM, hkn, e2p, Fn.sec]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi459r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi459r5Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi459r5Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi459r5Nondeg.body =
        ((Real.cos (env "d" + env "e" * t))⁻¹) ^ mm *
            (env "a" + env "b" * ((Real.cos (env "d" + env "e" * t))⁻¹) ^ k + env "c" *
            ((Real.cos (env "d" + env "e" * t))⁻¹) ^ j) ^ l := by
      simp [rubi459r5Nondeg, eval, Interp.real, hkM, hkn, hkj, hkp, Fn.sec]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * ((Real.cos (env "d" + env "e" * t))⁻¹) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * ((Real.cos (env "d" + env "e" * t))⁻¹) ^ k + env "c" *
            ((Real.cos (env "d" + env "e" * t))⁻¹) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

/-! ## rubi459r6Nondeg -/

theorem rubi459r6Nondeg_real : rubi459r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi459r6Nondeg.conditions rubi459r6Nondeg.body
    rubi459r6Nondeg.result rubi459r6Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi459r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi459r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkM : intValue? (env "m") with _ | mm
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r6Nondeg, Defined, eval, Interp.real, hkM] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r6Nondeg, Defined, eval, Interp.real, hkM, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r6Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r6Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi459r6Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi459r6Nondeg.body →
      Real.sin (env "d" + env "e" * w) ≠ 0 ∧ (mm < 0 → (Real.sin (env "d" + env "e" * w))⁻¹ ≠ 0) ∧
          (k < 0 → (Real.sin (env "d" + env "e" * w))⁻¹ ≠ 0) ∧
          (l < 0 → env "a" + env "b" * ((Real.sin (env "d" + env "e" * w))⁻¹) ^ k + env "c" *
          ((Real.sin (env "d" + env "e" * w))⁻¹) ^ j ≠ 0) := by
    intro w h
    simp [rubi459r6Nondeg, Defined, eval, Interp.real, hkM, hkn, hkj, hkp, Fn.csc] at h ⊢
    tauto
  have hsq : ∀ w, (env "b" + 2 * env "c" * ((Real.sin (env "d" + env "e" * w))⁻¹) ^ k) ^ 2 =
      4 * env "c" *
          (env "a" + env "b" * ((Real.sin (env "d" + env "e" * w))⁻¹) ^ k + env "c" *
          ((Real.sin (env "d" + env "e" * w))⁻¹) ^ j) := by
    intro w
    rw [hjk, mul_comm (2 : ℤ) k, zpow_mul]
    simp only [zpow_two]
    linear_combination hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi459r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hx0w, hMw, hTw, hQw⟩ := hD w hw
    have hB : 2 * l < 0 → env "b" + 2 * env "c" * ((Real.sin (env "d" + env "e" * w))⁻¹) ^ k ≠ 0 :=
        by
      intro hl h0
      have := hsq w
      rw [h0] at this
      exact hQw (by omega) (by
        have h4 : (4 : ℝ) * env "c" ≠ 0 := mul_ne_zero (by norm_num) (hWc (by omega))
        have : 4 * env "c" *
            (env "a" + env "b" * ((Real.sin (env "d" + env "e" * w))⁻¹) ^ k + env "c" *
            ((Real.sin (env "d" + env "e" * w))⁻¹) ^ j) = 0 := by rw [← this]; ring
        exact (mul_eq_zero.mp this).resolve_left h4)
    simp [Defined, eval, Interp.real, hkM, hkn, e2p, Fn.csc, hx0w] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi459r6Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi459r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        (((Real.sin (env "d" + env "e" * t))⁻¹) ^ mm *
            (env "b" + 2 * env "c" * ((Real.sin (env "d" + env "e" * t))⁻¹) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkM, hkn, e2p, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi459r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi459r6Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi459r6Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi459r6Nondeg.body =
        ((Real.sin (env "d" + env "e" * t))⁻¹) ^ mm *
            (env "a" + env "b" * ((Real.sin (env "d" + env "e" * t))⁻¹) ^ k + env "c" *
            ((Real.sin (env "d" + env "e" * t))⁻¹) ^ j) ^ l := by
      simp [rubi459r6Nondeg, eval, Interp.real, hkM, hkn, hkj, hkp, Fn.csc]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hX : (env "b" + 2 * env "c" * ((Real.sin (env "d" + env "e" * t))⁻¹) ^ k) ^ (2 * l) =
        (4 * env "c" *
            (env "a" + env "b" * ((Real.sin (env "d" + env "e" * t))⁻¹) ^ k + env "c" *
            ((Real.sin (env "d" + env "e" * t))⁻¹) ^ j)) ^ l := by
      rw [zpow_mul, ← hsq t]
      norm_cast
    rw [hX, mul_zpow, mul_zpow]
    field_simp

end OSR.IntegrationRec251
