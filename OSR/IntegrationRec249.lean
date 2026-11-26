import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: perfect-square trinomials

Proofs of RUBI 4.1.9 #1 and #2, 4.3.9 #1 and #2 (over ℝ and ℂ) and 4.5.9 #1 and #2 (over ℝ,
`sec` and `csc` having no complex interpretation): when `b^2 = 4 a c`,
`(a + b y^n + c y^(2 n))^p = (b + 2 c y^n)^(2 p) / (4^p c^p)` for an integer `p`, with
`y` one of `sin`, `cos`, `tan`, `cot`, `sec`, `csc` of `d + e x`. -/

namespace OSR.IntegrationRec249

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 4.1.9 #1 -/

theorem rubi419r1Nondeg_real : rubi419r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi419r1Nondeg.conditions rubi419r1Nondeg.body
    rubi419r1Nondeg.result rubi419r1Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi419r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi419r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r1Nondeg, Defined, eval, Interp.real, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r1Nondeg, Defined, eval, Interp.real, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r1Nondeg, Defined, eval, Interp.real, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi419r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi419r1Nondeg.body →
      (k < 0 → Real.sin (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Real.sin (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.sin (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi419r1Nondeg, Defined, eval, Interp.real, hkn, hkj, hkp] at h
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
  · simp only [rubi419r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hTw, hQw⟩ := hD w hw
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
    simp [Defined, eval, Interp.real, hkn, e2p]
    exact ⟨hTw, hB⟩
  · filter_upwards with w
    simp [rubi419r1Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi419r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" + 2 * env "c" * (Real.sin (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi419r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi419r1Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi419r1Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi419r1Nondeg.body =
        (env "a" + env "b" * (Real.sin (env "d" + env "e" * t)) ^ k + env "c" *
        (Real.sin (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi419r1Nondeg, eval, Interp.real, hkn, hkj, hkp]
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

theorem rubi419r1Nondeg_complex : rubi419r1Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi419r1Nondeg.conditions rubi419r1Nondeg.body
    rubi419r1Nondeg.result rubi419r1Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi419r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi419r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r1Nondeg, Defined, eval, Interp.complex, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r1Nondeg, Defined, eval, Interp.complex, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r1Nondeg, Defined, eval, Interp.complex, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi419r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi419r1Nondeg.body →
      (k < 0 → Complex.sin (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Complex.sin (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.sin (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi419r1Nondeg, Defined, eval, Interp.complex, hkn, hkj, hkp] at h
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
  · simp only [rubi419r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hTw, hQw⟩ := hD w hw
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
    simp [Defined, eval, Interp.complex, hkn, e2p]
    exact ⟨hTw, hB⟩
  · filter_upwards with w
    simp [rubi419r1Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi419r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" + 2 * env "c" * (Complex.sin (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkn, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi419r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi419r1Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi419r1Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi419r1Nondeg.body =
        (env "a" + env "b" * (Complex.sin (env "d" + env "e" * t)) ^ k + env "c" *
        (Complex.sin (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi419r1Nondeg, eval, Interp.complex, hkn, hkj, hkp]
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

/-! ## RUBI 4.1.9 #2 -/

theorem rubi419r2Nondeg_real : rubi419r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi419r2Nondeg.conditions rubi419r2Nondeg.body
    rubi419r2Nondeg.result rubi419r2Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi419r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi419r2Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r2Nondeg, Defined, eval, Interp.real, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r2Nondeg, Defined, eval, Interp.real, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r2Nondeg, Defined, eval, Interp.real, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi419r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi419r2Nondeg.body →
      (k < 0 → Real.cos (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Real.cos (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.cos (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi419r2Nondeg, Defined, eval, Interp.real, hkn, hkj, hkp] at h
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
  · simp only [rubi419r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hTw, hQw⟩ := hD w hw
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
    simp [Defined, eval, Interp.real, hkn, e2p]
    exact ⟨hTw, hB⟩
  · filter_upwards with w
    simp [rubi419r2Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi419r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" + 2 * env "c" * (Real.cos (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi419r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi419r2Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi419r2Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi419r2Nondeg.body =
        (env "a" + env "b" * (Real.cos (env "d" + env "e" * t)) ^ k + env "c" *
        (Real.cos (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi419r2Nondeg, eval, Interp.real, hkn, hkj, hkp]
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

theorem rubi419r2Nondeg_complex : rubi419r2Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi419r2Nondeg.conditions rubi419r2Nondeg.body
    rubi419r2Nondeg.result rubi419r2Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi419r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi419r2Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r2Nondeg, Defined, eval, Interp.complex, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r2Nondeg, Defined, eval, Interp.complex, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi419r2Nondeg, Defined, eval, Interp.complex, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi419r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi419r2Nondeg.body →
      (k < 0 → Complex.cos (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Complex.cos (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.cos (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi419r2Nondeg, Defined, eval, Interp.complex, hkn, hkj, hkp] at h
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
  · simp only [rubi419r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hTw, hQw⟩ := hD w hw
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
    simp [Defined, eval, Interp.complex, hkn, e2p]
    exact ⟨hTw, hB⟩
  · filter_upwards with w
    simp [rubi419r2Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi419r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" + 2 * env "c" * (Complex.cos (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkn, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi419r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi419r2Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi419r2Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi419r2Nondeg.body =
        (env "a" + env "b" * (Complex.cos (env "d" + env "e" * t)) ^ k + env "c" *
        (Complex.cos (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi419r2Nondeg, eval, Interp.complex, hkn, hkj, hkp]
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

/-! ## RUBI 4.3.9 #1 -/

theorem rubi439r1Nondeg_real : rubi439r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi439r1Nondeg.conditions rubi439r1Nondeg.body
    rubi439r1Nondeg.result rubi439r1Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi439r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r1Nondeg, Defined, eval, Interp.real, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r1Nondeg, Defined, eval, Interp.real, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r1Nondeg, Defined, eval, Interp.real, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi439r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi439r1Nondeg.body →
      Real.cos (env "d" + env "e" * w) ≠ 0 ∧ (k < 0 → Real.tan (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Real.tan (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.tan (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi439r1Nondeg, Defined, eval, Interp.real, hkn, hkj, hkp] at h
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
  · simp only [rubi439r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hxw, hTw, hQw⟩ := hD w hw
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
    simp [Defined, eval, Interp.real, hkn, e2p, hxw]
    exact ⟨hTw, hB⟩
  · filter_upwards with w
    simp [rubi439r1Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" + 2 * env "c" * (Real.tan (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi439r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r1Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r1Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi439r1Nondeg.body =
        (env "a" + env "b" * (Real.tan (env "d" + env "e" * t)) ^ k + env "c" *
        (Real.tan (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi439r1Nondeg, eval, Interp.real, hkn, hkj, hkp]
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

theorem rubi439r1Nondeg_complex : rubi439r1Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi439r1Nondeg.conditions rubi439r1Nondeg.body
    rubi439r1Nondeg.result rubi439r1Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi439r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r1Nondeg, Defined, eval, Interp.complex, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r1Nondeg, Defined, eval, Interp.complex, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r1Nondeg, Defined, eval, Interp.complex, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi439r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi439r1Nondeg.body →
      Complex.cos (env "d" + env "e" * w) ≠ 0 ∧ (k < 0 → Complex.tan (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Complex.tan (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.tan (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi439r1Nondeg, Defined, eval, Interp.complex, hkn, hkj, hkp] at h
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
  · simp only [rubi439r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hxw, hTw, hQw⟩ := hD w hw
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
    simp [Defined, eval, Interp.complex, hkn, e2p, hxw]
    exact ⟨hTw, hB⟩
  · filter_upwards with w
    simp [rubi439r1Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" + 2 * env "c" * (Complex.tan (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkn, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi439r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r1Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r1Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi439r1Nondeg.body =
        (env "a" + env "b" * (Complex.tan (env "d" + env "e" * t)) ^ k + env "c" *
        (Complex.tan (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi439r1Nondeg, eval, Interp.complex, hkn, hkj, hkp]
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

/-! ## RUBI 4.3.9 #2 -/

theorem rubi439r2Nondeg_real : rubi439r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi439r2Nondeg.conditions rubi439r2Nondeg.body
    rubi439r2Nondeg.result rubi439r2Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi439r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r2Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r2Nondeg, Defined, eval, Interp.real, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r2Nondeg, Defined, eval, Interp.real, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r2Nondeg, Defined, eval, Interp.real, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi439r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi439r2Nondeg.body →
      Real.sin (env "d" + env "e" * w) ≠ 0 ∧ (k < 0 → Real.cot (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Real.cot (env "d" + env "e" * w)) ^ k + env "c" *
          (Real.cot (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi439r2Nondeg, Defined, eval, Interp.real, hkn, hkj, hkp] at h
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
  · simp only [rubi439r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hxw, hTw, hQw⟩ := hD w hw
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
    simp [Defined, eval, Interp.real, hkn, e2p, hxw]
    exact ⟨hTw, hB⟩
  · filter_upwards with w
    simp [rubi439r2Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" + 2 * env "c" * (Real.cot (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, e2p]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi439r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r2Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r2Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi439r2Nondeg.body =
        (env "a" + env "b" * (Real.cot (env "d" + env "e" * t)) ^ k + env "c" *
        (Real.cot (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi439r2Nondeg, eval, Interp.real, hkn, hkj, hkp]
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

theorem rubi439r2Nondeg_complex : rubi439r2Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi439r2Nondeg.conditions rubi439r2Nondeg.body
    rubi439r2Nondeg.result rubi439r2Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi439r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi439r2Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r2Nondeg, Defined, eval, Interp.complex, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r2Nondeg, Defined, eval, Interp.complex, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi439r2Nondeg, Defined, eval, Interp.complex, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℂ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi439r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi439r2Nondeg.body →
      Complex.sin (env "d" + env "e" * w) ≠ 0 ∧ (k < 0 → Complex.cot (env "d" + env "e" * w) ≠ 0) ∧
          (l < 0 → env "a" + env "b" * (Complex.cot (env "d" + env "e" * w)) ^ k + env "c" *
          (Complex.cot (env "d" + env "e" * w)) ^ j ≠ 0) := by
    intro w h
    simp [rubi439r2Nondeg, Defined, eval, Interp.complex, hkn, hkj, hkp] at h
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
  · simp only [rubi439r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hxw, hTw, hQw⟩ := hD w hw
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
    simp [Defined, eval, Interp.complex, hkn, e2p, hxw]
    exact ⟨hTw, hB⟩
  · filter_upwards with w
    simp [rubi439r2Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi439r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" + 2 * env "c" * (Complex.cot (env "d" + env "e" * t)) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkn, e2p]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi439r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi439r2Nondeg.result) =
        fun w => ((4 : ℂ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi439r2Nondeg, eval, recEnv, Interp.complex, ivm1C, hkp]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi439r2Nondeg.body =
        (env "a" + env "b" * (Complex.cot (env "d" + env "e" * t)) ^ k + env "c" *
        (Complex.cot (env "d" + env "e" * t)) ^ j) ^ l := by
      simp [rubi439r2Nondeg, eval, Interp.complex, hkn, hkj, hkp]
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

/-! ## RUBI 4.5.9 #1 -/

theorem rubi459r1Nondeg_real : rubi459r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi459r1Nondeg.conditions rubi459r1Nondeg.body
    rubi459r1Nondeg.result rubi459r1Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi459r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi459r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r1Nondeg, Defined, eval, Interp.real, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r1Nondeg, Defined, eval, Interp.real, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r1Nondeg, Defined, eval, Interp.real, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi459r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi459r1Nondeg.body →
      Real.cos (env "d" + env "e" * w) ≠ 0 ∧ (k < 0 → (Real.cos (env "d" + env "e" * w))⁻¹ ≠ 0) ∧
          (l < 0 → env "a" + env "b" * ((Real.cos (env "d" + env "e" * w))⁻¹) ^ k + env "c" *
          ((Real.cos (env "d" + env "e" * w))⁻¹) ^ j ≠ 0) := by
    intro w h
    simp [rubi459r1Nondeg, Defined, eval, Interp.real, hkn, hkj, hkp, Fn.sec] at h ⊢
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
  · simp only [rubi459r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hxw, hTw, hQw⟩ := hD w hw
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
    simp [Defined, eval, Interp.real, hkn, e2p, Fn.sec, hxw] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi459r1Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi459r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" + 2 * env "c" * ((Real.cos (env "d" + env "e" * t))⁻¹) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, e2p, Fn.sec]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi459r1Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi459r1Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi459r1Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi459r1Nondeg.body =
        (env "a" + env "b" * ((Real.cos (env "d" + env "e" * t))⁻¹) ^ k + env "c" *
        ((Real.cos (env "d" + env "e" * t))⁻¹) ^ j) ^ l := by
      simp [rubi459r1Nondeg, eval, Interp.real, hkn, hkj, hkp, Fn.sec]
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

/-! ## RUBI 4.5.9 #2 -/

theorem rubi459r2Nondeg_real : rubi459r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi459r2Nondeg.conditions rubi459r2Nondeg.body
    rubi459r2Nondeg.result rubi459r2Nondeg.integrals
  intro env hc t hF
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi459r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "b" ^ 2 - 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul
      (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0))
      (by simp [rubi459r2Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r2Nondeg, Defined, eval, Interp.real, hkn] at h
  rcases hkj : intValue? (env "n2") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r2Nondeg, Defined, eval, Interp.real, hkn, hkj] at h
  rcases hkp : intValue? (env "p") with _ | l
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi459r2Nondeg, Defined, eval, Interp.real, hkn, hkj, hkp] at h
  have hjk : j = 2 * k := by
    have h1 := (intValue?_eq _ _).1 hkj
    rw [hn2, (intValue?_eq _ _).1 hkn] at h1
    exact_mod_cast h1.symm
  have e2p : intValue? (2 * env "p") = some (2 * l) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkp]; push_cast; ring)
  have hW0 : (l < 0 → env "c" ≠ 0) ∧ (4 : ℝ) ^ l ≠ 0 ∧ env "c" ^ l ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p")))
      (.int 0)) (by simp [rubi459r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, hkp] using h
  obtain ⟨hWc, h4l, hcl⟩ := hW0
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi459r2Nondeg.body →
      Real.sin (env "d" + env "e" * w) ≠ 0 ∧ (k < 0 → (Real.sin (env "d" + env "e" * w))⁻¹ ≠ 0) ∧
          (l < 0 → env "a" + env "b" * ((Real.sin (env "d" + env "e" * w))⁻¹) ^ k + env "c" *
          ((Real.sin (env "d" + env "e" * w))⁻¹) ^ j ≠ 0) := by
    intro w h
    simp [rubi459r2Nondeg, Defined, eval, Interp.real, hkn, hkj, hkp, Fn.csc] at h ⊢
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
  · simp only [rubi459r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hxw, hTw, hQw⟩ := hD w hw
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
    simp [Defined, eval, Interp.real, hkn, e2p, Fn.csc, hxw] at hB ⊢
    tauto
  · filter_upwards with w
    simp [rubi459r2Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hkp, h4l, hcl]
    exact hWc
  · simp only [rubi459r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1")
        ((env "b" + 2 * env "c" * ((Real.sin (env "d" + env "e" * t))⁻¹) ^ k) ^ (2 * l)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkn, e2p, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi459r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi459r2Nondeg.result) =
        fun w => ((4 : ℝ) ^ l * env "c" ^ l)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi459r2Nondeg, eval, recEnv, Interp.real, ivm1R, hkp]
    have hEF : eval Interp.real (Function.update env "x" t) rubi459r2Nondeg.body =
        (env "a" + env "b" * ((Real.sin (env "d" + env "e" * t))⁻¹) ^ k + env "c" *
        ((Real.sin (env "d" + env "e" * t))⁻¹) ^ j) ^ l := by
      simp [rubi459r2Nondeg, eval, Interp.real, hkn, hkj, hkp, Fn.csc]
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

end OSR.IntegrationRec249
