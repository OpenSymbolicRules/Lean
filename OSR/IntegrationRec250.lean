import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: further splits

Proofs over ℝ and ℂ of RUBI 4.1.2.2 #6 (the split of `(g cos u)^p (d sin u)^n (a + b sin u)`
into `a (g cos u)^p (d sin u)^n + (b / d) (g cos u)^p (d sin u)^(n + 1)`), and over ℝ only of
the quotients 4.5.4.1 #10, 4.5.3.1 #3 and 4.5.1.2 #52 by `a + b csc u` (no complex
`transc1#csc`) and of 4.1.7 #4, which splits `(A + B sin^2 u) / sqrt(a + b sin^2 u)` (no
complex `arith1#root`). -/

namespace OSR.IntegrationRec250

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 4.1.2.2 #6 -/

theorem rubi4122r6Nondeg_real : rubi4122r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4122r6Nondeg.conditions rubi4122r6Nondeg.body
    rubi4122r6Nondeg.result rubi4122r6Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4122r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r6Nondeg, Defined, eval, Interp.real, hkp] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r6Nondeg, Defined, eval, Interp.real, hkp, hkn] at h
  have en1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4122r6Nondeg.body →
      (q < 0 → env "g" * Real.cos (env "e" + env "f" * w) ≠ 0) ∧
          (k < 0 → env "d" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4122r6Nondeg, Defined, eval, Interp.real, hkp, hkn] at h
    simp only [ne_eq, mul_eq_zero, not_or]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp only [ne_eq, mul_eq_zero, not_or] at h
      simp [Defined, eval, Interp.real, hkp, hkn]
      exact h
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp only [ne_eq, mul_eq_zero, not_or] at h
      simp [Defined, eval, Interp.real, hkp, en1]
      exact ⟨h.1, fun h' => h.2 (by omega)⟩
  · filter_upwards with w
    simp [rubi4122r6Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hd]
  · simp only [rubi4122r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "g" * Real.cos (env "e" + env "f" * t)) ^ q *
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkp, hkn]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "g" * Real.cos (env "e" + env "f" * t)) ^ q *
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ (k + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkp, en1]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4122r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r6Nondeg.result) =
        fun w => env "a" * Φ "I1" w + env "b" * (env "d")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4122r6Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4122r6Nondeg.body =
        (env "g" * Real.cos (env "e" + env "f" * t)) ^ q *
            (env "d" * Real.sin (env "e" + env "f" * t)) ^ k *
          (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      simp [rubi4122r6Nondeg, eval, Interp.real, hkp, hkn]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have e1 : (env "d" * Real.sin (env "e" + env "f" * t)) ^ (k + 1) =
        (env "d" * Real.sin (env "e" + env "f" * t)) ^ k *
        (env "d" * Real.sin (env "e" + env "f" * t)) := by
      by_cases hm : k < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) k
      · lift k to ℕ using (by omega)
        rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1]
    generalize (env "g" * Real.cos (env "e" + env "f" * t)) ^ q = P
    generalize (env "d" * Real.sin (env "e" + env "f" * t)) ^ k = Q
    field_simp

theorem rubi4122r6Nondeg_complex : rubi4122r6Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4122r6Nondeg.conditions rubi4122r6Nondeg.body
    rubi4122r6Nondeg.result rubi4122r6Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4122r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkp : intValue? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r6Nondeg, Defined, eval, Interp.complex, hkp] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4122r6Nondeg, Defined, eval, Interp.complex, hkp, hkn] at h
  have en1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4122r6Nondeg.body →
      (q < 0 → env "g" * Complex.cos (env "e" + env "f" * w) ≠ 0) ∧
          (k < 0 → env "d" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4122r6Nondeg, Defined, eval, Interp.complex, hkp, hkn] at h
    simp only [ne_eq, mul_eq_zero, not_or]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4122r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp only [ne_eq, mul_eq_zero, not_or] at h
      simp [Defined, eval, Interp.complex, hkp, hkn]
      exact h
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp only [ne_eq, mul_eq_zero, not_or] at h
      simp [Defined, eval, Interp.complex, hkp, en1]
      exact ⟨h.1, fun h' => h.2 (by omega)⟩
  · filter_upwards with w
    simp [rubi4122r6Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hd]
  · simp only [rubi4122r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "g" * Complex.cos (env "e" + env "f" * t)) ^ q *
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, hkp, hkn]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "g" * Complex.cos (env "e" + env "f" * t)) ^ q *
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ (k + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkp, en1]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4122r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4122r6Nondeg.result) =
        fun w => env "a" * Φ "I1" w + env "b" * (env "d")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4122r6Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4122r6Nondeg.body =
        (env "g" * Complex.cos (env "e" + env "f" * t)) ^ q *
            (env "d" * Complex.sin (env "e" + env "f" * t)) ^ k *
          (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      simp [rubi4122r6Nondeg, eval, Interp.complex, hkp, hkn]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have e1 : (env "d" * Complex.sin (env "e" + env "f" * t)) ^ (k + 1) =
        (env "d" * Complex.sin (env "e" + env "f" * t)) ^ k *
        (env "d" * Complex.sin (env "e" + env "f" * t)) := by
      by_cases hm : k < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) k
      · lift k to ℕ using (by omega)
        rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1]
    generalize (env "g" * Complex.cos (env "e" + env "f" * t)) ^ q = P
    generalize (env "d" * Complex.sin (env "e" + env "f" * t)) ^ k = Q
    field_simp

/-! ## RUBI 4.5.4.1 #10, 4.5.3.1 #3, 4.5.1.2 #52 and 4.1.7 #4 (over ℝ) -/

theorem rubi4541r10Nondeg_real : rubi4541r10Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4541r10Nondeg.conditions rubi4541r10Nondeg.body
    rubi4541r10Nondeg.result rubi4541r10Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4541r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4541r10Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧ env "a" + env "b" *
          (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0 := by
    intro w h
    simp [rubi4541r10Nondeg, Defined, eval, Interp.real, ivm1R, iv2R, Fn.csc] at h
    tauto
  obtain ⟨hs0, hq0⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4541r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, (hD w hw).1]
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, ivm1R, Fn.csc, (hD w hw).1, (hD w hw).2]
  · filter_upwards with w
    simp [rubi4541r10Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4541r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((Real.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, Fn.csc]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "A" * env "b" +
        (env "b" * env "B" - env "a" * env "C") * (Real.sin (env "e" + env "f" * t))⁻¹) *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ivm1R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4541r10Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4541r10Nondeg.result) =
        fun w => env "C" * (env "b")⁻¹ * Φ "I1" w + (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4541r10Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4541r10Nondeg.body =
        (env "A" + env "B" * (Real.sin (env "e" + env "f" * t))⁻¹ + env "C" *
            ((Real.sin (env "e" + env "f" * t))⁻¹) ^ 2) *
          (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)⁻¹ := by
      simp [rubi4541r10Nondeg, eval, Interp.real, ivm1R, iv2R, Fn.csc]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    generalize Real.sin (env "e" + env "f" * t) = S at hs0 hq0 ⊢
    rw [show env "a" + env "b" * S⁻¹ = (env "a" * S + env "b") / S by field_simp] at hq0 ⊢
    have hq1 : env "a" * S + env "b" ≠ 0 := by
      intro h0; apply hq0; rw [h0, zero_div]
    generalize hE : env "a" * S + env "b" = D at hq1 ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi4531r3Nondeg_real : rubi4531r3Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r3Nondeg.conditions rubi4531r3Nondeg.body
    rubi4531r3Nondeg.result rubi4531r3Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4531r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r3Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧ env "a" + env "b" *
          (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0 := by
    intro w h
    simp [rubi4531r3Nondeg, Defined, eval, Interp.real, ivm1R, Fn.csc] at h
    tauto
  obtain ⟨hs0, hq0⟩ := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, (hD w hw).1]
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, ivm1R, Fn.csc, (hD w hw).1, (hD w hw).2]
  · filter_upwards with w
    simp [rubi4531r3Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4531r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((Real.sin (env "e" + env "f" * t))⁻¹) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, Fn.csc]
    have hΦ2' : HasDerivAt (Φ "I2") ((Real.sin (env "e" + env "f" * t))⁻¹ *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ivm1R, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4531r3Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4531r3Nondeg.result) =
        fun w => env "B" * (env "b")⁻¹ * Φ "I1" w +
          (env "A" * env "b" - env "a" * env "B") * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4531r3Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r3Nondeg.body =
        (Real.sin (env "e" + env "f" * t))⁻¹ *
            (env "A" + env "B" * (Real.sin (env "e" + env "f" * t))⁻¹) *
            (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹)⁻¹ := by
      simp [rubi4531r3Nondeg, eval, Interp.real, ivm1R, Fn.csc]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    generalize Real.sin (env "e" + env "f" * t) = S at hs0 hq0 ⊢
    rw [show env "a" + env "b" * S⁻¹ = (env "a" * S + env "b") / S by field_simp] at hq0 ⊢
    have hq1 : env "a" * S + env "b" ≠ 0 := by
      intro h0; apply hq0; rw [h0, zero_div]
    generalize hE : env "a" * S + env "b" = D at hq1 ⊢
    field_simp
    rw [← hE]
    ring

theorem rubi4512r52Nondeg_real : rubi4512r52Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4512r52Nondeg.conditions rubi4512r52Nondeg.body
    rubi4512r52Nondeg.result rubi4512r52Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4512r52Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4512r52Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4512r52Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "a" + env "b" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0) := by
    intro w h
    simp [rubi4512r52Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
    tauto
  have hs0 := (hD t hF.self_of_nhds).1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4512r52Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, hkm, Fn.csc, (hD w hw).1]
      exact (hD w hw).2
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, em1, Fn.csc, (hD w hw).1]
      exact fun h => (hD w hw).2 (by omega)
  · filter_upwards with w
    simp [rubi4512r52Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4512r52Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((Real.sin (env "e" + env "f" * t))⁻¹ *
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, hkm, Fn.csc]
    have hΦ2' : HasDerivAt (Φ "I2")
        ((Real.sin (env "e" + env "f" * t))⁻¹ *
            (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, em1, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4512r52Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4512r52Nondeg.result) =
        fun w => -(env "a" * (env "b")⁻¹) * Φ "I1" w + (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi4512r52Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4512r52Nondeg.body =
        ((Real.sin (env "e" + env "f" * t))⁻¹) ^ 2 *
            (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m := by
      simp [rubi4512r52Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have e1 : (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1) =
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
            (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1]
    generalize (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m = Q
    generalize Real.sin (env "e" + env "f" * t) = S at hs0 ⊢
    field_simp
    ring

theorem rubi417r4Nondeg_real : rubi417r4Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi417r4Nondeg.conditions rubi417r4Nondeg.body
    rubi417r4Nondeg.result rubi417r4Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi417r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi417r4Nondeg.body →
      0 < env "a" + env "b" * Real.sin (env "e" + env "f" * w) ^ 2 := by
    intro w h
    simp [rubi417r4Nondeg, Defined, eval, Interp.real, ivm1R, iv2R] at h
    have hs : Real.sqrt (env "a" + env "b" * Real.sin (env "e" + env "f" * w) ^ 2) ≠ 0 := by tauto
    exact Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs))
  have hQ0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi417r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, iv2R, (hD w hw).le]
    · filter_upwards [hF] with w hw
      simp [Defined, eval, Interp.real, ivm1R, iv2R, (hD w hw).le, (hD w hw).ne']
  · filter_upwards with w
    simp [rubi417r4Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi417r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (Real.sqrt (env "a" + env "b" *
        Real.sin (env "e" + env "f" * t) ^ 2)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, iv2R]
    have hΦ2' : HasDerivAt (Φ "I2") ((Real.sqrt (env "a" + env "b" *
        Real.sin (env "e" + env "f" * t) ^ 2))⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, ivm1R, iv2R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi417r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi417r4Nondeg.result) =
        fun w => env "B" * (env "b")⁻¹ * Φ "I1" w +
          (env "A" * env "b" - env "a" * env "B") * (env "b")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi417r4Nondeg, eval, recEnv, Interp.real, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
      ring
    have hEF : eval Interp.real (Function.update env "x" t) rubi417r4Nondeg.body =
        (env "A" + env "B" * Real.sin (env "e" + env "f" * t) ^ 2) *
            (Real.sqrt (env "a" + env "b" * Real.sin (env "e" + env "f" * t) ^ 2))⁻¹ := by
      simp [rubi417r4Nondeg, eval, Interp.real, ivm1R, iv2R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hS2 : Real.sqrt (env "a" + env "b" * Real.sin (env "e" + env "f" * t) ^ 2) ^ 2 = env "a" +
        env "b" * Real.sin (env "e" + env "f" * t) ^ 2 := Real.sq_sqrt hQ0.le
    have hS0 : Real.sqrt (env "a" + env "b" * Real.sin (env "e" + env "f" * t) ^ 2) ≠ 0 :=
        (Real.sqrt_pos.mpr hQ0).ne'
    generalize Real.sin (env "e" + env "f" * t) = s at hS2 hS0 ⊢
    generalize Real.sqrt (env "a" + env "b" * s ^ 2) = R at hS2 hS0 ⊢
    field_simp
    linear_combination env "B" * hS2

end OSR.IntegrationRec250
