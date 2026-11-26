import OSR.IntegrationNum1

/-! # Strengthened inverse tangent and trigonometric variants: rewrites and splits

Proofs over ℝ and ℂ of RUBI 5.3.1 (power) #5 and 5.3.2 #13, which rewrite `arctan(c x^n)` as
`arctan(1/(x^(-n)/c))` for an integer `n < 0` (the arguments coincide where `x ≠ 0`), and of
the algebraic splits 4.1.2.1 #56 (`(b sin u)^m (c + d sin u)^2`), 4.1.4.1 #7 and 4.3.4.1 #4
(`(a + b sin u)^m (A + C sin^2 u)` and its `tan` analogue when `A b^2 + a^2 C = 0`); and over ℝ
only (no complex `transc1#csc`) of the splits 4.5.4.1 #7 and 4.5.1.2 #2. -/

namespace OSR.IntegrationRec248

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 5.3.1 (power) #5 -/

theorem rubi531r5Nondeg_real : rubi531r5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi531r5Nondeg.conditions rubi531r5Nondeg.body
    rubi531r5Nondeg.result rubi531r5Nondeg.integrals
  intro env hc t hF
  have hcz : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi531r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hneg : env "n" < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi531r5Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpos : 1 < env "p" := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi531r5Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi531r5Nondeg, Defined, eval, Interp.real, hkp] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi531r5Nondeg, Defined, eval, Interp.real, hkp, hkn] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (n : ℝ) := (intValue?_eq _ _).1 hkn
  have hk1 : 1 < k := by
    have : (1 : ℝ) < k := hp ▸ hpos
    exact_mod_cast this
  have hn0 : n < 0 := by rw [hn] at hneg; exact_mod_cast hneg
  have hk0 : ¬ k < 0 := by omega
  have ivn : intValue? (-env "n") = some (-n) := (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi531r5Nondeg.body → w ≠ 0 := by
    intro w h
    simp [rubi531r5Nondeg, Defined, eval, Interp.real, hkp, hkn, hk0, hn0] at h
    tauto
  have hEq : ∀ w, eval Interp.real (Function.update env "x" w) rubi531r5Nondeg.body =
      eval Interp.real (Function.update env "x" w) (rubi531r5Nondeg.integrals.head!.2) := by
    intro w
    simp [rubi531r5Nondeg, eval, Interp.real, hkp, hkn, ivn, ivm1R]
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi531r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hw0 := hD w hw
    simp [rubi531r5Nondeg, Defined, eval, Interp.real, hkp, hkn, hk0, hn0] at hw
    simp [Defined, eval, Interp.real, hkp, ivn, ivm1R, hk0, hw0, hcz, zpow_ne_zero n hw0]
  · filter_upwards with w
    simp [rubi531r5Nondeg, Defined]
  · simp only [rubi531r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi531r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi531r5Nondeg.result) = Φ "I1" := by
      funext w
      simp [rubi531r5Nondeg, eval, recEnv]
    rw [hfun]
    convert hΦ using 1
    simpa [rubi531r5Nondeg] using hEq t

theorem rubi531r5Nondeg_complex : rubi531r5Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi531r5Nondeg.conditions rubi531r5Nondeg.body
    rubi531r5Nondeg.result rubi531r5Nondeg.integrals
  intro env hc t hF
  have hcz : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi531r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hneg : (env "n").re < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi531r5Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    exact h.2
  have hpos : 1 < (env "p").re := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi531r5Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    exact h.2
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi531r5Nondeg, Defined, eval, Interp.complex, hkp] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi531r5Nondeg, Defined, eval, Interp.complex, hkp, hkn] at h
  have hp : env "p" = (k : ℂ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (n : ℂ) := (intValue?_eq _ _).1 hkn
  have hk1 : 1 < k := by
    rw [hp] at hpos
    have : (1 : ℝ) < k := by simpa using hpos
    exact_mod_cast this
  have hn0 : n < 0 := by
    rw [hn] at hneg
    have : (n : ℝ) < 0 := by simpa using hneg
    exact_mod_cast this
  have hk0 : ¬ k < 0 := by omega
  have ivn : intValue? (-env "n") = some (-n) := (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi531r5Nondeg.body → w ≠ 0 :=
      by
    intro w h
    simp [rubi531r5Nondeg, Defined, eval, Interp.complex, hkp, hkn, hk0, hn0] at h
    tauto
  have hEq : ∀ w, eval Interp.complex (Function.update env "x" w) rubi531r5Nondeg.body =
      eval Interp.complex (Function.update env "x" w) (rubi531r5Nondeg.integrals.head!.2) := by
    intro w
    simp [rubi531r5Nondeg, eval, Interp.complex, hkp, hkn, ivn, ivm1C]
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi531r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hw0 := hD w hw
    simp [rubi531r5Nondeg, Defined, eval, Interp.complex, hkp, hkn, hk0, hn0] at hw
    simp [Defined, eval, Interp.complex, hkp, ivn, ivm1C, hk0, hw0, hcz, zpow_ne_zero n hw0]
    tauto
  · filter_upwards with w
    simp [rubi531r5Nondeg, Defined]
  · simp only [rubi531r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi531r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi531r5Nondeg.result) = Φ "I1" := by
      funext w
      simp [rubi531r5Nondeg, eval, recEnv]
    rw [hfun]
    convert hΦ using 1
    simpa [rubi531r5Nondeg] using hEq t

/-! ## RUBI 5.3.2 #13 -/

theorem rubi532r13Nondeg_real : rubi532r13Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi532r13Nondeg.conditions rubi532r13Nondeg.body
    rubi532r13Nondeg.result rubi532r13Nondeg.integrals
  intro env hc t hF
  have hcz : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi532r13Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hneg : env "n" < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi532r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpos : 1 < env "p" := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi532r13Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi532r13Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi532r13Nondeg, Defined, eval, Interp.real, hkp, hkm] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi532r13Nondeg, Defined, eval, Interp.real, hkp, hkn, hkm] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (n : ℝ) := (intValue?_eq _ _).1 hkn
  have hk1 : 1 < k := by
    have : (1 : ℝ) < k := hp ▸ hpos
    exact_mod_cast this
  have hn0 : n < 0 := by rw [hn] at hneg; exact_mod_cast hneg
  have hk0 : ¬ k < 0 := by omega
  have ivn : intValue? (-env "n") = some (-n) := (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi532r13Nondeg.body → w ≠ 0 := by
    intro w h
    simp [rubi532r13Nondeg, Defined, eval, Interp.real, hkp, hkn, hk0, hn0, hkm] at h
    tauto
  have hEq : ∀ w, eval Interp.real (Function.update env "x" w) rubi532r13Nondeg.body =
      eval Interp.real (Function.update env "x" w) (rubi532r13Nondeg.integrals.head!.2) := by
    intro w
    simp [rubi532r13Nondeg, eval, Interp.real, hkp, hkn, ivn, ivm1R, hkm]
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi532r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hw0 := hD w hw
    simp [rubi532r13Nondeg, Defined, eval, Interp.real, hkp, hkn, hk0, hn0, hkm] at hw
    simp [Defined, eval, Interp.real, hkp, ivn, ivm1R, hk0, hw0, hcz, zpow_ne_zero n hw0, hkm]
  · filter_upwards with w
    simp [rubi532r13Nondeg, Defined]
  · simp only [rubi532r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi532r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi532r13Nondeg.result) = Φ "I1" := by
      funext w
      simp [rubi532r13Nondeg, eval, recEnv]
    rw [hfun]
    convert hΦ using 1
    simpa [rubi532r13Nondeg] using hEq t

theorem rubi532r13Nondeg_complex : rubi532r13Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi532r13Nondeg.conditions rubi532r13Nondeg.body
    rubi532r13Nondeg.result rubi532r13Nondeg.integrals
  intro env hc t hF
  have hcz : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi532r13Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hneg : (env "n").re < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi532r13Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    exact h.2
  have hpos : 1 < (env "p").re := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi532r13Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex] at h
    exact h.2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi532r13Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi532r13Nondeg, Defined, eval, Interp.complex, hkp, hkm] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi532r13Nondeg, Defined, eval, Interp.complex, hkp, hkn, hkm] at h
  have hp : env "p" = (k : ℂ) := (intValue?_eq _ _).1 hkp
  have hn : env "n" = (n : ℂ) := (intValue?_eq _ _).1 hkn
  have hk1 : 1 < k := by
    rw [hp] at hpos
    have : (1 : ℝ) < k := by simpa using hpos
    exact_mod_cast this
  have hn0 : n < 0 := by
    rw [hn] at hneg
    have : (n : ℝ) < 0 := by simpa using hneg
    exact_mod_cast this
  have hk0 : ¬ k < 0 := by omega
  have ivn : intValue? (-env "n") = some (-n) := (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi532r13Nondeg.body →
      w ≠ 0 := by
    intro w h
    simp [rubi532r13Nondeg, Defined, eval, Interp.complex, hkp, hkn, hk0, hn0, hkm] at h
    tauto
  have hEq : ∀ w, eval Interp.complex (Function.update env "x" w) rubi532r13Nondeg.body =
      eval Interp.complex (Function.update env "x" w) (rubi532r13Nondeg.integrals.head!.2) := by
    intro w
    simp [rubi532r13Nondeg, eval, Interp.complex, hkp, hkn, ivn, ivm1C, hkm]
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi532r13Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hw0 := hD w hw
    simp [rubi532r13Nondeg, Defined, eval, Interp.complex, hkp, hkn, hk0, hn0, hkm] at hw
    simp [Defined, eval, Interp.complex, hkp, ivn, ivm1C, hk0, hw0, hcz, zpow_ne_zero n hw0, hkm]
    tauto
  · filter_upwards with w
    simp [rubi532r13Nondeg, Defined]
  · simp only [rubi532r13Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi532r13Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi532r13Nondeg.result) = Φ "I1" := by
      funext w
      simp [rubi532r13Nondeg, eval, recEnv]
    rw [hfun]
    convert hΦ using 1
    simpa [rubi532r13Nondeg] using hEq t

/-! ## RUBI 4.1.2.1 #56 -/

theorem rubi4121r56Nondeg_real : rubi4121r56Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r56Nondeg.conditions rubi4121r56Nondeg.body
    rubi4121r56Nondeg.result rubi4121r56Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4121r56Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r56Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r56Nondeg.body →
      True ∧ (m < 0 → env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r56Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
    simp only [ne_eq, mul_eq_zero, not_or, true_and]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r56Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := (hD w hw).2
      simp only [ne_eq, mul_eq_zero, not_or] at h
      simp [Defined, eval, Interp.real, em1]
      exact fun h' => h (by omega)
    · filter_upwards [hF] with w hw
      have h := (hD w hw).2
      simp only [ne_eq, mul_eq_zero, not_or] at h
      simp [Defined, eval, Interp.real, hkm, iv2R]
      exact h
  · filter_upwards with w
    simp [rubi4121r56Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4121r56Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, em1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "c" ^ 2 + env "d" ^ 2 * Real.sin (env "e" + env "f" * t) ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, iv2R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r56Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r56Nondeg.result) =
        fun w => 2 * env "c" * env "d" * (env "b")⁻¹ * Φ "I1" w + Φ "I2" w := by
      funext w
      simp [rubi4121r56Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r56Nondeg.body =
        (env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
            (env "c" + env "d" * Real.sin (env "e" + env "f" * t)) ^ 2 := by
      simp [rubi4121r56Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add hΦ2').congr_deriv ?_
    have e1 : (env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * Real.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1]
    generalize (env "b" * Real.sin (env "e" + env "f" * t)) ^ m = Q
    field_simp
    ring

theorem rubi4121r56Nondeg_complex : rubi4121r56Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r56Nondeg.conditions rubi4121r56Nondeg.body
    rubi4121r56Nondeg.result rubi4121r56Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4121r56Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r56Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r56Nondeg.body →
      True ∧ (m < 0 → env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4121r56Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
    simp only [ne_eq, mul_eq_zero, not_or, true_and]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r56Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := (hD w hw).2
      simp only [ne_eq, mul_eq_zero, not_or] at h
      simp [Defined, eval, Interp.complex, em1]
      exact fun h' => h (by omega)
    · filter_upwards [hF] with w hw
      have h := (hD w hw).2
      simp only [ne_eq, mul_eq_zero, not_or] at h
      simp [Defined, eval, Interp.complex, hkm, iv2C]
      exact h
  · filter_upwards with w
    simp [rubi4121r56Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, hb]
  · simp only [rubi4121r56Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m +
        1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.complex, em1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "c" ^ 2 + env "d" ^ 2 * Complex.sin (env "e" + env "f" * t) ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.complex, hkm, iv2C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r56Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r56Nondeg.result) =
        fun w => 2 * env "c" * env "d" * (env "b")⁻¹ * Φ "I1" w + Φ "I2" w := by
      funext w
      simp [rubi4121r56Nondeg, eval, recEnv, Interp.complex, ivm1C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r56Nondeg.body =
        (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
            (env "c" + env "d" * Complex.sin (env "e" + env "f" * t)) ^ 2 := by
      simp [rubi4121r56Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add hΦ2').congr_deriv ?_
    have e1 : (env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "b" * Complex.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1]
    generalize (env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = Q
    field_simp
    ring

/-! ## RUBI 4.1.4.1 #7 and 4.3.4.1 #4 -/

theorem rubi4141r7Nondeg_real : rubi4141r7Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4141r7Nondeg.conditions rubi4141r7Nondeg.body
    rubi4141r7Nondeg.result rubi4141r7Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4141r7Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
  have hrel : env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2)))
      (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4141r7Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hAC : env "A" = -(env "a" ^ 2 * env "C") / env "b" ^ 2 := by
    field_simp; linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r7Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4141r7Nondeg.body → True ∧
      (m < 0 → env "a" + env "b" * Real.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r7Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
    simp only [true_and]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := (hD w hw).2
    simp [Defined, eval, Interp.real, em1]
    exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4141r7Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi4141r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m +
        1) * (-env "a" + env "b" * Real.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4141r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r7Nondeg.result) = fun w => env "C" * (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r7Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4141r7Nondeg.body =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
            (env "A" + env "C" * Real.sin (env "e" + env "f" * t) ^ 2) := by
      simp [rubi4141r7Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1, hAC]
    generalize (env "a" + env "b" * Real.sin (env "e" + env "f" * t)) ^ m = Q
    field_simp
    ring

theorem rubi4141r7Nondeg_complex : rubi4141r7Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4141r7Nondeg.conditions rubi4141r7Nondeg.body
    rubi4141r7Nondeg.result rubi4141r7Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4141r7Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
  have hrel : env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2)))
      (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4141r7Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hAC : env "A" = -(env "a" ^ 2 * env "C") / env "b" ^ 2 := by
    field_simp; linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4141r7Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4141r7Nondeg.body → True ∧
      (m < 0 → env "a" + env "b" * Complex.sin (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4141r7Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
    simp only [true_and]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4141r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := (hD w hw).2
    simp [Defined, eval, Interp.complex, em1]
    exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4141r7Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb]
  · simp only [rubi4141r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.sin (env "e" + env "f" * t)) ^ (m + 1) *
        (-env "a" + env "b" * Complex.sin (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4141r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4141r7Nondeg.result) = fun w => env "C" * (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4141r7Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4141r7Nondeg.body =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
            (env "A" + env "C" * Complex.sin (env "e" + env "f" * t) ^ 2) := by
      simp [rubi4141r7Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1, hAC]
    generalize (env "a" + env "b" * Complex.sin (env "e" + env "f" * t)) ^ m = Q
    field_simp
    ring

theorem rubi4341r4Nondeg_real : rubi4341r4Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4341r4Nondeg.conditions rubi4341r4Nondeg.body
    rubi4341r4Nondeg.result rubi4341r4Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4341r4Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
  have hrel : env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2)))
      (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4341r4Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hAC : env "A" = -(env "a" ^ 2 * env "C") / env "b" ^ 2 := by
    field_simp; linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r4Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4341r4Nondeg.body →
      Real.cos (env "e" + env "f" * w) ≠ 0 ∧
      (m < 0 → env "a" + env "b" * Real.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r4Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := (hD w hw).2
    simp [Defined, eval, Interp.real, em1, (hD w hw).1]
    exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4341r4Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hb]
  · simp only [rubi4341r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m +
        1) * (env "a" + -env "b" * Real.tan (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4341r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4341r4Nondeg.result) = fun w => -env "C" * (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4341r4Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4341r4Nondeg.body =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
            (env "A" + env "C" * Real.tan (env "e" + env "f" * t) ^ 2) := by
      simp [rubi4341r4Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1, hAC]
    generalize (env "a" + env "b" * Real.tan (env "e" + env "f" * t)) ^ m = Q
    field_simp
    ring

theorem rubi4341r4Nondeg_complex : rubi4341r4Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4341r4Nondeg.conditions rubi4341r4Nondeg.body
    rubi4341r4Nondeg.result rubi4341r4Nondeg.integrals
  intro env hc t hF
  have hb2 : env "b" ^ 2 ≠ 0 := by
    have h := hc (.ne (.pow (.var "b") (.int 2)) (.int 0)) (by simp [rubi4341r4Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hb : env "b" ≠ 0 := fun h => hb2 (by rw [h]; ring)
  have hrel : env "A" * env "b" ^ 2 + env "a" ^ 2 * env "C" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2)))
      (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)) (by simp [rubi4341r4Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hAC : env "A" = -(env "a" ^ 2 * env "C") / env "b" ^ 2 := by
    field_simp; linear_combination hrel
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4341r4Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4341r4Nondeg.body →
      Complex.cos (env "e" + env "f" * w) ≠ 0 ∧
      (m < 0 → env "a" + env "b" * Complex.tan (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi4341r4Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := (hD w hw).2
    simp [Defined, eval, Interp.complex, em1, (hD w hw).1]
    exact fun h' => h (by omega)
  · filter_upwards with w
    simp [rubi4341r4Nondeg, Defined, eval, recEnv, Interp.complex, ivm1C, iv2C, hb]
  · simp only [rubi4341r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" *
        Complex.tan (env "e" + env "f" * t)) ^ (m + 1) *
        (env "a" + -env "b" * Complex.tan (env "e" + env "f" * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4341r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4341r4Nondeg.result) = fun w => -env "C" * (env "b" ^ 2)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi4341r4Nondeg, eval, recEnv, Interp.complex, ivm1C, iv2C]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4341r4Nondeg.body =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
            (env "A" + env "C" * Complex.tan (env "e" + env "f" * t) ^ 2) := by
      simp [rubi4341r4Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have e1 : (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ (m + 1) =
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m *
        (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    rw [e1, hAC]
    generalize (env "a" + env "b" * Complex.tan (env "e" + env "f" * t)) ^ m = Q
    field_simp
    ring

/-! ## RUBI 4.5.4.1 #7 and 4.5.1.2 #2 (over ℝ) -/

theorem rubi4541r7Nondeg_real : rubi4541r7Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4541r7Nondeg.conditions rubi4541r7Nondeg.body
    rubi4541r7Nondeg.result rubi4541r7Nondeg.integrals
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi4541r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4541r7Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4541r7Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "b" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0) := by
    intro w h
    simp [rubi4541r7Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
    simp only [ne_eq, mul_eq_zero, not_or, inv_eq_zero]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4541r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := (hD w hw).2
      have hs := (hD w hw).1
      simp only [ne_eq, mul_eq_zero, not_or, inv_eq_zero] at h
      simp [Defined, eval, Interp.real, em1, Fn.csc, hs]
      exact fun h' => (h (by omega)).1
    · filter_upwards [hF] with w hw
      have h := (hD w hw).2
      have hs := (hD w hw).1
      simp only [ne_eq, mul_eq_zero, not_or, inv_eq_zero] at h
      simp [Defined, eval, Interp.real, hkm, iv2R, Fn.csc, hs]
      exact fun h' => (h h').1
  · filter_upwards with w
    simp [rubi4541r7Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4541r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m +
        1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, em1, Fn.csc]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
        (env "A" + env "C" * ((Real.sin (env "e" + env "f" * t))⁻¹) ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, iv2R, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4541r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4541r7Nondeg.result) =
        fun w => env "B" * (env "b")⁻¹ * Φ "I1" w + Φ "I2" w := by
      funext w
      simp [rubi4541r7Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4541r7Nondeg.body =
        (env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
            (env "A" + env "B" * (Real.sin (env "e" + env "f" * t))⁻¹ + env "C" *
            ((Real.sin (env "e" + env "f" * t))⁻¹) ^ 2) := by
      simp [rubi4541r7Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add hΦ2').congr_deriv ?_
    have e1 : (env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1) =
        (env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
        (env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hs0 := (hD t hF.self_of_nhds).1
    rw [e1]
    generalize (env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m = Q
    generalize Real.sin (env "e" + env "f" * t) = S at hs0 ⊢
    field_simp
    ring

theorem rubi4512r2Nondeg_real : rubi4512r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4512r2Nondeg.conditions rubi4512r2Nondeg.body
    rubi4512r2Nondeg.result rubi4512r2Nondeg.integrals
  intro env hc t hF
  have hb : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi4512r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4512r2Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4512r2Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → env "d" * (Real.sin (env "e" + env "f" * w))⁻¹ ≠ 0) := by
    intro w h
    simp [rubi4512r2Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
    simp only [ne_eq, mul_eq_zero, not_or, inv_eq_zero]
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4512r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := (hD w hw).2
      have hs := (hD w hw).1
      simp only [ne_eq, mul_eq_zero, not_or, inv_eq_zero] at h
      simp [Defined, eval, Interp.real, em1, Fn.csc, hs]
      exact fun h' => (h (by omega)).1
    · filter_upwards [hF] with w hw
      have h := (hD w hw).2
      have hs := (hD w hw).1
      simp only [ne_eq, mul_eq_zero, not_or, inv_eq_zero] at h
      simp [Defined, eval, Interp.real, hkm, iv2R, Fn.csc, hs]
      exact fun h' => (h h').1
  · filter_upwards with w
    simp [rubi4512r2Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, hb]
  · simp only [rubi4512r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m +
        1)) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, em1, Fn.csc]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
        (env "a" ^ 2 + env "b" ^ 2 * ((Real.sin (env "e" + env "f" * t))⁻¹) ^ 2)) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, hkm, iv2R, Fn.csc]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4512r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4512r2Nondeg.result) =
        fun w => 2 * env "a" * env "b" * (env "d")⁻¹ * Φ "I1" w + Φ "I2" w := by
      funext w
      simp [rubi4512r2Nondeg, eval, recEnv, Interp.real, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4512r2Nondeg.body =
        (env "a" + env "b" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ 2 *
            (env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m := by
      simp [rubi4512r2Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add hΦ2').congr_deriv ?_
    have e1 : (env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ (m + 1) =
        (env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m *
        (env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) := by
      by_cases hm : m < 0
      · exact zpow_add_one₀ ((hD t hF.self_of_nhds).2 hm) m
      · lift m to ℕ using (by omega)
        rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast, pow_succ]
    have hs0 := (hD t hF.self_of_nhds).1
    rw [e1]
    generalize (env "d" * (Real.sin (env "e" + env "f" * t))⁻¹) ^ m = Q
    generalize Real.sin (env "e" + env "f" * t) = S at hs0 ⊢
    field_simp
    ring

end OSR.IntegrationRec248
