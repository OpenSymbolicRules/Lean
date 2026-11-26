import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic sine rules

Proofs over ℝ of RUBI 7.1 rules for `a + b arsinh(c x)`, whose argument is defined everywhere
so that only the integer powers constrain the domain:

* 7.1.6 #1 substitutes `u = c + d x` in `(a + b arsinh(c + d x))^n`;
* 7.1.1 #2 (`n < -1`), 7.1.2 #2 (factor `(d x)^m`) and 7.1.5 #2 (factor `(d + e x)^m`) integrate
  by parts with `arsinh'(c x) = c / sqrt(1 + c^2 x^2)`;
* 7.1.1 #3 and 7.1.2 #6 substitute `u = a + b arsinh(c x)`, using
  `cosh(arsinh y) = sqrt(1 + y^2)` and `sinh(arsinh y) = y`;
* 7.1.3 #7 and 7.1.4 #1 substitute `u = arsinh(c x)` when `e = c^2 d`, using
  `sech(arsinh y) = 1 / sqrt(1 + y^2)` and `tanh(arsinh y) = y / sqrt(1 + y^2)`.

The complex statements are vacuous (no complex interpretation of `transc1#arcsinh`) and stay
unproved. -/

namespace OSR.IntegrationRec239

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin (a b t : ℝ) : HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

/-- `arsinh (c x)` has derivative `c / sqrt(1 + c^2 x^2)`. -/
private theorem hasDerivAt_arsinh_mul (c t : ℝ) :
    HasDerivAt (fun w => Real.arsinh (c * w)) (c * (Real.sqrt (1 + c ^ 2 * t ^ 2))⁻¹) t := by
  have h := (Real.hasDerivAt_arsinh (c * t)).comp t ((hasDerivAt_id' t).const_mul c)
  refine h.congr_deriv ?_
  rw [mul_pow]; ring

/-! ## RUBI 7.1.6 #1 -/

theorem rubi716r1Nondeg_real : rubi716r1Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi716r1Nondeg.conditions
    rubi716r1Nondeg.body rubi716r1Nondeg.result rubi716r1Nondeg.integrals
    rubi716r1Nondeg.substs
  intro env hc t hF
  have hne : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi716r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkp : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi716r1Nondeg, Defined, eval, Interp.real, hkp] at h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi716r1Nondeg.body →
      (k < 0 → env "a" + env "b" * Real.arsinh (env "c" + env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi716r1Nondeg, Defined, eval, Interp.real, hkp] at h
    exact h
  have h0 := hD t hF.self_of_nhds
  have hcA : ContinuousAt (fun u : ℝ => env "a" + env "b" * Real.arsinh u)
      (env "c" + env "d" * t) :=
    continuousAt_const.add (continuousAt_const.mul Real.continuous_arsinh.continuousAt)
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t),
      k < 0 → env "a" + env "b" * Real.arsinh u ≠ 0 := by
    by_cases hk : k < 0
    · filter_upwards [hcA.tendsto.eventually (eventually_ne_nhds (h0 hk))] with u hu
      exact fun _ => hu
    · exact Filter.Eventually.of_forall fun _ h => absurd h hk
  have hsub : substAt Interp.real env rubi716r1Nondeg.substs "x" "I1" t =
      env "c" + env "d" * t := by
    simp [rubi716r1Nondeg, substAt, eval]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi716r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi716r1Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simpa [Defined, eval, Interp.real, hkp] using hu
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi716r1Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hne]
    · simp only [rubi716r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.arsinh (env "c" + env "d" * t)) ^ k)
          (env "c" + env "d" * t) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkp]
      have h := (hΦ'.comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "d")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi716r1Nondeg.integrals.map (·.1))
            rubi716r1Nondeg.substs Φ "x" w) rubi716r1Nondeg.result) =
          fun w => (env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w) := by
        funext w
        simp [rubi716r1Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi716r1Nondeg, eval, Interp.real, hkp]
      field_simp

/-! ## RUBI 7.1.1 #2 -/

theorem rubi711r2Nondeg_real : rubi711r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi711r2Nondeg.conditions rubi711r2Nondeg.body
    rubi711r2Nondeg.result rubi711r2Nondeg.integrals
  intro env hc t hF
  have hnlt : env "n" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi711r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW : env "b" * env "c" * (env "n" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n")
      (.int 1))) (.int 0)) (by simp [rubi711r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨hb, hcz⟩, hn1⟩ := hW'
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi711r2Nondeg, Defined, eval, Interp.real, hkn] at h
  have hn : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hkn
  have hk : k < -1 := by
    have : (k : ℝ) < -1 := hn ▸ hnlt
    exact_mod_cast this
  have hk0 : k < 0 := by omega
  have hk1 : k + 1 < 0 := by omega
  have en1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi711r2Nondeg.body →
      env "a" + env "b" * Real.arsinh (env "c" * w) ≠ 0 := by
    intro w h
    simp [rubi711r2Nondeg, Defined, eval, Interp.real, hkn, hk0] at h
    exact h
  have hA0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi711r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hAw := hD w hw
    have hS : 0 < 1 + env "c" ^ 2 * w ^ 2 := by positivity
    simp [Defined, eval, Interp.real, en1, ivm1R, iv2R, hAw, hS.le, hS.ne']
  · filter_upwards [hF] with w hw
    have hAw := hD w hw
    have hS : 0 < 1 + env "c" ^ 2 * w ^ 2 := by positivity
    simp [rubi711r2Nondeg, Defined, eval, recEnv, Interp.real, en1, ivm1R, iv2R, hb, hcz, hn1,
      hAw, hS.le]
  · simp only [rubi711r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t * (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ (k + 1) *
        (Real.sqrt (1 + env "c" ^ 2 * t ^ 2))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, en1, ivm1R, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi711r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi711r2Nondeg.result) =
        fun w => Real.sqrt (1 + env "c" ^ 2 * w ^ 2) *
            (env "a" + env "b" * Real.arsinh (env "c" * w)) ^ (k + 1) *
            (env "b" * env "c" * (env "n" + 1))⁻¹ +
          -env "c" * (env "b" * (env "n" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi711r2Nondeg, eval, recEnv, Interp.real, en1, ivm1R, iv2R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi711r2Nondeg.body =
        (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k := by
      simp [rubi711r2Nondeg, eval, Interp.real, hkn]
    rw [hfun, hEF]
    have hQ : 0 < 1 + env "c" ^ 2 * t ^ 2 := by positivity
    have hq : HasDerivAt (fun w => 1 + env "c" ^ 2 * w ^ 2) (env "c" ^ 2 * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (env "c" ^ 2)).const_add 1
      simpa using this
    have hS := (Real.hasDerivAt_sqrt hQ.ne').comp t hq
    have hA := ((hasDerivAt_arsinh_mul (env "c") t).const_mul (env "b")).const_add (env "a")
    have hP := (hasDerivAt_zpow (k + 1) _ (Or.inl hA0)).comp t hA
    refine (((hS.mul hP).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show k + 1 - 1 = k by ring]
    have hkr : ((k + 1 : ℤ) : ℝ) = env "n" + 1 := by rw [hn]; push_cast; ring
    rw [hkr]
    have hS0 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
    have hS2 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ^ 2 = 1 + env "c" ^ 2 * t ^ 2 :=
      Real.sq_sqrt hQ.le
    have eP : (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ (k + 1) =
        (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k *
          (env "a" + env "b" * Real.arsinh (env "c" * t)) := zpow_add_one₀ hA0 k
    rw [eP]
    generalize (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k = R
    generalize env "a" + env "b" * Real.arsinh (env "c" * t) = A
    generalize Real.sqrt (1 + env "c" ^ 2 * t ^ 2) = S at hS0 hS2 ⊢
    field_simp
    ring

/-! ## RUBI 7.1.1 #3 -/

theorem rubi711r3Nondeg_real : rubi711r3Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi711r3Nondeg.conditions
    rubi711r3Nondeg.body rubi711r3Nondeg.result rubi711r3Nondeg.integrals
    rubi711r3Nondeg.substs
  intro env hc t hF
  have hW : env "b" * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "c")) (.int 0)) (by simp [rubi711r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hb, hcz⟩ := hW'
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi711r3Nondeg, Defined, eval, Interp.real, hkn] at h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi711r3Nondeg.body →
      (k < 0 → env "a" + env "b" * Real.arsinh (env "c" * w) ≠ 0) := by
    intro w h
    simp [rubi711r3Nondeg, Defined, eval, Interp.real, hkn] at h
    exact h
  have h0 := hD t hF.self_of_nhds
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "a" + env "b" * Real.arsinh (env "c" * t)),
      k < 0 → u ≠ 0 := by
    by_cases hk : k < 0
    · filter_upwards [eventually_ne_nhds (h0 hk)] with u hu
      exact fun _ => hu
    · exact Filter.Eventually.of_forall fun _ h => absurd h hk
  have hsub : substAt Interp.real env rubi711r3Nondeg.substs "x" "I1" t =
      env "a" + env "b" * Real.arsinh (env "c" * t) := by
    simp [rubi711r3Nondeg, substAt, eval, Interp.real]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi711r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi711r3Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.real]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simpa [Defined, eval, Interp.real, hkn, ivm1R, hb] using hu
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi711r3Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hb, hcz]
    · simp only [rubi711r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have harg : -(env "a" * (env "b")⁻¹) +
          (env "a" + env "b" * Real.arsinh (env "c" * t)) * (env "b")⁻¹ =
          Real.arsinh (env "c" * t) := by field_simp; ring
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k *
            Real.sqrt (1 + env "c" ^ 2 * t ^ 2))
          (env "a" + env "b" * Real.arsinh (env "c" * t)) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkn, ivm1R, harg, mul_pow,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      have hA := ((hasDerivAt_arsinh_mul (env "c") t).const_mul (env "b")).const_add (env "a")
      have h := (hΦ'.comp t hA).const_mul (env "b" * env "c")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi711r3Nondeg.integrals.map (·.1))
            rubi711r3Nondeg.substs Φ "x" w) rubi711r3Nondeg.result) =
          fun w => (env "b" * env "c")⁻¹ *
            Φ "I1" (env "a" + env "b" * Real.arsinh (env "c" * w)) := by
        funext w
        simp [rubi711r3Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      have hEF : eval Interp.real (Function.update env "x" t) rubi711r3Nondeg.body =
          (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k := by
        simp [rubi711r3Nondeg, eval, Interp.real, hkn]
      rw [hEF]
      have hS0 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ≠ 0 :=
        (Real.sqrt_pos.mpr (by positivity)).ne'
      field_simp

/-! ## RUBI 7.1.3 #7 -/

theorem rubi713r7Nondeg_real : rubi713r7Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi713r7Nondeg.conditions
    rubi713r7Nondeg.body rubi713r7Nondeg.result rubi713r7Nondeg.integrals
    rubi713r7Nondeg.substs
  intro env hc t hF
  have hrel : env "e" = env "c" ^ 2 * env "d" := by
    have h := hc (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")))
      (by simp [rubi713r7Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpos : 0 < env "n" := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi713r7Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW : env "c" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "c") (.var "d")) (.int 0)) (by simp [rubi713r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi713r7Nondeg, Defined, eval, Interp.real, hkn] at h
  have hn : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hkn
  have hk : 0 < k := by rw [hn] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi713r7Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi713r7Nondeg, Defined, eval, Interp.real, hkn, hk0, ivm1R, iv2R] at h
    exact h
  have hD0 := hD t hF.self_of_nhds
  have hsub : substAt Interp.real env rubi713r7Nondeg.substs "x" "I1" t =
      Real.arsinh (env "c" * t) := by
    simp [rubi713r7Nondeg, substAt, eval, Interp.real]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi713r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi713r7Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.real]
    · filter_upwards with u
      simp [Defined, eval, Interp.real, hkn, hk0]
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi713r7Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hW]
    · simp only [rubi713r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k *
            Fn.sech (Real.arsinh (env "c" * t))) (Real.arsinh (env "c" * t)) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkn,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      have h := (hΦ'.comp t (hasDerivAt_arsinh_mul (env "c") t)).const_mul (env "c" * env "d")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi713r7Nondeg.integrals.map (·.1))
            rubi713r7Nondeg.substs Φ "x" w) rubi713r7Nondeg.result) =
          fun w => (env "c" * env "d")⁻¹ * Φ "I1" (Real.arsinh (env "c" * w)) := by
        funext w
        simp [rubi713r7Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      have hEF : eval Interp.real (Function.update env "x" t) rubi713r7Nondeg.body =
          (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k * (env "d" + env "e" * t ^ 2)⁻¹ := by
        simp [rubi713r7Nondeg, eval, Interp.real, hkn, ivm1R, iv2R]
      rw [hEF]
      have hQ : 0 < 1 + env "c" ^ 2 * t ^ 2 := by positivity
      have hS0 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
      have hS2 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ^ 2 = 1 + env "c" ^ 2 * t ^ 2 :=
        Real.sq_sqrt hQ.le
      have hcz : env "c" ≠ 0 := left_ne_zero_of_mul hW
      have hd : env "d" ≠ 0 := right_ne_zero_of_mul hW
      rw [Fn.sech, Real.cosh_arsinh, mul_pow, hrel]
      have hD1 : env "d" + env "c" ^ 2 * env "d" * t ^ 2 ≠ 0 := by rwa [hrel] at hD0
      generalize (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k = R
      generalize Real.sqrt (1 + env "c" ^ 2 * t ^ 2) = S at hS0 hS2 ⊢
      field_simp
      rw [hS2]

/-! ## RUBI 7.1.4 #1 -/

theorem rubi714r1Nondeg_real : rubi714r1Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi714r1Nondeg.conditions
    rubi714r1Nondeg.body rubi714r1Nondeg.result rubi714r1Nondeg.integrals
    rubi714r1Nondeg.substs
  intro env hc t hF
  have hrel : env "e" = env "c" ^ 2 * env "d" := by
    have h := hc (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")))
      (by simp [rubi714r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpos : 0 < env "n" := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi714r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi714r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi714r1Nondeg, Defined, eval, Interp.real, hkn] at h
  have hn : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hkn
  have hk : 0 < k := by rw [hn] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi714r1Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi714r1Nondeg, Defined, eval, Interp.real, hkn, hk0, ivm1R, iv2R] at h
    exact h
  have hD0 := hD t hF.self_of_nhds
  have hsub : substAt Interp.real env rubi714r1Nondeg.substs "x" "I1" t =
      Real.arsinh (env "c" * t) := by
    simp [rubi714r1Nondeg, substAt, eval, Interp.real]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi714r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi714r1Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.real]
    · filter_upwards with u
      simp [Defined, eval, Interp.real, hkn, hk0]
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi714r1Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hW]
    · simp only [rubi714r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k *
            Real.tanh (Real.arsinh (env "c" * t))) (Real.arsinh (env "c" * t)) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkn,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      have h := (hΦ'.comp t (hasDerivAt_arsinh_mul (env "c") t)).const_mul (env "e")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi714r1Nondeg.integrals.map (·.1))
            rubi714r1Nondeg.substs Φ "x" w) rubi714r1Nondeg.result) =
          fun w => (env "e")⁻¹ * Φ "I1" (Real.arsinh (env "c" * w)) := by
        funext w
        simp [rubi714r1Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      have hEF : eval Interp.real (Function.update env "x" t) rubi714r1Nondeg.body =
          t * (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k *
            (env "d" + env "e" * t ^ 2)⁻¹ := by
        simp [rubi714r1Nondeg, eval, Interp.real, hkn, ivm1R, iv2R]
      rw [hEF]
      have hQ : 0 < 1 + env "c" ^ 2 * t ^ 2 := by positivity
      have hS0 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
      have hS2 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ^ 2 = 1 + env "c" ^ 2 * t ^ 2 :=
        Real.sq_sqrt hQ.le
      have hcz : env "c" ≠ 0 := by
        intro h; apply hW; rw [hrel, h]; ring
      have hd : env "d" ≠ 0 := by
        intro h; apply hW; rw [hrel, h]; ring
      rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_arsinh, Real.cosh_arsinh, mul_pow, hrel]
      have hD1 : env "d" + env "c" ^ 2 * env "d" * t ^ 2 ≠ 0 := by rwa [hrel] at hD0
      generalize (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k = R
      generalize Real.sqrt (1 + env "c" ^ 2 * t ^ 2) = S at hS0 hS2 ⊢
      field_simp
      rw [hS2]

/-! ## RUBI 7.1.2 #6 -/

theorem rubi712r6Nondeg_real : rubi712r6Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi712r6Nondeg.conditions
    rubi712r6Nondeg.body rubi712r6Nondeg.result rubi712r6Nondeg.integrals
    rubi712r6Nondeg.substs
  intro env hc t hF
  have hmpos : 0 < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi712r6Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi712r6Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi712r6Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hj : 0 < j := by rw [hm] at hmpos; exact_mod_cast hmpos
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j + 1 < 0 := by omega
  have em1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hW : env "b" * env "c" ^ (j + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.pow (.var "c") (.app2 .add (.var "m") (.int 1))))
      (.int 0)) (by simp [rubi712r6Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, em1, hj1] using h
  have hb : env "b" ≠ 0 := left_ne_zero_of_mul hW
  have hcz : env "c" ≠ 0 := by
    intro h; apply hW; rw [h, zero_zpow _ (by omega), mul_zero]
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi712r6Nondeg.body →
      (k < 0 → env "a" + env "b" * Real.arsinh (env "c" * w) ≠ 0) := by
    intro w h
    simp [rubi712r6Nondeg, Defined, eval, Interp.real, hkm, hkn, hj0] at h
    exact h
  have h0 := hD t hF.self_of_nhds
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "a" + env "b" * Real.arsinh (env "c" * t)),
      k < 0 → u ≠ 0 := by
    by_cases hk : k < 0
    · filter_upwards [eventually_ne_nhds (h0 hk)] with u hu
      exact fun _ => hu
    · exact Filter.Eventually.of_forall fun _ h => absurd h hk
  have hsub : substAt Interp.real env rubi712r6Nondeg.substs "x" "I1" t =
      env "a" + env "b" * Real.arsinh (env "c" * t) := by
    simp [rubi712r6Nondeg, substAt, eval, Interp.real]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi712r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi712r6Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.real]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simpa [Defined, eval, Interp.real, hkn, hkm, hj0, ivm1R, hb] using hu
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi712r6Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, em1, hj1, hW]
    · simp only [rubi712r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have harg : -(env "a" * (env "b")⁻¹) +
          (env "a" + env "b" * Real.arsinh (env "c" * t)) * (env "b")⁻¹ =
          Real.arsinh (env "c" * t) := by field_simp; ring
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k * (env "c" * t) ^ j *
            Real.sqrt (1 + env "c" ^ 2 * t ^ 2))
          (env "a" + env "b" * Real.arsinh (env "c" * t)) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkn, hkm, ivm1R, harg, mul_pow,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      have hA := ((hasDerivAt_arsinh_mul (env "c") t).const_mul (env "b")).const_add (env "a")
      have h := (hΦ'.comp t hA).const_mul (env "b" * env "c" ^ (j + 1))⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi712r6Nondeg.integrals.map (·.1))
            rubi712r6Nondeg.substs Φ "x" w) rubi712r6Nondeg.result) =
          fun w => (env "b" * env "c" ^ (j + 1))⁻¹ *
            Φ "I1" (env "a" + env "b" * Real.arsinh (env "c" * w)) := by
        funext w
        simp [rubi712r6Nondeg, substEnv, substAt, eval, Interp.real, ivm1R, em1]
      rw [hfun]
      apply h.congr_deriv
      have hEF : eval Interp.real (Function.update env "x" t) rubi712r6Nondeg.body =
          t ^ j * (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k := by
        simp [rubi712r6Nondeg, eval, Interp.real, hkn, hkm]
      rw [hEF, mul_zpow, zpow_add_one₀ hcz]
      have hS0 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ≠ 0 :=
        (Real.sqrt_pos.mpr (by positivity)).ne'
      have hcj : env "c" ^ j ≠ 0 := zpow_ne_zero j hcz
      generalize (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k = R
      generalize env "c" ^ j = C at hcj ⊢
      field_simp

/-! ## RUBI 7.1.2 #2 -/

theorem rubi712r2Nondeg_real : rubi712r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi712r2Nondeg.conditions rubi712r2Nondeg.body
    rubi712r2Nondeg.result rubi712r2Nondeg.integrals
  intro env hc t hF
  have hW : env "d" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi712r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "n" := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi712r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hd, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi712r2Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi712r2Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  have em1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have ep1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hj1' : j + 1 < 0 → j < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi712r2Nondeg.body →
      (j < 0 → env "d" * w ≠ 0) := by
    intro w h
    simp [rubi712r2Nondeg, Defined, eval, Interp.real, hkm, hkp, hk0] at h
    simp only [ne_eq, mul_eq_zero, not_or]; tauto
  have hd0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi712r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hdw := hD w hw
    have hdw' : j + 1 < 0 → env "d" * w ≠ 0 := fun h => hdw (hj1' h)
    have hS : 0 < 1 + env "c" ^ 2 * w ^ 2 := by positivity
    simp only [ne_eq, mul_eq_zero, not_or] at hdw'
    simp [Defined, eval, Interp.real, em1, ep1, ivm1R, iv2R, hk1, hS.le, hS.ne']
    tauto
  · filter_upwards [hF] with w hw
    have hdw := hD w hw
    have hdw' : j + 1 < 0 → env "d" * w ≠ 0 := fun h => hdw (hj1' h)
    simp only [ne_eq, mul_eq_zero, not_or] at hdw'
    simp [rubi712r2Nondeg, Defined, eval, recEnv, Interp.real, em1, hkp, ivm1R, hd, hm1, hk0]
    tauto
  · simp only [rubi712r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * t) ^ (j + 1) *
        (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ (k - 1) *
        (Real.sqrt (1 + env "c" ^ 2 * t ^ 2))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, ep1, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi712r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi712r2Nondeg.result) =
        fun w => (env "d" * w) ^ (j + 1) *
            (env "a" + env "b" * Real.arsinh (env "c" * w)) ^ k * (env "d" * (env "m" + 1))⁻¹ +
          -env "b" * env "c" * env "n" * (env "d" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi712r2Nondeg, eval, recEnv, Interp.real, em1, hkp, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi712r2Nondeg.body =
        (env "d" * t) ^ j * (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k := by
      simp [rubi712r2Nondeg, eval, Interp.real, hkm, hkp]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_arsinh_mul (env "c") t).const_mul (env "b")).const_add (env "a")
    have hor : env "d" * t ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases hj : j < 0
      · exact Or.inl (hd0 hj)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (j + 1) _ hor).comp t ((hasDerivAt_id' t).const_mul (env "d"))
    have hQ := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t hA
    refine (((hP.mul hQ).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    have hkr : ((k : ℤ) : ℝ) = env "n" := hp.symm
    rw [hjr, hkr]
    have hS0 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity)).ne'
    generalize (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ (k - 1) = R
    generalize (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k = R1
    generalize (env "d" * t) ^ j = P
    generalize (env "d" * t) ^ (j + 1) = P1
    field_simp
    ring

/-! ## RUBI 7.1.5 #2 -/

theorem rubi715r2Nondeg_real : rubi715r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi715r2Nondeg.conditions rubi715r2Nondeg.body
    rubi715r2Nondeg.result rubi715r2Nondeg.integrals
  intro env hc t hF
  have hW : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi715r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "n" := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi715r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨he, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi715r2Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi715r2Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  have em1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have ep1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hj1' : j + 1 < 0 → j < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi715r2Nondeg.body →
      (j < 0 → env "d" + env "e" * w ≠ 0) := by
    intro w h
    simp [rubi715r2Nondeg, Defined, eval, Interp.real, hkm, hkp, hk0] at h
    tauto
  have hd0 := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi715r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hdw := hD w hw
    have hdw' : j + 1 < 0 → env "d" + env "e" * w ≠ 0 := fun h => hdw (hj1' h)
    have hS : 0 < 1 + env "c" ^ 2 * w ^ 2 := by positivity
    simp [Defined, eval, Interp.real, em1, ep1, ivm1R, iv2R, hk1, hS.le, hS.ne']
    tauto
  · filter_upwards [hF] with w hw
    have hdw := hD w hw
    have hdw' : j + 1 < 0 → env "d" + env "e" * w ≠ 0 := fun h => hdw (hj1' h)
    simp [rubi715r2Nondeg, Defined, eval, recEnv, Interp.real, em1, hkp, ivm1R, he, hm1, hk0]
    tauto
  · simp only [rubi715r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (j + 1) *
        (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ (k - 1) *
        (Real.sqrt (1 + env "c" ^ 2 * t ^ 2))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, ep1, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi715r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi715r2Nondeg.result) =
        fun w => (env "d" + env "e" * w) ^ (j + 1) *
            (env "a" + env "b" * Real.arsinh (env "c" * w)) ^ k * (env "e" * (env "m" + 1))⁻¹ +
          -env "b" * env "c" * env "n" * (env "e" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi715r2Nondeg, eval, recEnv, Interp.real, em1, hkp, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi715r2Nondeg.body =
        (env "d" + env "e" * t) ^ j * (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k := by
      simp [rubi715r2Nondeg, eval, Interp.real, hkm, hkp]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_arsinh_mul (env "c") t).const_mul (env "b")).const_add (env "a")
    have hor : env "d" + env "e" * t ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases hj : j < 0
      · exact Or.inl (hd0 hj)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (j + 1) _ hor).comp t (hasDerivAt_lin (env "d") (env "e") t)
    have hQ := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t hA
    refine (((hP.mul hQ).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show j + 1 - 1 = j by ring]
    have hjr : ((j + 1 : ℤ) : ℝ) = env "m" + 1 := by rw [hm]; push_cast; ring
    have hkr : ((k : ℤ) : ℝ) = env "n" := hp.symm
    rw [hjr, hkr]
    have hS0 : Real.sqrt (1 + env "c" ^ 2 * t ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity)).ne'
    generalize (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ (k - 1) = R
    generalize (env "a" + env "b" * Real.arsinh (env "c" * t)) ^ k = R1
    generalize (env "d" + env "e" * t) ^ j = P
    generalize (env "d" + env "e" * t) ^ (j + 1) = P1
    field_simp
    ring

end OSR.IntegrationRec239
