import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic cosine rules (continued)

Proofs over ℝ of RUBI 7.2.6 #2, which substitutes `u = c + d x` in
`(e + f x)^m (a + b arcosh(c + d x))^n`, and of the closed forms 7.2.3 #4 (over
`sqrt(d + e x^2)` with `c^2 d + e = 0`, which forces `d < 0`) and 7.2.3 #5 (over
`sqrt(d1 + e1 x) sqrt(d2 + e2 x)` with `e1 = c d1` and `e2 = -c d2`, which force `d1 > 0` and
`d2 < 0`): there the ratios of square roots in the result are constant where `1 < c x`. The real
`arcosh` is only defined on `[1, ∞)`, so an integrand defined near `x` forces its argument
above `1`. The
complex statements are vacuous (no complex interpretation of `transc1#arccosh`) and stay
unproved. -/

namespace OSR.IntegrationRec243

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem hasDerivAt_lin (a b t : ℝ) : HasDerivAt (fun w => a + b * w) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

/-- A bound `1 ≤ c + d w` holding near `t` holds strictly at `t` when `d ≠ 0`. -/
private theorem one_lt_of_eventually_lin {c d t : ℝ} (hd : d ≠ 0)
    (h : ∀ᶠ w in 𝓝 t, 1 ≤ c + d * w) : 1 < c + d * t := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have h1 := hball (y := t + ε / 2) (by
      rw [Real.dist_eq, show t + ε / 2 - t = ε / 2 by ring, abs_of_pos (by linarith)]; linarith)
    nlinarith
  · have h1 := hball (y := t - ε / 2) (by
      rw [Real.dist_eq, show t - ε / 2 - t = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]
      linarith)
    nlinarith

/-- A bound `1 ≤ c w` holding near `t` holds strictly at `t`. -/
private theorem one_lt_of_eventually_mul {c t : ℝ} (h : ∀ᶠ w in 𝓝 t, 1 ≤ c * w) :
    1 < c * t := by
  have hc : c ≠ 0 := by
    intro h0
    have := h.self_of_nhds
    rw [h0, zero_mul] at this
    linarith
  have := one_lt_of_eventually_lin (c := 0) (d := c) hc (by simpa using h)
  simpa using this

/-- `arcosh (c x)` has derivative `c / (sqrt(1 + c x) sqrt(-1 + c x))` where `1 < c x`. -/
private theorem hasDerivAt_arcosh_mul {c t : ℝ} (h : 1 < c * t) :
    HasDerivAt (fun w => Real.arcosh (c * w))
      (c * (Real.sqrt (1 + c * t) * Real.sqrt (-1 + c * t))⁻¹) t := by
  have hA := (Real.hasDerivAt_arcosh (x := c * t) h).comp t ((hasDerivAt_id' t).const_mul c)
  refine hA.congr_deriv ?_
  rw [show (c * t) ^ 2 - 1 = (1 + c * t) * (-1 + c * t) by ring,
    Real.sqrt_mul (by linarith)]
  ring

/-! ## RUBI 7.2.6 #2 -/

theorem rubi726r2Nondeg_real : rubi726r2Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi726r2Nondeg.conditions
    rubi726r2Nondeg.body rubi726r2Nondeg.result rubi726r2Nondeg.integrals
    rubi726r2Nondeg.substs
  intro env hc t hF
  have hne : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi726r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi726r2Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi726r2Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hlin : ∀ w, (env "d" * env "e" + -(env "c" * env "f")) * (env "d")⁻¹ +
      env "f" * (env "c" + env "d" * w) * (env "d")⁻¹ = env "e" + env "f" * w := by
    intro w
    field_simp
    ring
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi726r2Nondeg.body →
      (m < 0 → env "e" + env "f" * w ≠ 0) ∧
        (k < 0 → env "a" + env "b" * Real.arcosh (env "c" + env "d" * w) ≠ 0) ∧
        1 ≤ env "c" + env "d" * w := by
    intro w h
    simp [rubi726r2Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
    tauto
  obtain ⟨hm0, hA0, -⟩ := hD t hF.self_of_nhds
  have hu0 := one_lt_of_eventually_lin hne (hF.mono fun w hw => (hD w hw).2.2)
  have hcA : ContinuousAt (fun u : ℝ => env "a" + env "b" * Real.arcosh u)
      (env "c" + env "d" * t) :=
    continuousAt_const.add (continuousAt_const.mul (Real.hasDerivAt_arcosh hu0).continuousAt)
  have hnA : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t),
      k < 0 → env "a" + env "b" * Real.arcosh u ≠ 0 := by
    by_cases hk : k < 0
    · filter_upwards [hcA.tendsto.eventually (eventually_ne_nhds (hA0 hk))] with u hu
      exact fun _ => hu
    · exact Filter.Eventually.of_forall fun _ h => absurd h hk
  have hcf : ContinuousAt (fun u : ℝ => (env "d" * env "e" + -(env "c" * env "f")) *
      (env "d")⁻¹ + env "f" * u * (env "d")⁻¹) (env "c" + env "d" * t) := by
    fun_prop
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t),
      (m < 0 → (env "d" * env "e" + -(env "c" * env "f")) * (env "d")⁻¹ +
        env "f" * u * (env "d")⁻¹ ≠ 0) ∧ (k < 0 → env "a" + env "b" * Real.arcosh u ≠ 0) ∧
        1 ≤ u := by
    by_cases hmn : m < 0
    · have hv : (env "d" * env "e" + -(env "c" * env "f")) * (env "d")⁻¹ +
          env "f" * (env "c" + env "d" * t) * (env "d")⁻¹ ≠ 0 := by
        rw [hlin]; exact hm0 hmn
      filter_upwards [hcf.tendsto.eventually (eventually_ne_nhds hv), hnA,
        Ioi_mem_nhds hu0] with u h0 hu hu1
      exact ⟨fun _ => h0, hu, le_of_lt hu1⟩
    · filter_upwards [hnA, Ioi_mem_nhds hu0] with u hu hu1
      exact ⟨fun h => absurd h hmn, hu, le_of_lt hu1⟩
  have hsub : substAt Interp.real env rubi726r2Nondeg.substs "x" "I1" t =
      env "c" + env "d" * t := by
    simp [rubi726r2Nondeg, substAt, eval]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi726r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi726r2Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simp [Defined, eval, Interp.real, hkm, hkp, ivm1R, hu.2.2]
      tauto
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi726r2Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hne]
    · simp only [rubi726r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "e" + env "f" * t) ^ m *
            (env "a" + env "b" * Real.arcosh (env "c" + env "d" * t)) ^ k)
          (env "c" + env "d" * t) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkm, hkp, ivm1R, hlin]
      have h := (hΦ'.comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "d")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi726r2Nondeg.integrals.map (·.1))
            rubi726r2Nondeg.substs Φ "x" w) rubi726r2Nondeg.result) =
          fun w => (env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w) := by
        funext w
        simp [rubi726r2Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi726r2Nondeg, eval, Interp.real, hkm, hkp]
      field_simp

/-! ## RUBI 7.2.3 #4 -/

theorem rubi723r4Nondeg_real : rubi723r4Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi723r4Nondeg.conditions rubi723r4Nondeg.body
    rubi723r4Nondeg.result
  intro env hc t hF
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi723r4Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  have hW : env "b" * env "c" * (env "n" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n")
      (.int 1))) (.int 0)) (by simp [rubi723r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨hb, hcz⟩, hn1⟩ := hW'
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi723r4Nondeg, Defined, eval, Interp.real, hkn] at h
  have hn : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hkn
  have en1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hk1' : k + 1 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi723r4Nondeg.body →
      (k < 0 → env "a" + env "b" * Real.arcosh (env "c" * w) ≠ 0) ∧ 1 ≤ env "c" * w ∧
        0 < env "d" + env "e" * w ^ 2 := by
    intro w h
    simp [rubi723r4Nondeg, Defined, eval, Interp.real, hkn, ivm1R, iv2R] at h
    refine ⟨h.1.2, h.1.1, ?_⟩
    have hs : Real.sqrt (env "d" + env "e" * w ^ 2) ≠ 0 := by tauto
    exact Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs))
  obtain ⟨hA0, -, hT0⟩ := hD t hF.self_of_nhds
  have hct := one_lt_of_eventually_mul (hF.mono fun w hw => (hD w hw).2.1)
  have hnear1 : ∀ᶠ w in 𝓝 t, 1 < env "c" * w :=
    ((continuous_const.mul continuous_id).continuousAt (x := t)).eventually (Ioi_mem_nhds hct)
  have hfac : ∀ w, env "d" + env "e" * w ^ 2 =
      -env "d" * ((1 + env "c" * w) * (-1 + env "c" * w)) := by
    intro w; rw [he']; ring
  have hdneg : 0 < -env "d" := by
    have hp : 0 < (1 + env "c" * t) * (-1 + env "c" * t) := by
      apply mul_pos <;> linarith
    rw [hfac] at hT0
    exact pos_of_mul_pos_left hT0 hp.le
  have hsd : Real.sqrt (-env "d") ≠ 0 := (Real.sqrt_pos.mpr hdneg).ne'
  have hsq : ∀ w, 1 < env "c" * w → Real.sqrt (env "d" + env "e" * w ^ 2) =
      Real.sqrt (-env "d") * (Real.sqrt (1 + env "c" * w) * Real.sqrt (-1 + env "c" * w)) := by
    intro w hw
    rw [hfac, Real.sqrt_mul hdneg.le, Real.sqrt_mul (by linarith)]
  refine ⟨?_, ?_⟩
  · filter_upwards [hF, hnear1] with w hw hw1
    obtain ⟨hAw, -, hTw⟩ := hD w hw
    have hS1 : 0 < 1 + env "c" * w := by linarith
    have hS2 : 0 < -1 + env "c" * w := by linarith
    simp [rubi723r4Nondeg, Defined, eval, Interp.real, en1, ivm1R, iv2R, hb, hcz, hn1, hS1.le,
      hS2.le, hTw.le, hTw.ne', hw1.le]
    exact fun h => hAw (hk1' h)
  · have hev : (fun w => eval Interp.real (Function.update env "x" w) rubi723r4Nondeg.result)
        =ᶠ[𝓝 t]
        fun w => (env "b" * env "c" * (env "n" + 1))⁻¹ * (Real.sqrt (-env "d"))⁻¹ *
          (env "a" + env "b" * Real.arcosh (env "c" * w)) ^ (k + 1) := by
      filter_upwards [hnear1] with w hw1
      have n1 : Real.sqrt (1 + env "c" * w) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      have n2 : Real.sqrt (-1 + env "c" * w) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      simp [rubi723r4Nondeg, eval, Interp.real, en1, ivm1R, iv2R, hsq w hw1,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      field_simp
    have hA := ((hasDerivAt_arcosh_mul hct).const_mul (env "b")).const_add (env "a")
    have hor : env "a" + env "b" * Real.arcosh (env "c" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases hk : k < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (k + 1) _ hor).comp t hA
    refine ((hP.const_mul _).congr_of_eventuallyEq hev).congr_deriv ?_
    have hEF : eval Interp.real (Function.update env "x" t) rubi723r4Nondeg.body =
        (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k *
          (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
      simp [rubi723r4Nondeg, eval, Interp.real, hkn, ivm1R, iv2R]
    rw [hEF, hsq t hct, show k + 1 - 1 = k by ring]
    have hkr : ((k + 1 : ℤ) : ℝ) = env "n" + 1 := by rw [hn]; push_cast; ring
    rw [hkr]
    have n1 : Real.sqrt (1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    have n2 : Real.sqrt (-1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    generalize (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k = R
    field_simp

/-! ## RUBI 7.2.3 #5 -/

theorem rubi723r5Nondeg_real : rubi723r5Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi723r5Nondeg.conditions rubi723r5Nondeg.body
    rubi723r5Nondeg.result
  intro env hc t hF
  have he1 : env "e1" = env "c" * env "d1" := by
    have h := hc (.eq (.var "e1") (.app2 .mul (.var "c") (.var "d1"))) (by simp [rubi723r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he2 : env "e2" = -env "c" * env "d2" := by
    have h := hc (.eq (.var "e2") (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d2")))
      (by simp [rubi723r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW : env "b" * env "c" * (env "n" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n")
      (.int 1))) (.int 0)) (by simp [rubi723r5Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨hb, hcz⟩, hn1⟩ := hW'
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi723r5Nondeg, Defined, eval, Interp.real, hkn] at h
  have hn : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hkn
  have en1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hk1' : k + 1 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi723r5Nondeg.body →
      (k < 0 → env "a" + env "b" * Real.arcosh (env "c" * w) ≠ 0) ∧ 1 ≤ env "c" * w ∧
        0 < env "d1" + env "e1" * w ∧ 0 < env "d2" + env "e2" * w := by
    intro w h
    simp [rubi723r5Nondeg, Defined, eval, Interp.real, hkn, ivm1R, iv2R] at h
    have hs1 : Real.sqrt (env "d1" + env "e1" * w) ≠ 0 := by tauto
    have hs2 : Real.sqrt (env "d2" + env "e2" * w) ≠ 0 := by tauto
    refine ⟨by tauto, by tauto, ?_, ?_⟩
    · exact Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs1))
    · exact Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs2))
  obtain ⟨hA0, -, hT1, hT2⟩ := hD t hF.self_of_nhds
  have hct := one_lt_of_eventually_mul (hF.mono fun w hw => (hD w hw).2.1)
  have hnear1 : ∀ᶠ w in 𝓝 t, 1 < env "c" * w :=
    ((continuous_const.mul continuous_id).continuousAt (x := t)).eventually (Ioi_mem_nhds hct)
  have hf1 : ∀ w, env "d1" + env "e1" * w = env "d1" * (1 + env "c" * w) := by
    intro w; rw [he1]; ring
  have hf2 : ∀ w, env "d2" + env "e2" * w = -env "d2" * (-1 + env "c" * w) := by
    intro w; rw [he2]; ring
  have hd1 : 0 < env "d1" := by
    rw [hf1] at hT1; exact pos_of_mul_pos_left hT1 (by linarith)
  have hd2 : 0 < -env "d2" := by
    rw [hf2] at hT2; exact pos_of_mul_pos_left hT2 (by linarith)
  have hs1 : Real.sqrt (env "d1") ≠ 0 := (Real.sqrt_pos.mpr hd1).ne'
  have hs2 : Real.sqrt (-env "d2") ≠ 0 := (Real.sqrt_pos.mpr hd2).ne'
  have hq1 : ∀ w, Real.sqrt (env "d1" + env "e1" * w) =
      Real.sqrt (env "d1") * Real.sqrt (1 + env "c" * w) := by
    intro w; rw [hf1, Real.sqrt_mul hd1.le]
  have hq2 : ∀ w, Real.sqrt (env "d2" + env "e2" * w) =
      Real.sqrt (-env "d2") * Real.sqrt (-1 + env "c" * w) := by
    intro w; rw [hf2, Real.sqrt_mul hd2.le]
  refine ⟨?_, ?_⟩
  · filter_upwards [hF, hnear1] with w hw hw1
    obtain ⟨hAw, -, hTw1, hTw2⟩ := hD w hw
    have hS1 : 0 < 1 + env "c" * w := by linarith
    have hS2 : 0 < -1 + env "c" * w := by linarith
    simp [rubi723r5Nondeg, Defined, eval, Interp.real, en1, ivm1R, iv2R, hb, hcz, hn1, hS1.le,
      hS2.le, hTw1.le, hTw2.le, hTw1.ne', hTw2.ne']
    exact ⟨hw1.le, fun h => hAw (hk1' h)⟩
  · have hev : (fun w => eval Interp.real (Function.update env "x" w) rubi723r5Nondeg.result)
        =ᶠ[𝓝 t]
        fun w => (env "b" * env "c" * (env "n" + 1))⁻¹ * (Real.sqrt (env "d1"))⁻¹ *
          (Real.sqrt (-env "d2"))⁻¹ *
          (env "a" + env "b" * Real.arcosh (env "c" * w)) ^ (k + 1) := by
      filter_upwards [hnear1] with w hw1
      have n1 : Real.sqrt (1 + env "c" * w) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      have n2 : Real.sqrt (-1 + env "c" * w) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      simp [rubi723r5Nondeg, eval, Interp.real, en1, ivm1R, hq1 w, hq2 w,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      field_simp
    have hA := ((hasDerivAt_arcosh_mul hct).const_mul (env "b")).const_add (env "a")
    have hor : env "a" + env "b" * Real.arcosh (env "c" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases hk : k < 0
      · exact Or.inl (hA0 hk)
      · exact Or.inr (by omega)
    have hP := (hasDerivAt_zpow (k + 1) _ hor).comp t hA
    refine ((hP.const_mul _).congr_of_eventuallyEq hev).congr_deriv ?_
    have hEF : eval Interp.real (Function.update env "x" t) rubi723r5Nondeg.body =
        (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k *
          (Real.sqrt (env "d1" + env "e1" * t) * Real.sqrt (env "d2" + env "e2" * t))⁻¹ := by
      simp [rubi723r5Nondeg, eval, Interp.real, hkn, ivm1R]
    rw [hEF, hq1 t, hq2 t, show k + 1 - 1 = k by ring]
    have hkr : ((k + 1 : ℤ) : ℝ) = env "n" + 1 := by rw [hn]; push_cast; ring
    rw [hkr]
    have n1 : Real.sqrt (1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    have n2 : Real.sqrt (-1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    generalize (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k = R
    field_simp

end OSR.IntegrationRec243
