import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic cosine rules

Proofs over ℝ of RUBI 7.2 rules for `a + b arcosh(c x)`. The real `arcosh` is only defined on
`[1, ∞)`, so an integrand defined near `x` forces `1 < c x` (a closed condition holding on a
neighbourhood holds strictly at its centre), where
`arcosh'(c x) = c / (sqrt(1 + c x) sqrt(-1 + c x))`:

* 7.2.2 #2 and 7.2.5 #2 (factors `(d x)^m` and `(d + e x)^m`) and 7.2.1 #2 (`n < -1`, with the
  derivative `c^2 x / (sqrt(1 + c x) sqrt(-1 + c x))` of the product of square roots) integrate
  by parts;
* 7.2.6 #1 substitutes `u = c + d x`;
* 7.2.1 #3, 7.2.2 #6 and 7.2.2 #1 substitute `u = a + b arcosh(c x)`, using
  `cosh(arcosh y) = y`, `sinh(arcosh y) = sqrt(y^2 - 1)` and `tanh(arcosh y) = sqrt(y^2 - 1) / y`.

The complex statements are vacuous (no complex interpretation of `transc1#arccosh`) and stay
unproved. -/

namespace OSR.IntegrationRec242

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

/-! ## RUBI 7.2.2 #2 -/

theorem rubi722r2Nondeg_real : rubi722r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi722r2Nondeg.conditions rubi722r2Nondeg.body
    rubi722r2Nondeg.result rubi722r2Nondeg.integrals
  intro env hc t hF
  have hW : env "d" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi722r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "n" := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi722r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hd, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi722r2Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi722r2Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi722r2Nondeg.body →
      (j < 0 → env "d" * w ≠ 0) ∧ 1 ≤ env "c" * w := by
    intro w h
    simp [rubi722r2Nondeg, Defined, eval, Interp.real, hkm, hkp, hk0] at h
    refine ⟨?_, ?_⟩
    · simp only [ne_eq, mul_eq_zero, not_or]; tauto
    · tauto
  have hd0 := (hD t hF.self_of_nhds).1
  have hct := one_lt_of_eventually_mul (hF.mono fun w hw => (hD w hw).2)
  have hnear1 : ∀ᶠ w in 𝓝 t, 1 < env "c" * w :=
    ((continuous_const.mul continuous_id).continuousAt (x := t)).eventually (Ioi_mem_nhds hct)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi722r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF, hnear1] with w hw hw1
    have hdw := (hD w hw).1
    have hdw' : j + 1 < 0 → env "d" * w ≠ 0 := fun h => hdw (hj1' h)
    have hS1 : 0 < 1 + env "c" * w := by linarith
    have hS2 : 0 < -1 + env "c" * w := by linarith
    simp only [ne_eq, mul_eq_zero, not_or] at hdw'
    simp [Defined, eval, Interp.real, em1, ep1, ivm1R, iv2R, hk1, hS1.le, hS2.le, hS1.ne',
      hS2.ne', hw1.le]
    tauto
  · filter_upwards [hF] with w hw
    have hdw := (hD w hw).1
    have hdw' : j + 1 < 0 → env "d" * w ≠ 0 := fun h => hdw (hj1' h)
    simp only [ne_eq, mul_eq_zero, not_or] at hdw'
    simp [rubi722r2Nondeg, Defined, eval, recEnv, Interp.real, em1, hkp, ivm1R, hd, hm1, hk0,
      (hD w hw).2]
    tauto
  · simp only [rubi722r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * t) ^ (j + 1) *
        (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ (k - 1) *
        (Real.sqrt (1 + env "c" * t) * Real.sqrt (-1 + env "c" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, ep1, ivm1R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi722r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi722r2Nondeg.result) =
        fun w => (env "d" * w) ^ (j + 1) *
            (env "a" + env "b" * Real.arcosh (env "c" * w)) ^ k * (env "d" * (env "m" + 1))⁻¹ +
          -env "b" * env "c" * env "n" * (env "d" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi722r2Nondeg, eval, recEnv, Interp.real, em1, hkp, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi722r2Nondeg.body =
        (env "d" * t) ^ j * (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k := by
      simp [rubi722r2Nondeg, eval, Interp.real, hkm, hkp]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_arcosh_mul hct).const_mul (env "b")).const_add (env "a")
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
    have hS1 : Real.sqrt (1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    have hS2 : Real.sqrt (-1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    generalize (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ (k - 1) = R
    generalize (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k = R1
    generalize (env "d" * t) ^ j = P
    generalize (env "d" * t) ^ (j + 1) = P1
    field_simp
    ring

/-! ## RUBI 7.2.5 #2 -/

theorem rubi725r2Nondeg_real : rubi725r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi725r2Nondeg.conditions rubi725r2Nondeg.body
    rubi725r2Nondeg.result rubi725r2Nondeg.integrals
  intro env hc t hF
  have hW : env "e" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [rubi725r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "n" := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi725r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨he, hm1⟩ := hW'
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi725r2Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi725r2Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi725r2Nondeg.body →
      (j < 0 → env "d" + env "e" * w ≠ 0) ∧ 1 ≤ env "c" * w := by
    intro w h
    simp [rubi725r2Nondeg, Defined, eval, Interp.real, hkm, hkp, hk0] at h
    refine ⟨?_, ?_⟩
    · tauto
    · tauto
  have hd0 := (hD t hF.self_of_nhds).1
  have hct := one_lt_of_eventually_mul (hF.mono fun w hw => (hD w hw).2)
  have hnear1 : ∀ᶠ w in 𝓝 t, 1 < env "c" * w :=
    ((continuous_const.mul continuous_id).continuousAt (x := t)).eventually (Ioi_mem_nhds hct)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi725r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF, hnear1] with w hw hw1
    have hdw := (hD w hw).1
    have hdw' : j + 1 < 0 → env "d" + env "e" * w ≠ 0 := fun h => hdw (hj1' h)
    have hS1 : 0 < 1 + env "c" * w := by linarith
    have hS2 : 0 < -1 + env "c" * w := by linarith
    simp [Defined, eval, Interp.real, em1, ep1, ivm1R, iv2R, hk1, hS1.le, hS2.le, hS1.ne',
      hS2.ne', hw1.le]
    tauto
  · filter_upwards [hF] with w hw
    have hdw := (hD w hw).1
    have hdw' : j + 1 < 0 → env "d" + env "e" * w ≠ 0 := fun h => hdw (hj1' h)
    simp [rubi725r2Nondeg, Defined, eval, recEnv, Interp.real, em1, hkp, ivm1R, he, hm1, hk0,
      (hD w hw).2]
    tauto
  · simp only [rubi725r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (j + 1) *
        (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ (k - 1) *
        (Real.sqrt (-1 + env "c" * t) * Real.sqrt (1 + env "c" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, ep1, ivm1R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi725r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi725r2Nondeg.result) =
        fun w => (env "d" + env "e" * w) ^ (j + 1) *
            (env "a" + env "b" * Real.arcosh (env "c" * w)) ^ k * (env "e" * (env "m" + 1))⁻¹ +
          -env "b" * env "c" * env "n" * (env "e" * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi725r2Nondeg, eval, recEnv, Interp.real, em1, hkp, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi725r2Nondeg.body =
        (env "d" + env "e" * t) ^ j * (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k := by
      simp [rubi725r2Nondeg, eval, Interp.real, hkm, hkp]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_arcosh_mul hct).const_mul (env "b")).const_add (env "a")
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
    have hS1 : Real.sqrt (1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    have hS2 : Real.sqrt (-1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    generalize (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ (k - 1) = R
    generalize (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k = R1
    generalize (env "d" + env "e" * t) ^ j = P
    generalize (env "d" + env "e" * t) ^ (j + 1) = P1
    field_simp
    ring

/-! ## RUBI 7.2.6 #1 -/

theorem rubi726r1Nondeg_real : rubi726r1Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi726r1Nondeg.conditions
    rubi726r1Nondeg.body rubi726r1Nondeg.result rubi726r1Nondeg.integrals
    rubi726r1Nondeg.substs
  intro env hc t hF
  have hne : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi726r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkp : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi726r1Nondeg, Defined, eval, Interp.real, hkp] at h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi726r1Nondeg.body →
      (k < 0 → env "a" + env "b" * Real.arcosh (env "c" + env "d" * w) ≠ 0) ∧
        1 ≤ env "c" + env "d" * w := by
    intro w h
    simp [rubi726r1Nondeg, Defined, eval, Interp.real, hkp] at h
    tauto
  have h0 := (hD t hF.self_of_nhds).1
  have hu0 := one_lt_of_eventually_lin hne (hF.mono fun w hw => (hD w hw).2)
  have hcA : ContinuousAt (fun u : ℝ => env "a" + env "b" * Real.arcosh u)
      (env "c" + env "d" * t) :=
    continuousAt_const.add (continuousAt_const.mul (Real.hasDerivAt_arcosh hu0).continuousAt)
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "c" + env "d" * t),
      (k < 0 → env "a" + env "b" * Real.arcosh u ≠ 0) ∧ 1 ≤ u := by
    by_cases hk : k < 0
    · filter_upwards [hcA.tendsto.eventually (eventually_ne_nhds (h0 hk)),
        Ioi_mem_nhds hu0] with u hu hu1
      exact ⟨fun _ => hu, le_of_lt hu1⟩
    · filter_upwards [Ioi_mem_nhds hu0] with u hu1
      exact ⟨fun h => absurd h hk, le_of_lt hu1⟩
  have hsub : substAt Interp.real env rubi726r1Nondeg.substs "x" "I1" t =
      env "c" + env "d" * t := by
    simp [rubi726r1Nondeg, substAt, eval]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi726r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards with w
      intro g hg
      simp only [rubi726r1Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simp [Defined, eval, Interp.real, hkp, hu.2]
      exact hu.1
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi726r1Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hne]
    · simp only [rubi726r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.arcosh (env "c" + env "d" * t)) ^ k)
          (env "c" + env "d" * t) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkp]
      have h := (hΦ'.comp t (hasDerivAt_lin (env "c") (env "d") t)).const_mul (env "d")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi726r1Nondeg.integrals.map (·.1))
            rubi726r1Nondeg.substs Φ "x" w) rubi726r1Nondeg.result) =
          fun w => (env "d")⁻¹ * Φ "I1" (env "c" + env "d" * w) := by
        funext w
        simp [rubi726r1Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      simp [rubi726r1Nondeg, eval, Interp.real, hkp]
      field_simp

/-! ## RUBI 7.2.1 #2 -/

/-- `sqrt(1 + c x) sqrt(-1 + c x)` has derivative `c^2 x / (sqrt(1 + c x) sqrt(-1 + c x))`. -/
private theorem hasDerivAt_sqrt_prod {c t : ℝ} (h : 1 < c * t) :
    HasDerivAt (fun w => Real.sqrt (1 + c * w) * Real.sqrt (-1 + c * w))
      (c ^ 2 * t * (Real.sqrt (1 + c * t) * Real.sqrt (-1 + c * t))⁻¹) t := by
  have h1 : 0 < 1 + c * t := by linarith
  have h2 : 0 < -1 + c * t := by linarith
  have hS1 := (Real.hasDerivAt_sqrt h1.ne').comp t (hasDerivAt_lin 1 c t)
  have hS2 := (Real.hasDerivAt_sqrt h2.ne').comp t (hasDerivAt_lin (-1) c t)
  refine (hS1.mul hS2).congr_deriv ?_
  simp only [Function.comp_apply]
  have e1 : Real.sqrt (1 + c * t) ^ 2 = 1 + c * t := Real.sq_sqrt h1.le
  have e2 : Real.sqrt (-1 + c * t) ^ 2 = -1 + c * t := Real.sq_sqrt h2.le
  have n1 : Real.sqrt (1 + c * t) ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
  have n2 : Real.sqrt (-1 + c * t) ≠ 0 := (Real.sqrt_pos.mpr h2).ne'
  generalize Real.sqrt (1 + c * t) = S1 at e1 n1 ⊢
  generalize Real.sqrt (-1 + c * t) = S2 at e2 n2 ⊢
  rw [show 1 / (2 * S1) * c * S2 + S1 * (1 / (2 * S2) * c) = c * (S1 ^ 2 + S2 ^ 2) / (2 * S1 * S2)
    by field_simp; ring, e1, e2]
  field_simp
  ring

theorem rubi721r2Nondeg_real : rubi721r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi721r2Nondeg.conditions rubi721r2Nondeg.body
    rubi721r2Nondeg.result rubi721r2Nondeg.integrals
  intro env hc t hF
  have hnlt : env "n" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi721r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW : env "b" * env "c" * (env "n" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n")
      (.int 1))) (.int 0)) (by simp [rubi721r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨hb, hcz⟩, hn1⟩ := hW'
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi721r2Nondeg, Defined, eval, Interp.real, hkn] at h
  have hn : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hkn
  have hk : k < -1 := by
    have : (k : ℝ) < -1 := hn ▸ hnlt
    exact_mod_cast this
  have hk0 : k < 0 := by omega
  have hk1 : k + 1 < 0 := by omega
  have en1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi721r2Nondeg.body →
      env "a" + env "b" * Real.arcosh (env "c" * w) ≠ 0 ∧ 1 ≤ env "c" * w := by
    intro w h
    simp [rubi721r2Nondeg, Defined, eval, Interp.real, hkn, hk0] at h
    tauto
  have hA0 := (hD t hF.self_of_nhds).1
  have hct := one_lt_of_eventually_mul (hF.mono fun w hw => (hD w hw).2)
  have hnear1 : ∀ᶠ w in 𝓝 t, 1 < env "c" * w :=
    ((continuous_const.mul continuous_id).continuousAt (x := t)).eventually (Ioi_mem_nhds hct)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi721r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF, hnear1] with w hw hw1
    have hAw := (hD w hw).1
    have hS1 : 0 < 1 + env "c" * w := by linarith
    have hS2 : 0 < -1 + env "c" * w := by linarith
    simp [Defined, eval, Interp.real, en1, ivm1R, iv2R, hAw, hS1.le, hS2.le, hS1.ne',
      hS2.ne', hw1.le]
  · filter_upwards [hF, hnear1] with w hw hw1
    have hAw := (hD w hw).1
    have hS1 : 0 < 1 + env "c" * w := by linarith
    have hS2 : 0 < -1 + env "c" * w := by linarith
    simp [rubi721r2Nondeg, Defined, eval, recEnv, Interp.real, en1, ivm1R, iv2R, hb, hcz, hn1,
      hAw, hS1.le, hS2.le, hw1.le]
  · simp only [rubi721r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t * (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ (k + 1) *
        (Real.sqrt (1 + env "c" * t) * Real.sqrt (-1 + env "c" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, en1, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi721r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi721r2Nondeg.result) =
        fun w => Real.sqrt (1 + env "c" * w) * Real.sqrt (-1 + env "c" * w) *
            (env "a" + env "b" * Real.arcosh (env "c" * w)) ^ (k + 1) *
            (env "b" * env "c" * (env "n" + 1))⁻¹ +
          -env "c" * (env "b" * (env "n" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi721r2Nondeg, eval, recEnv, Interp.real, en1, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi721r2Nondeg.body =
        (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k := by
      simp [rubi721r2Nondeg, eval, Interp.real, hkn]
    rw [hfun, hEF]
    have hR := hasDerivAt_sqrt_prod hct
    have hA := ((hasDerivAt_arcosh_mul hct).const_mul (env "b")).const_add (env "a")
    have hP := (hasDerivAt_zpow (k + 1) _ (Or.inl hA0)).comp t hA
    refine (((hR.mul hP).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [show k + 1 - 1 = k by ring]
    have hkr : ((k + 1 : ℤ) : ℝ) = env "n" + 1 := by rw [hn]; push_cast; ring
    rw [hkr]
    have n1 : Real.sqrt (1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    have n2 : Real.sqrt (-1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    have eP : (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ (k + 1) =
        (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k *
          (env "a" + env "b" * Real.arcosh (env "c" * t)) := zpow_add_one₀ hA0 k
    rw [eP]
    generalize (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k = R
    generalize env "a" + env "b" * Real.arcosh (env "c" * t) = A
    generalize Real.sqrt (1 + env "c" * t) = S1 at n1 ⊢
    generalize Real.sqrt (-1 + env "c" * t) = S2 at n2 ⊢
    field_simp
    ring

/-! ## RUBI 7.2.1 #3 -/

theorem rubi721r3Nondeg_real : rubi721r3Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi721r3Nondeg.conditions
    rubi721r3Nondeg.body rubi721r3Nondeg.result rubi721r3Nondeg.integrals
    rubi721r3Nondeg.substs
  intro env hc t hF
  have hW : env "b" * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.var "c")) (.int 0)) (by simp [rubi721r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨hb, hcz⟩ := hW'
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi721r3Nondeg, Defined, eval, Interp.real, hkn] at h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi721r3Nondeg.body →
      (k < 0 → env "a" + env "b" * Real.arcosh (env "c" * w) ≠ 0) ∧ 1 ≤ env "c" * w := by
    intro w h
    simp [rubi721r3Nondeg, Defined, eval, Interp.real, hkn] at h
    tauto
  have h0 := (hD t hF.self_of_nhds).1
  have hct := one_lt_of_eventually_mul (hF.mono fun w hw => (hD w hw).2)
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "a" + env "b" * Real.arcosh (env "c" * t)),
      k < 0 → u ≠ 0 := by
    by_cases hk : k < 0
    · filter_upwards [eventually_ne_nhds (h0 hk)] with u hu
      exact fun _ => hu
    · exact Filter.Eventually.of_forall fun _ h => absurd h hk
  have hsub : substAt Interp.real env rubi721r3Nondeg.substs "x" "I1" t =
      env "a" + env "b" * Real.arcosh (env "c" * t) := by
    simp [rubi721r3Nondeg, substAt, eval, Interp.real]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi721r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi721r3Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.real, (hD w hw).2]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simpa [Defined, eval, Interp.real, hkn, ivm1R, hb] using hu
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi721r3Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hb, hcz]
    · simp only [rubi721r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have harg : -(env "a" * (env "b")⁻¹) +
          (env "a" + env "b" * Real.arcosh (env "c" * t)) * (env "b")⁻¹ =
          Real.arcosh (env "c" * t) := by field_simp; ring
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k *
            Real.sinh (Real.arcosh (env "c" * t)))
          (env "a" + env "b" * Real.arcosh (env "c" * t)) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkn, ivm1R, harg,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      have hA := ((hasDerivAt_arcosh_mul hct).const_mul (env "b")).const_add (env "a")
      have h := (hΦ'.comp t hA).const_mul (env "b" * env "c")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi721r3Nondeg.integrals.map (·.1))
            rubi721r3Nondeg.substs Φ "x" w) rubi721r3Nondeg.result) =
          fun w => (env "b" * env "c")⁻¹ *
            Φ "I1" (env "a" + env "b" * Real.arcosh (env "c" * w)) := by
        funext w
        simp [rubi721r3Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      have hEF : eval Interp.real (Function.update env "x" t) rubi721r3Nondeg.body =
          (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k := by
        simp [rubi721r3Nondeg, eval, Interp.real, hkn]
      rw [hEF, Real.sinh_arcosh hct.le,
        show (env "c" * t) ^ 2 - 1 = (1 + env "c" * t) * (-1 + env "c" * t) by ring,
        Real.sqrt_mul (by linarith)]
      have n1 : Real.sqrt (1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      have n2 : Real.sqrt (-1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      field_simp

/-! ## RUBI 7.2.2 #6 -/

theorem rubi722r6Nondeg_real : rubi722r6Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi722r6Nondeg.conditions
    rubi722r6Nondeg.body rubi722r6Nondeg.result rubi722r6Nondeg.integrals
    rubi722r6Nondeg.substs
  intro env hc t hF
  have hmpos : 0 < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi722r6Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi722r6Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi722r6Nondeg, Defined, eval, Interp.real, hkm, hkn] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hj : 0 < j := by rw [hm] at hmpos; exact_mod_cast hmpos
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j + 1 < 0 := by omega
  have em1 : intValue? (env "m" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hW : env "b" * env "c" ^ (j + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.pow (.var "c") (.app2 .add (.var "m") (.int 1))))
      (.int 0)) (by simp [rubi722r6Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, em1, hj1] using h
  have hb : env "b" ≠ 0 := left_ne_zero_of_mul hW
  have hcz : env "c" ≠ 0 := by
    intro h; apply hW; rw [h, zero_zpow _ (by omega), mul_zero]
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi722r6Nondeg.body →
      (k < 0 → env "a" + env "b" * Real.arcosh (env "c" * w) ≠ 0) ∧ 1 ≤ env "c" * w := by
    intro w h
    simp [rubi722r6Nondeg, Defined, eval, Interp.real, hkm, hkn, hj0] at h
    tauto
  have h0 := (hD t hF.self_of_nhds).1
  have hct := one_lt_of_eventually_mul (hF.mono fun w hw => (hD w hw).2)
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "a" + env "b" * Real.arcosh (env "c" * t)),
      k < 0 → u ≠ 0 := by
    by_cases hk : k < 0
    · filter_upwards [eventually_ne_nhds (h0 hk)] with u hu
      exact fun _ => hu
    · exact Filter.Eventually.of_forall fun _ h => absurd h hk
  have hsub : substAt Interp.real env rubi722r6Nondeg.substs "x" "I1" t =
      env "a" + env "b" * Real.arcosh (env "c" * t) := by
    simp [rubi722r6Nondeg, substAt, eval, Interp.real]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi722r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi722r6Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.real, (hD w hw).2]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simpa [Defined, eval, Interp.real, hkn, hkm, hj0, ivm1R, hb] using hu
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi722r6Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, em1, hj1, hW]
    · simp only [rubi722r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have harg : -(env "a" * (env "b")⁻¹) +
          (env "a" + env "b" * Real.arcosh (env "c" * t)) * (env "b")⁻¹ =
          Real.arcosh (env "c" * t) := by field_simp; ring
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k *
            Real.cosh (Real.arcosh (env "c" * t)) ^ j * Real.sinh (Real.arcosh (env "c" * t)))
          (env "a" + env "b" * Real.arcosh (env "c" * t)) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkn, hkm, ivm1R, harg,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      have hA := ((hasDerivAt_arcosh_mul hct).const_mul (env "b")).const_add (env "a")
      have h := (hΦ'.comp t hA).const_mul (env "b" * env "c" ^ (j + 1))⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi722r6Nondeg.integrals.map (·.1))
            rubi722r6Nondeg.substs Φ "x" w) rubi722r6Nondeg.result) =
          fun w => (env "b" * env "c" ^ (j + 1))⁻¹ *
            Φ "I1" (env "a" + env "b" * Real.arcosh (env "c" * w)) := by
        funext w
        simp [rubi722r6Nondeg, substEnv, substAt, eval, Interp.real, ivm1R, em1]
      rw [hfun]
      apply h.congr_deriv
      have hEF : eval Interp.real (Function.update env "x" t) rubi722r6Nondeg.body =
          t ^ j * (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k := by
        simp [rubi722r6Nondeg, eval, Interp.real, hkn, hkm]
      rw [hEF, Real.cosh_arcosh hct.le, Real.sinh_arcosh hct.le,
        show (env "c" * t) ^ 2 - 1 = (1 + env "c" * t) * (-1 + env "c" * t) by ring,
        Real.sqrt_mul (by linarith), mul_zpow, zpow_add_one₀ hcz]
      have n1 : Real.sqrt (1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      have n2 : Real.sqrt (-1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      have hcj : env "c" ^ j ≠ 0 := zpow_ne_zero j hcz
      generalize (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k = R
      generalize env "c" ^ j = C at hcj ⊢
      field_simp

/-! ## RUBI 7.2.2 #1 -/

theorem rubi722r1Nondeg_real : rubi722r1Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi722r1Nondeg.conditions
    rubi722r1Nondeg.body rubi722r1Nondeg.result rubi722r1Nondeg.integrals
    rubi722r1Nondeg.substs
  intro env hc t hF
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi722r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "n" := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi722r1Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkn : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi722r1Nondeg, Defined, eval, Interp.real, hkn] at h
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi722r1Nondeg.body →
      (k < 0 → env "a" + env "b" * Real.arcosh (env "c" * w) ≠ 0) ∧ 1 ≤ env "c" * w ∧
        w ≠ 0 := by
    intro w h
    simp [rubi722r1Nondeg, Defined, eval, Interp.real, hkn, ivm1R] at h
    tauto
  have h0 := (hD t hF.self_of_nhds).1
  have hct := one_lt_of_eventually_mul (hF.mono fun w hw => (hD w hw).2.1)
  have ht0 := (hD t hF.self_of_nhds).2.2
  have hcz : env "c" ≠ 0 := by
    intro h; rw [h, zero_mul] at hct; linarith
  have hnear : ∀ᶠ u : ℝ in 𝓝 (env "a" + env "b" * Real.arcosh (env "c" * t)),
      k < 0 → u ≠ 0 := by
    by_cases hk : k < 0
    · filter_upwards [eventually_ne_nhds (h0 hk)] with u hu
      exact fun _ => hu
    · exact Filter.Eventually.of_forall fun _ h => absurd h hk
  have hsub : substAt Interp.real env rubi722r1Nondeg.substs "x" "I1" t =
      env "a" + env "b" * Real.arcosh (env "c" * t) := by
    simp [rubi722r1Nondeg, substAt, eval, Interp.real]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi722r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi722r1Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      simp [Defined, eval, Interp.real, (hD w hw).2.1]
    · rw [hsub]
      filter_upwards [hnear] with u hu
      simpa [Defined, eval, Interp.real, hkn, ivm1R, hb] using hu
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi722r1Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, hb]
    · simp only [rubi722r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have harg : -(env "a" * (env "b")⁻¹) +
          (env "a" + env "b" * Real.arcosh (env "c" * t)) * (env "b")⁻¹ =
          Real.arcosh (env "c" * t) := by field_simp; ring
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k *
            Real.tanh (Real.arcosh (env "c" * t)))
          (env "a" + env "b" * Real.arcosh (env "c" * t)) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkn, ivm1R, harg,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      have hA := ((hasDerivAt_arcosh_mul hct).const_mul (env "b")).const_add (env "a")
      have h := (hΦ'.comp t hA).const_mul (env "b")⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi722r1Nondeg.integrals.map (·.1))
            rubi722r1Nondeg.substs Φ "x" w) rubi722r1Nondeg.result) =
          fun w => (env "b")⁻¹ *
            Φ "I1" (env "a" + env "b" * Real.arcosh (env "c" * w)) := by
        funext w
        simp [rubi722r1Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      have hEF : eval Interp.real (Function.update env "x" t) rubi722r1Nondeg.body =
          (env "a" + env "b" * Real.arcosh (env "c" * t)) ^ k * t⁻¹ := by
        simp [rubi722r1Nondeg, eval, Interp.real, hkn, ivm1R]
      rw [hEF, Real.tanh_arcosh hct.le,
        show (env "c" * t) ^ 2 - 1 = (1 + env "c" * t) * (-1 + env "c" * t) by ring,
        Real.sqrt_mul (by linarith)]
      have n1 : Real.sqrt (1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      have n2 : Real.sqrt (-1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      field_simp

end OSR.IntegrationRec242
