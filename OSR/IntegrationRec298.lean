import OSR.IntegrationNum1

/-! # Strengthened variants with two integer exponents: explicit terms plus a residual integral

Proofs of RUBI rules whose result is an explicit term with powers `y^m z^n` plus at most one residual
integral. The derivative of the explicit term is built from the rule expression; the integrand is
recovered with `sin² + cos² = 1` (when trigonometric) and the stated parameter relations, separately
for each exponent equal to `0` or not (`linear_combination` coefficients computed by Gröbner
reduction). Rules with `csc`, `cot` or `arctan` are proved over ℝ only. -/

namespace OSR.IntegrationRec298

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem zsplit {K : Type} [Field K] (X : K) (j : ℤ) (n : ℕ) (h : X ≠ 0 ∨ 0 ≤ j) :
    X ^ (j + n) = X ^ j * X ^ n := by
  rcases h with h | h
  · rw [zpow_add₀ h, zpow_natCast]
  · lift j to ℕ using h
    rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_add]

/-! ## rubi1213r7Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1213r7Nondeg_real : rubi1213r7Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1213r7Nondeg.conditions rubi1213r7Nondeg.body
    rubi1213r7Nondeg.result rubi1213r7Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1213r7Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hr1 : (env "m" + (2 * env "p")) + 3 - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1213r7Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hn2 : ((2 * env "c") * env "f") + (((-1) * env "b") * env "g") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))) (.int 0)) (by simp [rubi1213r7Nondeg])
  have hn2v : ((2 * env "c") * env "f") + (-env "b" * env "g") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))) (.int 0)) (by simp [rubi1213r7Nondeg])
  have hn3 : ((2 * env "c") * env "d") + (((-1) * env "b") * env "e") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi1213r7Nondeg])
  have hn3v : ((2 * env "c") * env "d") + (-env "b" * env "e") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi1213r7Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 2))) (.int 0)) (by simp [rubi1213r7Nondeg])
  have hn4_0 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc4
  have hdc : env "c" ≠ 0 := by
    intro hzc
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (1) * hr0 - (-4*env "a") * hzc
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn2 (by linear_combination (2*env "f") * hzc + (-env "g") * hzb)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r7Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r7Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1213r7Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r7Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emm1, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r7Nondeg, Defined, eval, recEnv, Interp.real, emm1, emk1, ivm1R,
        iv2R] at h hn2 hn3 hn4_0 hdc ⊢
    try tauto
  · simp only [rubi1213r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 1) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emm1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1213r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r7Nondeg.result) =
            fun w => ((((((-2) * env "c") * ((env "e" * env "f") + (((-1) * env "d") * env "g"))) *
            ((env "d" + (env "e" * w))) ^ (m + 1)) *
            (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (k + 1)) *
            (((env "p" + 1) *
            ((((2 * env "c") * env "d") + (((-1) * env "b") * env "e"))) ^ 2))⁻¹) +
            ((((2 * env "c") * env "f") + (((-1) * env "b") * env "g")) *
            ((((2 * env "c") * env "d") + (((-1) * env "b") * env "e")))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1213r7Nondeg, eval, recEnv, Interp.real, emm1, emk1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1213r7Nondeg.body =
        (((env "d" + (env "e" * t))) ^ (m) * (env "f" + (env "g" * t))) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1213r7Nondeg, eval, Interp.real, hkm, hkk, iv2R]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((((-2) * env "c") *
        ((env "e" * env "f") +
        (((-1) * env "d") * env "g"))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t ((((env "p" + 1) * ((((2 * env "c") * env "d") + (((-1) * env "b") * env "e"))) ^ 2))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hr1c : (((m : ℤ) : ℝ) + (2 * ((k : ℤ) : ℝ))) + 3 - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hr1
    have hn4_0c : ((k : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn4_0
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdn0 : 2 * env "c" * env "d" + -(env "e" * env "b") ≠ 0 :=
            fun h0 => hn3 (by linear_combination (1) * h0)
        field_simp
        linear_combination (-env "d"*env "e"*env "g"/2 + env "e"^2*env "f"/2) * hr0 +
            (env "b"^2*env "d"*env "e"*env "g"/2 - env "b"^2*env "e"^2*env "f"/2 +
            2*env "b"*env "c"*env "d"*env "e"*env "g"*t - 2*env "b"*env "c"*env "e"^2*env "f"*t +
            2*env "c"^2*env "d"*env "e"*env "g"*t^2 - 2*env "c"^2*env "e"^2*env "f"*t^2) * hr1c
      · subst hm0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ k =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k + 1) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k + 2) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        have hdn0 : 2 * env "c" * env "d" + -(env "e" * env "b") ≠ 0 :=
            fun h0 => hn3 (by linear_combination (1) * h0)
        field_simp
        linear_combination (-env "a"*env "d"*env "e"*env "g"*Pk/2 +
            env "a"*env "e"^2*env "f"*Pk/2 - env "b"*env "d"*env "e"*env "g"*Pk*t*((k : ℤ) : ℝ) -
            2*env "b"*env "d"*env "e"*env "g"*Pk*t + env "b"*env "e"^2*env "f"*Pk*t*((k : ℤ) : ℝ) +
            2*env "b"*env "e"^2*env "f"*Pk*t -
            env "c"*env "d"*env "e"*env "g"*Pk*t^2*((k : ℤ) : ℝ) -
            2*env "c"*env "d"*env "e"*env "g"*Pk*t^2 +
            env "c"*env "e"^2*env "f"*Pk*t^2*((k : ℤ) : ℝ) + 2*env "c"*env "e"^2*env "f"*Pk*t^2) *
            hr0 + (env "a"*env "b"^2*env "d"*env "e"*env "g"*Pk/2 -
            env "a"*env "b"^2*env "e"^2*env "f"*Pk/2 + env "b"^3*env "d"*env "e"*env "g"*Pk*t -
            env "b"^3*env "e"^2*env "f"*Pk*t + 3*env "b"^2*env "c"*env "d"*env "e"*env "g"*Pk*t^2 -
            3*env "b"^2*env "c"*env "e"^2*env "f"*Pk*t^2 +
            4*env "b"*env "c"^2*env "d"*env "e"*env "g"*Pk*t^3 -
            4*env "b"*env "c"^2*env "e"^2*env "f"*Pk*t^3 +
            2*env "c"^3*env "d"*env "e"*env "g"*Pk*t^4 - 2*env "c"^3*env "e"^2*env "f"*Pk*t^4) *
            hr1c
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
            ((env "d" + (env "e" * t))) ^ 1 := by
          have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
            ((env "d" + (env "e" * t))) ^ 2 := by
          have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
            ((env "d" + (env "e" * t))) ^ 3 := by
          have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m]
        generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
        have hdn0 : 2 * env "c" * env "d" + -(env "e" * env "b") ≠ 0 :=
            fun h0 => hn3 (by linear_combination (1) * h0)
        field_simp
        linear_combination (-env "d"^2*env "e"*env "g"*Pm*((m : ℤ) : ℝ)/2 -
            env "d"^2*env "e"*env "g"*Pm/2 + env "d"*env "e"^2*env "f"*Pm*((m : ℤ) : ℝ)/2 +
            env "d"*env "e"^2*env "f"*Pm/2 - env "d"*env "e"^2*env "g"*Pm*t*((m : ℤ) : ℝ)/2 -
            env "d"*env "e"^2*env "g"*Pm*t/2 + env "e"^3*env "f"*Pm*t*((m : ℤ) : ℝ)/2 +
            env "e"^3*env "f"*Pm*t/2) * hr0 +
            (env "b"^2*env "d"^2*env "e"*env "g"*Pm/2 - env "b"^2*env "d"*env "e"^2*env "f"*Pm/2 +
            env "b"^2*env "d"*env "e"^2*env "g"*Pm*t/2 - env "b"^2*env "e"^3*env "f"*Pm*t/2 +
            2*env "b"*env "c"*env "d"^2*env "e"*env "g"*Pm*t -
            2*env "b"*env "c"*env "d"*env "e"^2*env "f"*Pm*t +
            2*env "b"*env "c"*env "d"*env "e"^2*env "g"*Pm*t^2 -
            2*env "b"*env "c"*env "e"^3*env "f"*Pm*t^2 +
            2*env "c"^2*env "d"^2*env "e"*env "g"*Pm*t^2 -
            2*env "c"^2*env "d"*env "e"^2*env "f"*Pm*t^2 +
            2*env "c"^2*env "d"*env "e"^2*env "g"*Pm*t^3 - 2*env "c"^2*env "e"^3*env "f"*Pm*t^3) *
            hr1c
      · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
            ((env "d" + (env "e" * t))) ^ 1 := by
          have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
            ((env "d" + (env "e" * t))) ^ 2 := by
          have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
            ((env "d" + (env "e" * t))) ^ 3 := by
          have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m]
        have hdmk : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ k =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k + 1) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k + 2) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        have hdn0 : env "d" * 2 * env "c" + -(env "e" * env "b") ≠ 0 :=
            fun h0 => hn3 (by linear_combination (1) * h0)
        field_simp
        linear_combination (-env "a"*env "d"^2*env "e"*env "g"*Pk*Pm*((m : ℤ) : ℝ)/2 -
            env "a"*env "d"^2*env "e"*env "g"*Pk*Pm/2 +
            env "a"*env "d"*env "e"^2*env "f"*Pk*Pm*((m : ℤ) : ℝ)/2 +
            env "a"*env "d"*env "e"^2*env "f"*Pk*Pm/2 -
            env "a"*env "d"*env "e"^2*env "g"*Pk*Pm*t*((m : ℤ) : ℝ)/2 -
            env "a"*env "d"*env "e"^2*env "g"*Pk*Pm*t/2 +
            env "a"*env "e"^3*env "f"*Pk*Pm*t*((m : ℤ) : ℝ)/2 +
            env "a"*env "e"^3*env "f"*Pk*Pm*t/2 -
            env "b"*env "d"^2*env "e"*env "g"*Pk*Pm*t*((k : ℤ) : ℝ) -
            env "b"*env "d"^2*env "e"*env "g"*Pk*Pm*t*((m : ℤ) : ℝ) -
            2*env "b"*env "d"^2*env "e"*env "g"*Pk*Pm*t +
            env "b"*env "d"*env "e"^2*env "f"*Pk*Pm*t*((k : ℤ) : ℝ) +
            env "b"*env "d"*env "e"^2*env "f"*Pk*Pm*t*((m : ℤ) : ℝ) +
            2*env "b"*env "d"*env "e"^2*env "f"*Pk*Pm*t -
            env "b"*env "d"*env "e"^2*env "g"*Pk*Pm*t^2*((k : ℤ) : ℝ) -
            env "b"*env "d"*env "e"^2*env "g"*Pk*Pm*t^2*((m : ℤ) : ℝ) -
            2*env "b"*env "d"*env "e"^2*env "g"*Pk*Pm*t^2 +
            env "b"*env "e"^3*env "f"*Pk*Pm*t^2*((k : ℤ) : ℝ) +
            env "b"*env "e"^3*env "f"*Pk*Pm*t^2*((m : ℤ) : ℝ) +
            2*env "b"*env "e"^3*env "f"*Pk*Pm*t^2 -
            env "c"*env "d"^2*env "e"*env "g"*Pk*Pm*t^2*((k : ℤ) : ℝ) -
            env "c"*env "d"^2*env "e"*env "g"*Pk*Pm*t^2*((m : ℤ) : ℝ) -
            2*env "c"*env "d"^2*env "e"*env "g"*Pk*Pm*t^2 +
            env "c"*env "d"*env "e"^2*env "f"*Pk*Pm*t^2*((k : ℤ) : ℝ) +
            env "c"*env "d"*env "e"^2*env "f"*Pk*Pm*t^2*((m : ℤ) : ℝ) +
            2*env "c"*env "d"*env "e"^2*env "f"*Pk*Pm*t^2 -
            env "c"*env "d"*env "e"^2*env "g"*Pk*Pm*t^3*((k : ℤ) : ℝ) -
            env "c"*env "d"*env "e"^2*env "g"*Pk*Pm*t^3*((m : ℤ) : ℝ) -
            2*env "c"*env "d"*env "e"^2*env "g"*Pk*Pm*t^3 +
            env "c"*env "e"^3*env "f"*Pk*Pm*t^3*((k : ℤ) : ℝ) +
            env "c"*env "e"^3*env "f"*Pk*Pm*t^3*((m : ℤ) : ℝ) +
            2*env "c"*env "e"^3*env "f"*Pk*Pm*t^3) * hr0 +
            (env "a"*env "b"^2*env "d"^2*env "e"*env "g"*Pk*Pm/2 -
            env "a"*env "b"^2*env "d"*env "e"^2*env "f"*Pk*Pm/2 +
            env "a"*env "b"^2*env "d"*env "e"^2*env "g"*Pk*Pm*t/2 -
            env "a"*env "b"^2*env "e"^3*env "f"*Pk*Pm*t/2 +
            env "b"^3*env "d"^2*env "e"*env "g"*Pk*Pm*t -
            env "b"^3*env "d"*env "e"^2*env "f"*Pk*Pm*t +
            env "b"^3*env "d"*env "e"^2*env "g"*Pk*Pm*t^2 - env "b"^3*env "e"^3*env "f"*Pk*Pm*t^2 +
            3*env "b"^2*env "c"*env "d"^2*env "e"*env "g"*Pk*Pm*t^2 -
            3*env "b"^2*env "c"*env "d"*env "e"^2*env "f"*Pk*Pm*t^2 +
            3*env "b"^2*env "c"*env "d"*env "e"^2*env "g"*Pk*Pm*t^3 -
            3*env "b"^2*env "c"*env "e"^3*env "f"*Pk*Pm*t^3 +
            4*env "b"*env "c"^2*env "d"^2*env "e"*env "g"*Pk*Pm*t^3 -
            4*env "b"*env "c"^2*env "d"*env "e"^2*env "f"*Pk*Pm*t^3 +
            4*env "b"*env "c"^2*env "d"*env "e"^2*env "g"*Pk*Pm*t^4 -
            4*env "b"*env "c"^2*env "e"^3*env "f"*Pk*Pm*t^4 +
            2*env "c"^3*env "d"^2*env "e"*env "g"*Pk*Pm*t^4 -
            2*env "c"^3*env "d"*env "e"^2*env "f"*Pk*Pm*t^4 +
            2*env "c"^3*env "d"*env "e"^2*env "g"*Pk*Pm*t^5 -
            2*env "c"^3*env "e"^3*env "f"*Pk*Pm*t^5) * hr1c

set_option maxHeartbeats 1000000 in
theorem rubi1213r7Nondeg_complex : rubi1213r7Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1213r7Nondeg.conditions rubi1213r7Nondeg.body
    rubi1213r7Nondeg.result rubi1213r7Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1213r7Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hr1 : (env "m" + (2 * env "p")) + 3 - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1213r7Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hn2 : ((2 * env "c") * env "f") + (((-1) * env "b") * env "g") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))) (.int 0)) (by simp [rubi1213r7Nondeg])
  have hn2v : ((2 * env "c") * env "f") + (-env "b" * env "g") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))) (.int 0)) (by simp [rubi1213r7Nondeg])
  have hn3 : ((2 * env "c") * env "d") + (((-1) * env "b") * env "e") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi1213r7Nondeg])
  have hn3v : ((2 * env "c") * env "d") + (-env "b" * env "e") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi1213r7Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 2))) (.int 0)) (by simp [rubi1213r7Nondeg])
  have hn4_0 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc4
  have hdc : env "c" ≠ 0 := by
    intro hzc
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (1) * hr0 - (-4*env "a") * hzc
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn2 (by linear_combination (2*env "f") * hzc + (-env "g") * hzb)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r7Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r7Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1213r7Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r7Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkk, emm1, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r7Nondeg, Defined, eval, recEnv, Interp.complex, emm1, emk1, ivm1C,
        iv2C] at h hn2 hn3 hn4_0 hdc ⊢
    try tauto
  · simp only [rubi1213r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 1) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkk, emm1, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1213r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r7Nondeg.result) =
            fun w => ((((((-2) * env "c") * ((env "e" * env "f") + (((-1) * env "d") * env "g"))) *
            ((env "d" + (env "e" * w))) ^ (m + 1)) *
            (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (k + 1)) *
            (((env "p" + 1) *
            ((((2 * env "c") * env "d") + (((-1) * env "b") * env "e"))) ^ 2))⁻¹) +
            ((((2 * env "c") * env "f") + (((-1) * env "b") * env "g")) *
            ((((2 * env "c") * env "d") + (((-1) * env "b") * env "e")))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1213r7Nondeg, eval, recEnv, Interp.complex, emm1, emk1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1213r7Nondeg.body =
        (((env "d" + (env "e" * t))) ^ (m) * (env "f" + (env "g" * t))) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1213r7Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((((-2) * env "c") *
        ((env "e" * env "f") +
        (((-1) * env "d") * env "g"))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t ((((env "p" + 1) * ((((2 * env "c") * env "d") + (((-1) * env "b") * env "e"))) ^ 2))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hr1c : (((m : ℤ) : ℂ) + (2 * ((k : ℤ) : ℂ))) + 3 - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hr1
    have hn4_0c : ((k : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn4_0
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdn0 : 2 * env "c" * env "d" + -(env "e" * env "b") ≠ 0 :=
            fun h0 => hn3 (by linear_combination (1) * h0)
        field_simp
        linear_combination (-env "d"*env "e"*env "g"/2 + env "e"^2*env "f"/2) * hr0 +
            (env "b"^2*env "d"*env "e"*env "g"/2 - env "b"^2*env "e"^2*env "f"/2 +
            2*env "b"*env "c"*env "d"*env "e"*env "g"*t - 2*env "b"*env "c"*env "e"^2*env "f"*t +
            2*env "c"^2*env "d"*env "e"*env "g"*t^2 - 2*env "c"^2*env "e"^2*env "f"*t^2) * hr1c
      · subst hm0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ k =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k + 1) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k + 2) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        have hdn0 : 2 * env "c" * env "d" + -(env "e" * env "b") ≠ 0 :=
            fun h0 => hn3 (by linear_combination (1) * h0)
        field_simp
        linear_combination (-env "a"*env "d"*env "e"*env "g"*Pk/2 +
            env "a"*env "e"^2*env "f"*Pk/2 - env "b"*env "d"*env "e"*env "g"*Pk*t*((k : ℤ) : ℂ) -
            2*env "b"*env "d"*env "e"*env "g"*Pk*t + env "b"*env "e"^2*env "f"*Pk*t*((k : ℤ) : ℂ) +
            2*env "b"*env "e"^2*env "f"*Pk*t -
            env "c"*env "d"*env "e"*env "g"*Pk*t^2*((k : ℤ) : ℂ) -
            2*env "c"*env "d"*env "e"*env "g"*Pk*t^2 +
            env "c"*env "e"^2*env "f"*Pk*t^2*((k : ℤ) : ℂ) + 2*env "c"*env "e"^2*env "f"*Pk*t^2) *
            hr0 + (env "a"*env "b"^2*env "d"*env "e"*env "g"*Pk/2 -
            env "a"*env "b"^2*env "e"^2*env "f"*Pk/2 + env "b"^3*env "d"*env "e"*env "g"*Pk*t -
            env "b"^3*env "e"^2*env "f"*Pk*t + 3*env "b"^2*env "c"*env "d"*env "e"*env "g"*Pk*t^2 -
            3*env "b"^2*env "c"*env "e"^2*env "f"*Pk*t^2 +
            4*env "b"*env "c"^2*env "d"*env "e"*env "g"*Pk*t^3 -
            4*env "b"*env "c"^2*env "e"^2*env "f"*Pk*t^3 +
            2*env "c"^3*env "d"*env "e"*env "g"*Pk*t^4 - 2*env "c"^3*env "e"^2*env "f"*Pk*t^4) *
            hr1c
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
            ((env "d" + (env "e" * t))) ^ 1 := by
          have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
            ((env "d" + (env "e" * t))) ^ 2 := by
          have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
            ((env "d" + (env "e" * t))) ^ 3 := by
          have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m]
        generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
        have hdn0 : 2 * env "c" * env "d" + -(env "e" * env "b") ≠ 0 :=
            fun h0 => hn3 (by linear_combination (1) * h0)
        field_simp
        linear_combination (-env "d"^2*env "e"*env "g"*Pm*((m : ℤ) : ℂ)/2 -
            env "d"^2*env "e"*env "g"*Pm/2 + env "d"*env "e"^2*env "f"*Pm*((m : ℤ) : ℂ)/2 +
            env "d"*env "e"^2*env "f"*Pm/2 - env "d"*env "e"^2*env "g"*Pm*t*((m : ℤ) : ℂ)/2 -
            env "d"*env "e"^2*env "g"*Pm*t/2 + env "e"^3*env "f"*Pm*t*((m : ℤ) : ℂ)/2 +
            env "e"^3*env "f"*Pm*t/2) * hr0 +
            (env "b"^2*env "d"^2*env "e"*env "g"*Pm/2 - env "b"^2*env "d"*env "e"^2*env "f"*Pm/2 +
            env "b"^2*env "d"*env "e"^2*env "g"*Pm*t/2 - env "b"^2*env "e"^3*env "f"*Pm*t/2 +
            2*env "b"*env "c"*env "d"^2*env "e"*env "g"*Pm*t -
            2*env "b"*env "c"*env "d"*env "e"^2*env "f"*Pm*t +
            2*env "b"*env "c"*env "d"*env "e"^2*env "g"*Pm*t^2 -
            2*env "b"*env "c"*env "e"^3*env "f"*Pm*t^2 +
            2*env "c"^2*env "d"^2*env "e"*env "g"*Pm*t^2 -
            2*env "c"^2*env "d"*env "e"^2*env "f"*Pm*t^2 +
            2*env "c"^2*env "d"*env "e"^2*env "g"*Pm*t^3 - 2*env "c"^2*env "e"^3*env "f"*Pm*t^3) *
            hr1c
      · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
            ((env "d" + (env "e" * t))) ^ 1 := by
          have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
            ((env "d" + (env "e" * t))) ^ 2 := by
          have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
            ((env "d" + (env "e" * t))) ^ 3 := by
          have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m]
        have hdmk : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ k =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k + 1) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k + 2) =
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) *
            (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        have hdn0 : env "d" * 2 * env "c" + -(env "e" * env "b") ≠ 0 :=
            fun h0 => hn3 (by linear_combination (1) * h0)
        field_simp
        linear_combination (-env "a"*env "d"^2*env "e"*env "g"*Pk*Pm*((m : ℤ) : ℂ)/2 -
            env "a"*env "d"^2*env "e"*env "g"*Pk*Pm/2 +
            env "a"*env "d"*env "e"^2*env "f"*Pk*Pm*((m : ℤ) : ℂ)/2 +
            env "a"*env "d"*env "e"^2*env "f"*Pk*Pm/2 -
            env "a"*env "d"*env "e"^2*env "g"*Pk*Pm*t*((m : ℤ) : ℂ)/2 -
            env "a"*env "d"*env "e"^2*env "g"*Pk*Pm*t/2 +
            env "a"*env "e"^3*env "f"*Pk*Pm*t*((m : ℤ) : ℂ)/2 +
            env "a"*env "e"^3*env "f"*Pk*Pm*t/2 -
            env "b"*env "d"^2*env "e"*env "g"*Pk*Pm*t*((k : ℤ) : ℂ) -
            env "b"*env "d"^2*env "e"*env "g"*Pk*Pm*t*((m : ℤ) : ℂ) -
            2*env "b"*env "d"^2*env "e"*env "g"*Pk*Pm*t +
            env "b"*env "d"*env "e"^2*env "f"*Pk*Pm*t*((k : ℤ) : ℂ) +
            env "b"*env "d"*env "e"^2*env "f"*Pk*Pm*t*((m : ℤ) : ℂ) +
            2*env "b"*env "d"*env "e"^2*env "f"*Pk*Pm*t -
            env "b"*env "d"*env "e"^2*env "g"*Pk*Pm*t^2*((k : ℤ) : ℂ) -
            env "b"*env "d"*env "e"^2*env "g"*Pk*Pm*t^2*((m : ℤ) : ℂ) -
            2*env "b"*env "d"*env "e"^2*env "g"*Pk*Pm*t^2 +
            env "b"*env "e"^3*env "f"*Pk*Pm*t^2*((k : ℤ) : ℂ) +
            env "b"*env "e"^3*env "f"*Pk*Pm*t^2*((m : ℤ) : ℂ) +
            2*env "b"*env "e"^3*env "f"*Pk*Pm*t^2 -
            env "c"*env "d"^2*env "e"*env "g"*Pk*Pm*t^2*((k : ℤ) : ℂ) -
            env "c"*env "d"^2*env "e"*env "g"*Pk*Pm*t^2*((m : ℤ) : ℂ) -
            2*env "c"*env "d"^2*env "e"*env "g"*Pk*Pm*t^2 +
            env "c"*env "d"*env "e"^2*env "f"*Pk*Pm*t^2*((k : ℤ) : ℂ) +
            env "c"*env "d"*env "e"^2*env "f"*Pk*Pm*t^2*((m : ℤ) : ℂ) +
            2*env "c"*env "d"*env "e"^2*env "f"*Pk*Pm*t^2 -
            env "c"*env "d"*env "e"^2*env "g"*Pk*Pm*t^3*((k : ℤ) : ℂ) -
            env "c"*env "d"*env "e"^2*env "g"*Pk*Pm*t^3*((m : ℤ) : ℂ) -
            2*env "c"*env "d"*env "e"^2*env "g"*Pk*Pm*t^3 +
            env "c"*env "e"^3*env "f"*Pk*Pm*t^3*((k : ℤ) : ℂ) +
            env "c"*env "e"^3*env "f"*Pk*Pm*t^3*((m : ℤ) : ℂ) +
            2*env "c"*env "e"^3*env "f"*Pk*Pm*t^3) * hr0 +
            (env "a"*env "b"^2*env "d"^2*env "e"*env "g"*Pk*Pm/2 -
            env "a"*env "b"^2*env "d"*env "e"^2*env "f"*Pk*Pm/2 +
            env "a"*env "b"^2*env "d"*env "e"^2*env "g"*Pk*Pm*t/2 -
            env "a"*env "b"^2*env "e"^3*env "f"*Pk*Pm*t/2 +
            env "b"^3*env "d"^2*env "e"*env "g"*Pk*Pm*t -
            env "b"^3*env "d"*env "e"^2*env "f"*Pk*Pm*t +
            env "b"^3*env "d"*env "e"^2*env "g"*Pk*Pm*t^2 - env "b"^3*env "e"^3*env "f"*Pk*Pm*t^2 +
            3*env "b"^2*env "c"*env "d"^2*env "e"*env "g"*Pk*Pm*t^2 -
            3*env "b"^2*env "c"*env "d"*env "e"^2*env "f"*Pk*Pm*t^2 +
            3*env "b"^2*env "c"*env "d"*env "e"^2*env "g"*Pk*Pm*t^3 -
            3*env "b"^2*env "c"*env "e"^3*env "f"*Pk*Pm*t^3 +
            4*env "b"*env "c"^2*env "d"^2*env "e"*env "g"*Pk*Pm*t^3 -
            4*env "b"*env "c"^2*env "d"*env "e"^2*env "f"*Pk*Pm*t^3 +
            4*env "b"*env "c"^2*env "d"*env "e"^2*env "g"*Pk*Pm*t^4 -
            4*env "b"*env "c"^2*env "e"^3*env "f"*Pk*Pm*t^4 +
            2*env "c"^3*env "d"^2*env "e"*env "g"*Pk*Pm*t^4 -
            2*env "c"^3*env "d"*env "e"^2*env "f"*Pk*Pm*t^4 +
            2*env "c"^3*env "d"*env "e"^2*env "g"*Pk*Pm*t^5 -
            2*env "c"^3*env "e"^3*env "f"*Pk*Pm*t^5) * hr1c

/-! ## rubi4522r1Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4522r1Nondeg_real : rubi4522r1Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4522r1Nondeg.conditions rubi4522r1Nondeg.body
    rubi4522r1Nondeg.result
  intro env hc t hF
  have hr0 : (env "b" * env "c") + (env "a" * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0)) (by simp [rubi4522r1Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4522r1Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hr2 : (env "m" + env "n") + 1 - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)) (.int 0)) (by simp [rubi4522r1Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hn3 : (2 * env "m") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1)) (.int 0)) (by simp [rubi4522r1Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4522r1Nondeg])
  have hn4_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_2 : (2 * env "m") + 1 ≠ 0 := by
    have h := hc4
    simp [Cond.Holds, Defined, eval] at h
    tauto
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn4_0 (by linear_combination (1) * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4522r1Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4522r1Nondeg, Defined, eval, Interp.real, hkm, hkk, Fn.csc] at h
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "n" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "n" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4522r1Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4522r1Nondeg, Defined, eval, Interp.real, hkm, hkk, Fn.csc] at h ⊢
    try tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4522r1Nondeg, Defined, eval, Interp.real, hkm, hkk, ivm1R,
        Fn.csc] at h hn3 hn4_0 hn4_1 hn4_2 hdb ⊢
    try tauto
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w)
        rubi4522r1Nondeg.result) =
            fun w => ((((env "b" *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m)) *
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (k)) *
            (((env "a" * env "f") * ((2 * env "m") + 1)))⁻¹) := by
      funext w
      simp [rubi4522r1Nondeg, eval, Interp.real, hkm, hkk, ivm1R, Fn.csc, Real.cot_eq_cos_div_sin,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4522r1Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k) := by
      simp [rubi4522r1Nondeg, eval, Interp.real, hkm, hkk, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t ((((env "a" * env "f") * ((2 * env "m") + 1)))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hr2c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hr2
    have hn3c : (2 * ((m : ℤ) : ℝ)) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3
    have hn4_2c : (2 * ((m : ℤ) : ℝ)) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn4_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "b") * hP + (0) * hr0 + (0) * hr1 + (-env "a"*S - env "b") * hr2c
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ k =
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k - 1) *
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k + 1) =
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k - 1) *
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k + 2) =
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k - 1) *
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        refine mul_left_cancel₀ hn4_0 ?_
        linear_combination (-env "a"*env "b"*env "c"*Pk*S -
            env "a"*env "b"*env "d"*Pk*((k : ℤ) : ℝ) - env "a"*env "b"*env "d"*Pk) * hP +
            (-env "a"*Pk*S + env "b"*Pk*S^2*((k : ℤ) : ℝ) - env "b"*Pk*((k : ℤ) : ℝ) -
            env "b"*Pk) * hr0 + (-env "c"*Pk*S^2) * hr1 +
            (-env "b"^2*env "c"*Pk*S^2 + env "b"^2*env "c"*Pk) * hr2c
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
            1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        have hden : ((m : ℤ) : ℝ) * 2 + 1 ≠ 0 := fun h0 => hn3c (by linear_combination (1) * h0)
        rw [div_eq_iff hden]
        linear_combination (-env "a"*env "b"*Pm*S - env "b"^2*Pm*((m : ℤ) : ℝ) - env "b"^2*Pm) *
            hP + (0) * hr0 + (-2*Pm*S^2*((m : ℤ) : ℝ) - Pm*S^2) * hr1 +
            (-2*env "a"*env "b"*Pm*S - env "b"^2*Pm*S^2 - env "b"^2*Pm) * hr2c
      · have hdmm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
          1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ k =
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k - 1) *
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k + 1) =
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k - 1) *
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k + 2) =
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k - 1) *
            ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        have hdn0 : ((m : ℤ) : ℝ) * 2 + 1 ≠ 0 := fun h0 => hn3c (by linear_combination (1) * h0)
        field_simp
        linear_combination (-env "a"*env "b"*env "c"*env "f"*Pk*Pm*S^2 -
            env "a"*env "b"*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) -
            env "a"*env "b"*env "d"*env "f"*Pk*Pm*S -
            env "b"^2*env "c"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) - env "b"^2*env "c"*env "f"*Pk*Pm*S -
            env "b"^2*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) -
            env "b"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) - env "b"^2*env "d"*env "f"*Pk*Pm) * hP +
            (-2*env "a"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) - 2*env "a"*env "f"*Pk*Pm*S^2 -
            env "b"*env "f"*Pk*Pm*S^3*((m : ℤ) : ℝ) - env "b"*env "f"*Pk*Pm*S^3 -
            env "b"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) - env "b"*env "f"*Pk*Pm*S) * hr0 +
            (-2*env "c"*env "f"*Pk*Pm*S^3*((m : ℤ) : ℝ) - env "c"*env "f"*Pk*Pm*S^3 +
            env "d"*env "f"*Pk*Pm*S^2) * hr1 +
            (env "a"*env "b"*env "d"*env "f"*Pk*Pm*S^3 - env "a"*env "b"*env "d"*env "f"*Pk*Pm*S +
            env "b"^2*env "d"*env "f"*Pk*Pm*S^2 - env "b"^2*env "d"*env "f"*Pk*Pm) * hr2c

/-! ## rubi4542r17Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4542r17Nondeg_real : rubi4542r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r17Nondeg.conditions rubi4542r17Nondeg.body
    rubi4542r17Nondeg.result rubi4542r17Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r17Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn3 : (env "m" + env "n") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)) (.int 0)) (by simp [rubi4542r17Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int 0)) (by simp [rubi4542r17Nondeg])
  have hn4_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_1 : (env "m" + env "n") + 1 ≠ 0 := by
    have h := hc4
    simp [Cond.Holds, Defined, eval] at h
    tauto
  have hc5 :=
      hc (.ne (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int 0)) (by simp [rubi4542r17Nondeg])
  have hn5_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_1 : (env "m" + env "n") + 1 ≠ 0 := by
    have h := hc5
    simp [Cond.Holds, Defined, eval] at h
    tauto
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr0 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn5_0 (by linear_combination (1) * hzb)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r17Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r17Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc] at h
  have hb1 : -1 < m := by
    have h := hc (.ge (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4542r17Nondeg])
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have hb2 : -1 < k := by
    have h := hc (.ge (.var "n") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4542r17Nondeg])
    have h' : (-1 : ℝ) < ((k : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
      simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "n" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "n" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r17Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) ∧
          (k < 0 → (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4542r17Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, hkk, Fn.csc] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r17Nondeg, Defined, eval, recEnv, Interp.real, hkm, hkk, ivm1R,
        Fn.csc] at h hn3 hn4_0 hn4_1 hn5_0 hn5_1 hda ⊢
    try tauto
  · simp only [rubi4542r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k)) *
        ((((env "A" * env "b") * ((env "m" + env "n") + 1)) + ((env "b" * env "C") * env "n")) +
        ((((env "a" * env "C") * env "m") + ((env "b" * env "B") * ((env "m" + env "n") + 1))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, hkk, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r17Nondeg.result) =
            fun w => ((((((-1) * env "C") *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m)) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (k)) *
            ((env "f" * ((env "m" + env "n") + 1)))⁻¹) +
            (1 * ((env "b" * ((env "m" + env "n") + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4542r17Nondeg, eval, recEnv, Interp.real, hkm, hkk, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r17Nondeg.body =
        (((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k)) *
        ((env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r17Nondeg, eval, Interp.real, hkm, hkk, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "C"))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) ((hasDerivAt_const t (env "d")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)))).mul (hasDerivAt_const t (((env "f" * ((env "m" + env "n") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hn3c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn3
    have hn4_1c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn4_1
    have hn5_1c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn5_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (env "C") * hP + (0) * hr0
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ k =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 1 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 1) =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 2 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 2) =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 3 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        have hden : ((k : ℤ) : ℝ) + 1 ≠ 0 := by exact_mod_cast (show k + 1 ≠ 0 by omega)
        rw [div_eq_iff hden]
        linear_combination (env "C"*env "d"*Pk*((k : ℤ) : ℝ) + env "C"*env "d"*Pk) * hP + (0) * hr0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
            1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        have hden : ((m : ℤ) : ℝ) + 1 ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        rw [div_eq_iff hden]
        linear_combination (env "C"*env "a"*env "b"*Pm*S + env "C"*env "b"^2*Pm*((m : ℤ) : ℝ) +
            env "C"*env "b"^2*Pm) * hP + (env "C"*Pm*S^2*((m : ℤ) : ℝ)) * hr0
      · have hdmm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
          1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ k =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 1 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 1) =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 2 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 2) =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 3 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
        generalize ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (env "C"*env "a"*env "b"*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) +
            env "C"*env "a"*env "b"*env "d"*env "f"*Pk*Pm*S +
            env "C"*env "b"^2*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) +
            env "C"*env "b"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) +
            env "C"*env "b"^2*env "d"*env "f"*Pk*Pm) * hP +
            (env "C"*env "d"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ)) * hr0

/-! ## rubi4542r18Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4542r18Nondeg_real : rubi4542r18Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r18Nondeg.conditions rubi4542r18Nondeg.body
    rubi4542r18Nondeg.result rubi4542r18Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r18Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn3 : (env "m" + env "n") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)) (.int 0)) (by simp [rubi4542r18Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int 0)) (by simp [rubi4542r18Nondeg])
  have hn4_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_1 : (env "m" + env "n") + 1 ≠ 0 := by
    have h := hc4
    simp [Cond.Holds, Defined, eval] at h
    tauto
  have hc5 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int 0)) (by simp [rubi4542r18Nondeg])
  have hn5_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_1 : (env "m" + env "n") + 1 ≠ 0 := by
    have h := hc5
    simp [Cond.Holds, Defined, eval] at h
    tauto
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr0 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn4_0 (by linear_combination (1) * hzb)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r18Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r18Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc] at h
  have hb1 : -1 < m := by
    have h := hc (.ge (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4542r18Nondeg])
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have hb2 : -1 < k := by
    have h := hc (.ge (.var "n") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))) (by simp [rubi4542r18Nondeg])
    have h' : (-1 : ℝ) < ((k : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
      simp [Cond.Holds, Defined, eval, Interp.real, ivm1R] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "n" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "n" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r18Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) ∧
          (k < 0 → (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4542r18Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, hkk, Fn.csc] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r18Nondeg, Defined, eval, recEnv, Interp.real, hkm, hkk, ivm1R,
        Fn.csc] at h hn3 hn4_0 hn4_1 hn5_0 hn5_1 hda ⊢
    try tauto
  · simp only [rubi4542r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k)) *
        ((((env "A" * env "b") * ((env "m" + env "n") + 1)) + ((env "b" * env "C") * env "n")) +
        (((env "a" * env "C") * env "m") * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, hkk, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r18Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r18Nondeg.result) =
            fun w => ((((((-1) * env "C") *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m)) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (k)) *
            ((env "f" * ((env "m" + env "n") + 1)))⁻¹) +
            (1 * ((env "b" * ((env "m" + env "n") + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4542r18Nondeg, eval, recEnv, Interp.real, hkm, hkk, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r18Nondeg.body =
        (((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k)) *
        (env "A" + (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r18Nondeg, eval, Interp.real, hkm, hkk, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "C"))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) ((hasDerivAt_const t (env "d")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)))).mul (hasDerivAt_const t (((env "f" * ((env "m" + env "n") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hn3c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn3
    have hn4_1c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn4_1
    have hn5_1c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn5_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (env "C") * hP + (0) * hr0
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ k =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 1 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 1) =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 2 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 2) =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 3 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        have hden : ((k : ℤ) : ℝ) + 1 ≠ 0 := by exact_mod_cast (show k + 1 ≠ 0 by omega)
        rw [div_eq_iff hden]
        linear_combination (env "C"*env "d"*Pk*((k : ℤ) : ℝ) + env "C"*env "d"*Pk) * hP + (0) * hr0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
            1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        have hden : ((m : ℤ) : ℝ) + 1 ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
        rw [div_eq_iff hden]
        linear_combination (env "C"*env "a"*env "b"*Pm*S + env "C"*env "b"^2*Pm*((m : ℤ) : ℝ) +
            env "C"*env "b"^2*Pm) * hP + (env "C"*Pm*S^2*((m : ℤ) : ℝ)) * hr0
      · have hdmm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ m -
          1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ m =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 1) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m + 2) =
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ k =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 1 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 1) =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 2 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k + 2) =
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 3 := by
          have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
        generalize ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (env "C"*env "a"*env "b"*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) +
            env "C"*env "a"*env "b"*env "d"*env "f"*Pk*Pm*S +
            env "C"*env "b"^2*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) +
            env "C"*env "b"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) +
            env "C"*env "b"^2*env "d"*env "f"*Pk*Pm) * hP +
            (env "C"*env "d"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ)) * hr0

/-! ## rubi6113r15Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi6113r15Nondeg_real : rubi6113r15Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6113r15Nondeg.conditions rubi6113r15Nondeg.body
    rubi6113r15Nondeg.result rubi6113r15Nondeg.integrals
  intro env hc t hF
  have hr1 : (env "b" * env "e") + (((-2) * env "c") * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r15Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi6113r15Nondeg])
  have hn2_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r15Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi6113r15Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6113r15Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r15Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emm2, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r15Nondeg, Defined, eval, recEnv, Interp.real, emm1, ivm1R,
        iv2R] at h hn2_0 hn2_1 ⊢
    try tauto
  · simp only [rubi6113r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 2) *
        Real.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emm2, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6113r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r15Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            Real.sinh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) *
            ((env "e" * (env "m" + 1)))⁻¹) +
            (((-2) * env "c") * (((env "e") ^ 2 * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi6113r15Nondeg, eval, recEnv, Interp.real, emm1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi6113r15Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Real.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r15Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul ((Real.hasDerivAt_sinh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((env "e" * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m, e2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
      generalize Real.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Real.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      field_simp
      linear_combination (0) * hP +
          (C*env "d"^2*Pm + 2*C*env "d"*env "e"*Pm*t + C*env "e"^2*Pm*t^2) * hr1

set_option maxHeartbeats 1000000 in
theorem rubi6113r15Nondeg_complex : rubi6113r15Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6113r15Nondeg.conditions rubi6113r15Nondeg.body
    rubi6113r15Nondeg.result rubi6113r15Nondeg.integrals
  intro env hc t hF
  have hr1 : (env "b" * env "e") + (((-2) * env "c") * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r15Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi6113r15Nondeg])
  have hn2_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r15Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi6113r15Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi6113r15Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r15Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emm2, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r15Nondeg, Defined, eval, recEnv, Interp.complex, emm1, ivm1C,
        iv2C] at h hn2_0 hn2_1 ⊢
    try tauto
  · simp only [rubi6113r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 2) *
        Complex.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emm2, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6113r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r15Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            Complex.sinh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) *
            ((env "e" * (env "m" + 1)))⁻¹) +
            (((-2) * env "c") * (((env "e") ^ 2 * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi6113r15Nondeg, eval, recEnv, Interp.complex, emm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi6113r15Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Complex.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r15Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul ((Complex.hasDerivAt_sinh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((env "e" * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m, e2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
      generalize Complex.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Complex.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      field_simp
      linear_combination (0) * hP +
          (C*env "d"^2*Pm + 2*C*env "d"*env "e"*Pm*t + C*env "e"^2*Pm*t^2) * hr1

/-! ## rubi6113r16Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi6113r16Nondeg_real : rubi6113r16Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6113r16Nondeg.conditions rubi6113r16Nondeg.body
    rubi6113r16Nondeg.result rubi6113r16Nondeg.integrals
  intro env hc t hF
  have hr1 : (env "b" * env "e") + (((-2) * env "c") * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r16Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi6113r16Nondeg])
  have hn2_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r16Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi6113r16Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6113r16Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r16Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emm2, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r16Nondeg, Defined, eval, recEnv, Interp.real, emm1, ivm1R,
        iv2R] at h hn2_0 hn2_1 ⊢
    try tauto
  · simp only [rubi6113r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 2) *
        Real.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emm2, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6113r16Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r16Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            Real.cosh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) *
            ((env "e" * (env "m" + 1)))⁻¹) +
            (((-2) * env "c") * (((env "e") ^ 2 * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi6113r16Nondeg, eval, recEnv, Interp.real, emm1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi6113r16Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Real.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r16Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul ((Real.hasDerivAt_cosh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((env "e" * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m, e2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
      generalize Real.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Real.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      field_simp
      linear_combination (0) * hP +
          (env "d"^2*Pm*S + 2*env "d"*env "e"*Pm*S*t + env "e"^2*Pm*S*t^2) * hr1

set_option maxHeartbeats 1000000 in
theorem rubi6113r16Nondeg_complex : rubi6113r16Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6113r16Nondeg.conditions rubi6113r16Nondeg.body
    rubi6113r16Nondeg.result rubi6113r16Nondeg.integrals
  intro env hc t hF
  have hr1 : (env "b" * env "e") + (((-2) * env "c") * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r16Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi6113r16Nondeg])
  have hn2_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r16Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi6113r16Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi6113r16Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r16Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emm2, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r16Nondeg, Defined, eval, recEnv, Interp.complex, emm1, ivm1C,
        iv2C] at h hn2_0 hn2_1 ⊢
    try tauto
  · simp only [rubi6113r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 2) *
        Complex.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emm2, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6113r16Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r16Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            Complex.cosh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) *
            ((env "e" * (env "m" + 1)))⁻¹) +
            (((-2) * env "c") * (((env "e") ^ 2 * (env "m" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi6113r16Nondeg, eval, recEnv, Interp.complex, emm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi6113r16Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Complex.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r16Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul ((Complex.hasDerivAt_cosh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((env "e" * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "d" + (env "e" * t))) ^ m = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 1) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m, e2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
      generalize Complex.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Complex.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      field_simp
      linear_combination (0) * hP +
          (env "d"^2*Pm*S + 2*env "d"*env "e"*Pm*S*t + env "e"^2*Pm*S*t^2) * hr1

/-! ## rubi4110r15Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4110r15Nondeg_real : rubi4110r15Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4110r15Nondeg.conditions rubi4110r15Nondeg.body
    rubi4110r15Nondeg.result rubi4110r15Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.var "n") (.int 2))) (.int 0)) (by simp [rubi4110r15Nondeg])
  have hn1_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc1
  have hn1_1 : env "n" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc1
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4110r15Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi4110r15Nondeg])
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "n" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4110r15Nondeg.body →
      (m < 0 → (env "b" * Real.sin ((env "e" + (env "f" * w)))) ≠ 0) := by
    intro w h
    simp [rubi4110r15Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4110r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm2] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4110r15Nondeg, Defined, eval, recEnv, Interp.real, hkm, emmm1, ivm1R,
        iv2R] at h hn1_0 hn1_1 ⊢
    try tauto
  · simp only [rubi4110r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "c" + (env "d" * t)) *
        ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm2, sub_eq_add_neg, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4110r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4110r15Nondeg.result) =
            fun w => (((env "d" * ((env "b" * Real.sin ((env "e" + (env "f" * w))))) ^ (m)) *
            (((env "f") ^ 2 * (env "n") ^ 2))⁻¹) +
            ((((((-1) * env "b") * (env "c" + (env "d" * w))) *
            Real.cos ((env "e" + (env "f" * w)))) *
            ((env "b" * Real.sin ((env "e" + (env "f" * w))))) ^ (m - 1)) *
            ((env "f" * env "n"))⁻¹)) + (((env "b") ^ 2 * (env "n" + (-1))) * (env "n")⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4110r15Nondeg, eval, recEnv, Interp.real, hkm, emmm1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4110r15Nondeg.body =
        (env "c" + (env "d" * t)) * ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ (m) := by
      simp [rubi4110r15Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "b" * Real.sin ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "d")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (hasDerivAt_const t ((((env "f") ^ 2 * (env "n") ^ 2))⁻¹))).add (((((hasDerivAt_const t (((-1) * env "b"))).mul ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m - 1) _ (hdzm (m - 1) (by omega))) ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (hasDerivAt_const t (((env "f" * env "n"))⁻¹)))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      show m - 1 - 1 = m -
          2 by ring]
    have hn1_1c : ((m : ℤ) : ℝ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd (by norm_num) hn1_1c
    · have hdmm : (env "b" * Real.sin ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 1) =
          ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 2) *
          ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ 1 := by
        have := zsplit ((env "b" * Real.sin ((env "e" + (env "f" * t))))) (m - 2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ (m) =
          ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 2) *
          ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ 2 := by
        have := zsplit ((env "b" * Real.sin ((env "e" + (env "f" * t))))) (m - 2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ (m + 1) =
          ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 2) *
          ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ 3 := by
        have := zsplit ((env "b" * Real.sin ((env "e" + (env "f" * t))))) (m - 2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ (m + 2) =
          ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 2) *
          ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ 4 := by
        have := zsplit ((env "b" * Real.sin ((env "e" + (env "f" * t))))) (m - 2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "b" * Real.sin ((env "e" + (env "f" * t))))) ^ (m - 2) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "b"^2*env "c"*env "f"^2*Pm*((m : ℤ) : ℝ)^2 +
          env "b"^2*env "c"*env "f"^2*Pm*((m : ℤ) : ℝ) -
          env "b"^2*env "d"*env "f"^2*Pm*t*((m : ℤ) : ℝ)^2 +
          env "b"^2*env "d"*env "f"^2*Pm*t*((m : ℤ) : ℝ)) * hP

set_option maxHeartbeats 1000000 in
theorem rubi4110r15Nondeg_complex : rubi4110r15Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4110r15Nondeg.conditions rubi4110r15Nondeg.body
    rubi4110r15Nondeg.result rubi4110r15Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.var "n") (.int 2))) (.int 0)) (by simp [rubi4110r15Nondeg])
  have hn1_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc1
  have hn1_1 : env "n" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc1
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4110r15Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi4110r15Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "n" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4110r15Nondeg.body →
      (m < 0 → (env "b" * Complex.sin ((env "e" + (env "f" * w)))) ≠ 0) := by
    intro w h
    simp [rubi4110r15Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4110r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emmm2] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4110r15Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emmm1, ivm1C,
        iv2C] at h hn1_0 hn1_1 ⊢
    try tauto
  · simp only [rubi4110r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "c" + (env "d" * t)) *
        ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emmm2, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4110r15Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4110r15Nondeg.result) =
            fun w => (((env "d" * ((env "b" * Complex.sin ((env "e" + (env "f" * w))))) ^ (m)) *
            (((env "f") ^ 2 * (env "n") ^ 2))⁻¹) +
            ((((((-1) * env "b") * (env "c" + (env "d" * w))) *
            Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "b" * Complex.sin ((env "e" + (env "f" * w))))) ^ (m - 1)) *
            ((env "f" * env "n"))⁻¹)) + (((env "b") ^ 2 * (env "n" + (-1))) * (env "n")⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4110r15Nondeg, eval, recEnv, Interp.complex, hkm, emmm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4110r15Nondeg.body =
        (env "c" + (env "d" * t)) * ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m) :=
        by
      simp [rubi4110r15Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "b" * Complex.sin ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "d")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (hasDerivAt_const t ((((env "f") ^ 2 * (env "n") ^ 2))⁻¹))).add (((((hasDerivAt_const t (((-1) * env "b"))).mul ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m - 1) _ (hdzm (m - 1) (by omega))) ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (hasDerivAt_const t (((env "f" * env "n"))⁻¹)))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      show m - 1 - 1 = m -
          2 by ring]
    have hn1_1c : ((m : ℤ) : ℂ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd (by norm_num) hn1_1c
    · have hdmm : (env "b" * Complex.sin ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 1) =
          ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 2) *
          ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ 1 := by
        have := zsplit ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) (m - 2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m) =
          ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 2) *
          ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ 2 := by
        have := zsplit ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) (m - 2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m + 1) =
          ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 2) *
          ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ 3 := by
        have := zsplit ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) (m - 2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m + 2) =
          ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 2) *
          ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ 4 := by
        have := zsplit ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) (m - 2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "b" * Complex.sin ((env "e" + (env "f" * t))))) ^ (m - 2) = Pm
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "b"^2*env "c"*env "f"^2*Pm*((m : ℤ) : ℂ)^2 +
          env "b"^2*env "c"*env "f"^2*Pm*((m : ℤ) : ℂ) -
          env "b"^2*env "d"*env "f"^2*Pm*t*((m : ℤ) : ℂ)^2 +
          env "b"^2*env "d"*env "f"^2*Pm*t*((m : ℤ) : ℂ)) * hP

/-! ## rubi4112r26Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4112r26Nondeg_real : rubi4112r26Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4112r26Nondeg.conditions rubi4112r26Nondeg.body
    rubi4112r26Nondeg.result rubi4112r26Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4112r26Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4112r26Nondeg])
  have hn2 : env "m" + env "p" ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.var "m") (.var "p")) (.int 0)) (by simp [rubi4112r26Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "f") (.var "g")) (.app2 .add (.var "m") (.var "p"))) (.int 0)) (by simp [rubi4112r26Nondeg])
  have hn5_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_1 : env "g" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_2 : env "m" + env "p" ≠ 0 := by
    have h := hc5
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r26Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r26Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hb1 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi4112r26Nondeg])
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4112r26Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "g" * Real.cos ((env "e" + (env "f" * w)))) ≠ 0) := by
    intro w h
    simp [rubi4112r26Nondeg, Defined, eval, Interp.real, hkm, hkk] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emmm2, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4112r26Nondeg, Defined, eval, recEnv, Interp.real, emmm1, emk1,
        ivm1R] at h hn0 hn2 hn5_0 hn5_1 hn5_2 ⊢
    try tauto
  · simp only [rubi4112r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k) *
        ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 2)) *
        ((((env "b") ^ 2 * (env "m" + (-1))) + ((env "a") ^ 2 * (env "m" + env "p"))) +
        (((env "a" * env "b") * (((2 * env "m") + env "p") + (-1))) *
        Real.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emmm2, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4112r26Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4112r26Nondeg.result) =
            fun w => (((((-1) * env "b") *
            ((env "g" * Real.cos ((env "e" + (env "f" * w))))) ^ (k + 1)) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m - 1)) *
            (((env "f" * env "g") * (env "m" + env "p")))⁻¹) + (1 * ((env "m" + env "p"))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4112r26Nondeg, eval, recEnv, Interp.real, emmm1, emk1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4112r26Nondeg.body =
        ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k) *
        ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) := by
      simp [rubi4112r26Nondeg, eval, Interp.real, hkm, hkk]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "g" * Real.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) * env "b"))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k +
        1) _ (hdzk (k +
        1) (by omega))) ((hasDerivAt_const t (env "g")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m - 1) _ (hdzm (m - 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "f" * env "g") * (env "m" + env "p")))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right, show m - 1 - 1 =
        m - 2 by ring]
    have hn2c : ((m : ℤ) : ℝ) + ((k : ℤ) : ℝ) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn2
    have hn5_2c : ((m : ℤ) : ℝ) + ((k : ℤ) : ℝ) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn5_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 2 :=
            by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have el1m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              2) 1 hdmm
          rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
        have el2m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              2) 2 hdmm
          rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
        have el3m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              2) 3 hdmm
          rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have el4m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 4 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              2) 4 hdmm
          rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [el1m, el2m]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) = Pm
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "b"^2*Pm*((m : ℤ) : ℝ) + env "b"^2*Pm) * hP
      · have hdmm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 2 :=
          by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have el1m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              2) 1 hdmm
          rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
        have el2m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              2) 2 hdmm
          rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
        have el3m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              2) 3 hdmm
          rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have el4m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 4 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              2) 4 hdmm
          rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [el1m, el2m]
        have hdmk : (env "g" * Real.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ k =
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 1) =
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k + 2) =
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "g" * Real.cos ((env "e" + (env "f" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) = Pm
        generalize ((env "g" * Real.cos ((env "e" + (env "f" * t))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-C*env "b"^2*env "f"*env "g"*Pk*Pm*((m : ℤ) : ℝ) +
            C*env "b"^2*env "f"*env "g"*Pk*Pm) * hP

set_option maxHeartbeats 1000000 in
theorem rubi4112r26Nondeg_complex : rubi4112r26Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4112r26Nondeg.conditions rubi4112r26Nondeg.body
    rubi4112r26Nondeg.result rubi4112r26Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4112r26Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4112r26Nondeg])
  have hn2 : env "m" + env "p" ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.var "m") (.var "p")) (.int 0)) (by simp [rubi4112r26Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "f") (.var "g")) (.app2 .add (.var "m") (.var "p"))) (.int 0)) (by simp [rubi4112r26Nondeg])
  have hn5_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_1 : env "g" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_2 : env "m" + env "p" ≠ 0 := by
    have h := hc5
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r26Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r26Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
  have hb1 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi4112r26Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "p" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4112r26Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "g" * Complex.cos ((env "e" + (env "f" * w)))) ≠ 0) := by
    intro w h
    simp [rubi4112r26Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkk, emmm2, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4112r26Nondeg, Defined, eval, recEnv, Interp.complex, emmm1, emk1,
        ivm1C] at h hn0 hn2 hn5_0 hn5_1 hn5_2 ⊢
    try tauto
  · simp only [rubi4112r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k) *
        ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 2)) *
        ((((env "b") ^ 2 * (env "m" + (-1))) + ((env "a") ^ 2 * (env "m" + env "p"))) +
        (((env "a" * env "b") * (((2 * env "m") + env "p") + (-1))) *
        Complex.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkk, emmm2, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4112r26Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4112r26Nondeg.result) =
            fun w => (((((-1) * env "b") *
            ((env "g" * Complex.cos ((env "e" + (env "f" * w))))) ^ (k + 1)) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m - 1)) *
            (((env "f" * env "g") * (env "m" + env "p")))⁻¹) + (1 * ((env "m" + env "p"))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4112r26Nondeg, eval, recEnv, Interp.complex, emmm1, emk1, ivm1C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4112r26Nondeg.body =
        ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k) *
        ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) := by
      simp [rubi4112r26Nondeg, eval, Interp.complex, hkm, hkk]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "g" * Complex.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) * env "b"))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k +
        1) _ (hdzk (k +
        1) (by omega))) ((hasDerivAt_const t (env "g")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m - 1) _ (hdzm (m - 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "f" * env "g") * (env "m" + env "p")))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right, show m - 1 - 1 =
        m - 2 by ring]
    have hn2c : ((m : ℤ) : ℂ) + ((k : ℤ) : ℂ) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn2
    have hn5_2c : ((m : ℤ) : ℂ) + ((k : ℤ) : ℂ) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn5_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m -
            2 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have el1m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              2) 1 hdmm
          rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
        have el2m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              2) 2 hdmm
          rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
        have el3m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              2) 3 hdmm
          rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have el4m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 4 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              2) 4 hdmm
          rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [el1m, el2m]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) = Pm
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        have hden : ((m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
        rw [div_eq_iff hden]
        linear_combination (-env "b"^2*Pm*((m : ℤ) : ℂ) + env "b"^2*Pm) * hP
      · have hdmm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m -
          2 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have el1m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              2) 1 hdmm
          rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
        have el2m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              2) 2 hdmm
          rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
        have el3m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              2) 3 hdmm
          rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have el4m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 4 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              2) 4 hdmm
          rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [el1m, el2m]
        have hdmk : (env "g" * Complex.cos ((env "e" + (env "f" * t)))) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ k =
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 1 := by
          have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k + 1) =
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 2 := by
          have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k + 2) =
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) *
            ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ 3 := by
          have := zsplit ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 2) = Pm
        generalize ((env "g" * Complex.cos ((env "e" + (env "f" * t))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-C*env "b"^2*env "f"*env "g"*Pk*Pm*((m : ℤ) : ℂ) +
            C*env "b"^2*env "f"*env "g"*Pk*Pm) * hP

/-! ## rubi4121r50Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4121r50Nondeg_real : rubi4121r50Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r50Nondeg.conditions rubi4121r50Nondeg.body
    rubi4121r50Nondeg.result rubi4121r50Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r50Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r50Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4121r50Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn2 : (env "c") ^ 2 + ((-1) * (env "d") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4121r50Nondeg])
  have hn2v : (env "c") ^ 2 + -(env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4121r50Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.var "n"))) (.int 0)) (by simp [rubi4121r50Nondeg])
  have hn5_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_1 : env "m" + env "n" ≠ 0 := by
    have h := hc5
    simp [Cond.Holds, Defined, eval] at h
    tauto
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "d") * hza + (env "c") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "c") * hzb + (-env "d") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r50Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r50Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hb3 : 1 < k := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi4121r50Nondeg])
    have h' : (1 : ℝ) < ((k : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltk : k < 1 → k < 0 := by omega
  have hlek1 : k ≤ 1 → k < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "n" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "n" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r50Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4121r50Nondeg, Defined, eval, Interp.real, hkm, hkk] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r50Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, emmk2, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r50Nondeg, Defined, eval, recEnv, Interp.real, hkm, emmk1,
        ivm1R] at h hn0 hn2 hn5_0 hn5_1 hda hdb ⊢
    try tauto
  · simp only [rubi4121r50Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 2)) *
        (((env "d" *
        (((env "a" * env "c") * env "m") + ((env "b" * env "d") * (env "n" + (-1))))) +
        ((env "b" * (env "c") ^ 2) * (env "m" + env "n"))) +
        ((env "d" *
        (((env "a" * env "d") * env "m") +
        ((env "b" * env "c") * ((env "m" + (2 * env "n")) + (-1))))) *
        Real.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, emmk2, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4121r50Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r50Nondeg.result) =
            fun w => ((((((-1) * env "d") * Real.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w)))))) ^ (k - 1)) *
            ((env "f" * (env "m" + env "n")))⁻¹) + (1 * ((env "b" * (env "m" + env "n")))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4121r50Nondeg, eval, recEnv, Interp.real, hkm, emmk1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r50Nondeg.body =
        ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k) := by
      simp [rubi4121r50Nondeg, eval, Interp.real, hkm, hkk]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "d"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k - 1) _ (hdzk (k - 1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((env "f" * (env "m" + env "n")))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, show k - 1 - 1 = k - 2 by ring]
    have hn5_1c : ((m : ℤ) : ℝ) + ((k : ℤ) : ℝ) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn5_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb3 (by omega)
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 2 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have el1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              2) 1 hdmk
          rwa [show k - 2 + ((1 : ℕ) : ℤ) = k - 1 by push_cast; ring] at this
        have el2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              2) 2 hdmk
          rwa [show k - 2 + ((2 : ℕ) : ℤ) = k by push_cast; ring] at this
        have el3k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              2) 3 hdmk
          rwa [show k - 2 + ((3 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have el4k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 4 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              2) 4 hdmk
          rwa [show k - 2 + ((4 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [el1k, el2k]
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "d"^2*Pk*((k : ℤ) : ℝ) + env "d"^2*Pk) * hP + (0) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb3 (by omega)
      · have hdmm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 :=
          by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ m =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 2 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have el1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              2) 1 hdmk
          rwa [show k - 2 + ((1 : ℕ) : ℤ) = k - 1 by push_cast; ring] at this
        have el2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              2) 2 hdmk
          rwa [show k - 2 + ((2 : ℕ) : ℤ) = k by push_cast; ring] at this
        have el3k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              2) 3 hdmk
          rwa [show k - 2 + ((3 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have el4k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 4 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              2) 4 hdmk
          rwa [show k - 2 + ((4 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [el1k, el2k]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "a"*env "b"*env "d"^2*env "f"*Pk*Pm*((k : ℤ) : ℝ) +
            env "a"*env "b"*env "d"^2*env "f"*Pk*Pm -
            env "b"^2*env "c"*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) -
            env "b"^2*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) -
            env "b"^2*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) +
            env "b"^2*env "d"^2*env "f"*Pk*Pm*S) * hP +
            (env "c"*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) +
            env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ)) * hr1

set_option maxHeartbeats 1000000 in
theorem rubi4121r50Nondeg_complex : rubi4121r50Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r50Nondeg.conditions rubi4121r50Nondeg.body
    rubi4121r50Nondeg.result rubi4121r50Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r50Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4121r50Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4121r50Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hn2 : (env "c") ^ 2 + ((-1) * (env "d") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4121r50Nondeg])
  have hn2v : (env "c") ^ 2 + -(env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4121r50Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.var "n"))) (.int 0)) (by simp [rubi4121r50Nondeg])
  have hn5_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_1 : env "m" + env "n" ≠ 0 := by
    have h := hc5
    simp [Cond.Holds, Defined, eval] at h
    tauto
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (-env "d") * hza + (env "c") * hzb)
  have hdb : env "b" ≠ 0 := by
    intro hzb
    have hza : env "a" = 0 := by
      have h2 : env "a" ^ 2 = 0 := by linear_combination (1) * hr1 - (-env "b") * hzb
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn0 (by linear_combination (env "c") * hzb + (-env "d") * hza)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r50Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r50Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
  have hb3 : 1 < k := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi4121r50Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkk, Complex.ext_iff] at h
    have h' : (1 : ℝ) < ((k : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltk : k < 1 → k < 0 := by omega
  have hlek1 : k ≤ 1 → k < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "n" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "n" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "n" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "n" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r50Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4121r50Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r50Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, emmk2, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r50Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emmk1,
        ivm1C] at h hn0 hn2 hn5_0 hn5_1 hda hdb ⊢
    try tauto
  · simp only [rubi4121r50Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 2)) *
        (((env "d" *
        (((env "a" * env "c") * env "m") + ((env "b" * env "d") * (env "n" + (-1))))) +
        ((env "b" * (env "c") ^ 2) * (env "m" + env "n"))) +
        ((env "d" *
        (((env "a" * env "d") * env "m") +
        ((env "b" * env "c") * ((env "m" + (2 * env "n")) + (-1))))) *
        Complex.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, emmk2, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4121r50Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4121r50Nondeg.result) =
            fun w => ((((((-1) * env "d") * Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (k - 1)) *
            ((env "f" * (env "m" + env "n")))⁻¹) + (1 * ((env "b" * (env "m" + env "n")))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4121r50Nondeg, eval, recEnv, Interp.complex, hkm, emmk1, ivm1C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r50Nondeg.body =
        ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k) := by
      simp [rubi4121r50Nondeg, eval, Interp.complex, hkm, hkk]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "d"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k - 1) _ (hdzk (k - 1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((env "f" * (env "m" + env "n")))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, show k - 1 - 1 = k - 2 by ring]
    have hn5_1c : ((m : ℤ) : ℂ) + ((k : ℤ) : ℂ) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn5_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb3 (by omega)
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k -
            2 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have el1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              2) 1 hdmk
          rwa [show k - 2 + ((1 : ℕ) : ℤ) = k - 1 by push_cast; ring] at this
        have el2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              2) 2 hdmk
          rwa [show k - 2 + ((2 : ℕ) : ℤ) = k by push_cast; ring] at this
        have el3k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              2) 3 hdmk
          rwa [show k - 2 + ((3 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have el4k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 4 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              2) 4 hdmk
          rwa [show k - 2 + ((4 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [el1k, el2k]
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        have hden : ((k : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
        rw [div_eq_iff hden]
        linear_combination (-env "d"^2*Pk*((k : ℤ) : ℂ) + env "d"^2*Pk) * hP + (0) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb3 (by omega)
      · have hdmm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m -
          1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ m =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
              1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m]
        have hdmk : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k -
            2 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have el1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              2) 1 hdmk
          rwa [show k - 2 + ((1 : ℕ) : ℤ) = k - 1 by push_cast; ring] at this
        have el2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              2) 2 hdmk
          rwa [show k - 2 + ((2 : ℕ) : ℤ) = k by push_cast; ring] at this
        have el3k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              2) 3 hdmk
          rwa [show k - 2 + ((3 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have el4k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 4 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              2) 4 hdmk
          rwa [show k - 2 + ((4 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [el1k, el2k]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 2) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "a"*env "b"*env "d"^2*env "f"*Pk*Pm*((k : ℤ) : ℂ) +
            env "a"*env "b"*env "d"^2*env "f"*Pk*Pm -
            env "b"^2*env "c"*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℂ) -
            env "b"^2*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) -
            env "b"^2*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) +
            env "b"^2*env "d"^2*env "f"*Pk*Pm*S) * hP +
            (env "c"*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℂ) +
            env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ)) * hr1

/-! ## rubi416r9Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi416r9Nondeg_real : rubi416r9Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r9Nondeg.conditions rubi416r9Nondeg.body
    rubi416r9Nondeg.result rubi416r9Nondeg.integrals
  intro env hc t hF
  have hn0 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r9Nondeg])
  have hn0v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r9Nondeg])
  have hc2 := hc (.ne (.app2 .mul (.var "e") (.var "n")) (.int 0)) (by simp [rubi416r9Nondeg])
  have hn2_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "n" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r9Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb1 : 1 < m := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi416r9Nondeg])
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "n" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r9Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r9Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm2, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r9Nondeg, Defined, eval, recEnv, Interp.real, emmm1, ivm1R] at h hn0 hn2_0 hn2_1 ⊢
    try tauto
  · simp only [rubi416r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((((env "n" * (env "a") ^ 2) +
        ((env "n" + (-1)) * ((env "b") ^ 2 + (env "c") ^ 2))) +
        (((env "a" * env "b") * ((2 * env "n") + (-1))) * Real.cos ((env "d" + (env "e" * t))))) +
        (((env "a" * env "c") * ((2 * env "n") + (-1))) * Real.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm2, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi416r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r9Nondeg.result) =
            fun w => ((((-1) *
            ((env "c" * Real.cos ((env "d" + (env "e" * w)))) +
            (((-1) * env "b") * Real.sin ((env "d" + (env "e" * w)))))) *
            (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m - 1)) *
            ((env "e" * env "n"))⁻¹) + (1 * (env "n")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi416r9Nondeg, eval, recEnv, Interp.real, emmm1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r9Nondeg.body =
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r9Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul (((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).add ((hasDerivAt_const t (((-1) * env "b"))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m - 1) _ (hdzm (m - 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((env "e" * env "n"))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      show m - 1 - 1 = m -
          2 by ring]
    have hn2_1c : ((m : ℤ) : ℝ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd (by norm_num) hn2_1c
    · have hdmm : ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 2) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 2) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 2) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 2) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 4 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 2) = Pm
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "b"^2*env "e"*Pm*((m : ℤ) : ℝ) + env "b"^2*env "e"*Pm -
          env "c"^2*env "e"*Pm*((m : ℤ) : ℝ) + env "c"^2*env "e"*Pm) * hP

set_option maxHeartbeats 1000000 in
theorem rubi416r9Nondeg_complex : rubi416r9Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi416r9Nondeg.conditions rubi416r9Nondeg.body
    rubi416r9Nondeg.result rubi416r9Nondeg.integrals
  intro env hc t hF
  have hn0 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r9Nondeg])
  have hn0v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r9Nondeg])
  have hc2 := hc (.ne (.app2 .mul (.var "e") (.var "n")) (.int 0)) (by simp [rubi416r9Nondeg])
  have hn2_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "n" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r9Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb1 : 1 < m := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi416r9Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "n" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r9Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r9Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r9Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emmm2, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r9Nondeg, Defined, eval, recEnv, Interp.complex, emmm1,
        ivm1C] at h hn0 hn2_0 hn2_1 ⊢
    try tauto
  · simp only [rubi416r9Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((((env "n" * (env "a") ^ 2) +
        ((env "n" + (-1)) * ((env "b") ^ 2 + (env "c") ^ 2))) +
        (((env "a" * env "b") * ((2 * env "n") + (-1))) *
        Complex.cos ((env "d" + (env "e" * t))))) +
        (((env "a" * env "c") * ((2 * env "n") + (-1))) *
        Complex.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emmm2, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi416r9Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r9Nondeg.result) =
            fun w => ((((-1) *
            ((env "c" * Complex.cos ((env "d" + (env "e" * w)))) +
            (((-1) * env "b") * Complex.sin ((env "d" + (env "e" * w)))))) *
            (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m - 1)) *
            ((env "e" * env "n"))⁻¹) + (1 * (env "n")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi416r9Nondeg, eval, recEnv, Interp.complex, emmm1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r9Nondeg.body =
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r9Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul (((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).add ((hasDerivAt_const t (((-1) * env "b"))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m - 1) _ (hdzm (m - 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((env "e" * env "n"))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      show m - 1 - 1 = m -
          2 by ring]
    have hn2_1c : ((m : ℤ) : ℂ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd (by norm_num) hn2_1c
    · have hdmm : ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 2) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 2) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 2) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 2) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 4 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 2) = Pm
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "b"^2*env "e"*Pm*((m : ℤ) : ℂ) + env "b"^2*env "e"*Pm -
          env "c"^2*env "e"*Pm*((m : ℤ) : ℂ) + env "c"^2*env "e"*Pm) * hP

/-! ## rubi417r11Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi417r11Nondeg_real : rubi417r11Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi417r11Nondeg.conditions rubi417r11Nondeg.body
    rubi417r11Nondeg.result rubi417r11Nondeg.integrals
  intro env hc t hF
  have hn0 : env "a" + env "b" ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.var "a") (.var "b")) (.int 0)) (by simp [rubi417r11Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.var "p")) (.int 0)) (by simp [rubi417r11Nondeg])
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "p" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi417r11Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb1 : 1 < m := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi417r11Nondeg])
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "p" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi417r11Nondeg.body →
      (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w)))) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi417r11Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi417r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm2, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi417r11Nondeg, Defined, eval, recEnv, Interp.real, emmm1, ivm1R,
        iv2R] at h hn0 hn2_1 hn2_2 ⊢
    try tauto
  · simp only [rubi417r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 2) *
        ((env "a" * (env "b" + ((2 * env "a") * env "p"))) +
        (((env "b" * ((2 * env "a") + env "b")) * ((2 * env "p") + (-1))) *
        (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm2, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi417r11Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi417r11Nondeg.result) =
            fun w => ((((((-1) * env "b") * Real.cos ((env "e" + (env "f" * w)))) *
            Real.sin ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w)))) ^ 2))) ^ (m - 1)) *
            (((2 * env "f") * env "p"))⁻¹) + (1 * ((2 * env "p"))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi417r11Nondeg, eval, recEnv, Interp.real, emmm1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi417r11Nondeg.body =
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m) := by
      simp [rubi417r11Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "b"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m - 1) _ (hdzm (m - 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).pow 2))))).mul (hasDerivAt_const t ((((2 * env "f") * env "p"))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      show m - 1 - 1 = m -
          2 by ring]
    have hn2_2c : ((m : ℤ) : ℝ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd (by norm_num) hn2_2c
    · have hdmm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ m -
        2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 2) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 2) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 2) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 2) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 4 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 2) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "a"*env "b"*env "f"*Pm - 2*env "b"^2*env "f"*Pm*S^2*((m : ℤ) : ℝ) +
          env "b"^2*env "f"*Pm*S^2) * hP

set_option maxHeartbeats 1000000 in
theorem rubi417r11Nondeg_complex : rubi417r11Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi417r11Nondeg.conditions rubi417r11Nondeg.body
    rubi417r11Nondeg.result rubi417r11Nondeg.integrals
  intro env hc t hF
  have hn0 : env "a" + env "b" ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.var "a") (.var "b")) (.int 0)) (by simp [rubi417r11Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.var "p")) (.int 0)) (by simp [rubi417r11Nondeg])
  have hn2_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "p" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi417r11Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb1 : 1 < m := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi417r11Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "p" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "p" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "p" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "p" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi417r11Nondeg.body →
      (m < 0 → (env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * w)))) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi417r11Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi417r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emmm2, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi417r11Nondeg, Defined, eval, recEnv, Interp.complex, emmm1, ivm1C,
        iv2C] at h hn0 hn2_1 hn2_2 ⊢
    try tauto
  · simp only [rubi417r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 2) *
        ((env "a" * (env "b" + ((2 * env "a") * env "p"))) +
        (((env "b" * ((2 * env "a") + env "b")) * ((2 * env "p") + (-1))) *
        (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emmm2, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi417r11Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi417r11Nondeg.result) =
            fun w => ((((((-1) * env "b") * Complex.cos ((env "e" + (env "f" * w)))) *
            Complex.sin ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * w)))) ^ 2))) ^ (m - 1)) *
            (((2 * env "f") * env "p"))⁻¹) + (1 * ((2 * env "p"))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi417r11Nondeg, eval, recEnv, Interp.complex, emmm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi417r11Nondeg.body =
        ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m) := by
      simp [rubi417r11Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "b"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m - 1) _ (hdzm (m - 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).pow 2))))).mul (hasDerivAt_const t ((((2 * env "f") * env "p"))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      show m - 1 - 1 = m -
          2 by ring]
    have hn2_2c : ((m : ℤ) : ℂ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd (by norm_num) hn2_2c
    · have hdmm : (env "a" +
        (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m -
          1) = ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 2) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m) =
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 2) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m +
          1) = ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 2) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m +
          2) = ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 2) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 4 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m -
          2) = Pm
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "a"*env "b"*env "f"*Pm - 2*env "b"^2*env "f"*Pm*S^2*((m : ℤ) : ℂ) +
          env "b"^2*env "f"*Pm*S^2) * hP

/-! ## rubi4514r3Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4514r3Nondeg_real : rubi4514r3Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4514r3Nondeg.conditions rubi4514r3Nondeg.body
    rubi4514r3Nondeg.result rubi4514r3Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "m")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.int 0)) (by simp [rubi4514r3Nondeg])
  have hn1_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_1 : env "m" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_2 : env "m" + (-1) ≠ 0 := by
    have h := hc1
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4514r3Nondeg, Defined, eval, Interp.real, hkm, Real.cot_eq_cos_div_sin] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi4514r3Nondeg])
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4514r3Nondeg.body →
      Real.sin (env "c" + env "d" * w) ≠ 0 ∧
          (m < 0 →
          (env "e" *
          (Real.cos ((env "c" + (env "d" * w))) / Real.sin ((env "c" + (env "d" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4514r3Nondeg, Defined, eval, Interp.real, hkm, Real.cot_eq_cos_div_sin] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4514r3Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm2, Real.cot_eq_cos_div_sin] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4514r3Nondeg, Defined, eval, recEnv, Interp.real, emmm1, ivm1R, iv2R,
        Real.cot_eq_cos_div_sin] at h hn1_0 hn1_1 hn1_2 ⊢
    try tauto
  · simp only [rubi4514r3Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "e" *
        (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ (m - 2) *
        ((env "a" * env "m") +
        ((env "b" * (env "m" + (-1))) * (Real.sin ((env "c" + (env "d" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm2, Fn.csc, Real.cot_eq_cos_div_sin, sub_eq_add_neg,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4514r3Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4514r3Nondeg.result) =
            fun w => (((((-1) * env "e") *
            ((env "e" *
            (Real.cos ((env "c" + (env "d" * w))) / Real.sin ((env "c" + (env "d" * w)))))) ^ (m -
            1)) * ((env "a" * env "m") +
            ((env "b" * (env "m" + (-1))) * (Real.sin ((env "c" + (env "d" * w))))⁻¹))) *
            (((env "d" * env "m") * (env "m" + (-1))))⁻¹) +
            (((-1) * (env "e") ^ 2) * (env "m")⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4514r3Nondeg, eval, recEnv, Interp.real, emmm1, ivm1R, iv2R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4514r3Nondeg.body =
        ((env "e" *
        (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ (m) *
        (env "a" + (env "b" * (Real.sin ((env "c" + (env "d" * t))))⁻¹)) := by
      simp [rubi4514r3Nondeg, eval, Interp.real, hkm, Fn.csc, Real.cot_eq_cos_div_sin]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "e" *
        (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" +
        (env "d" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) * env "e"))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "e")).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))) hs0)))).mul ((hasDerivAt_const t ((env "a" * env "m"))).add ((hasDerivAt_const t ((env "b" * (env "m" + (-1))))).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))).inv hs0)))).mul (hasDerivAt_const t ((((env "d" * env "m") * (env "m" + (-1))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,

      show m - 1 - 1 = m -
          2 by ring]
    have hn1_1c : ((m : ℤ) : ℝ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_1
    have hn1_2c : ((m : ℤ) : ℝ) + (-1) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd (by norm_num) hn1_1c
    · have hdmm : (env "e" *
        (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" +
        (env "d" * t))))) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ (m -
          1) = ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ (m -
          2) * ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ 1 := by
        have := zsplit ((env "e" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) (m -
            2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ (m) =
          ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ (m -
          2) * ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ 2 := by
        have := zsplit ((env "e" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) (m -
            2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ (m +
          1) = ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ (m -
          2) * ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ 3 := by
        have := zsplit ((env "e" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) (m -
            2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ (m +
          2) = ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ (m -
          2) * ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ 4 := by
        have := zsplit ((env "e" *
            (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) (m -
            2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "e" *
          (Real.cos ((env "c" + (env "d" * t))) / Real.sin ((env "c" + (env "d" * t)))))) ^ (m -
          2) = Pm
      generalize Real.sin (env "c" + env "d" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "c" + env "d" * t) = C at hP ⊢
      field_simp
      ring

/-! ## rubi6113r11Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi6113r11Nondeg_real : rubi6113r11Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6113r11Nondeg.conditions rubi6113r11Nondeg.body
    rubi6113r11Nondeg.result rubi6113r11Nondeg.integrals
  intro env hc t hF
  have hr1 : (env "b" * env "e") + (((-2) * env "c") * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r11Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc2 := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r11Nondeg])
  have hn2_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r11Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi6113r11Nondeg])
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6113r11Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r11Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm2, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r11Nondeg, Defined, eval, recEnv, Interp.real, emmm1, ivm1R, iv2R] at h hn2_1 ⊢
    try tauto
  · simp only [rubi6113r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m - 2) *
        Real.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm2, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6113r11Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r11Nondeg.result) =
            fun w => (((env "e" * ((env "d" + (env "e" * w))) ^ (m - 1)) *
            Real.cosh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) * ((2 * env "c"))⁻¹) +
            ((((-1) * (env "e") ^ 2) * (env "m" + (-1))) * ((2 * env "c"))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi6113r11Nondeg, eval, recEnv, Interp.real, emmm1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi6113r11Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Real.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r11Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "e")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul ((Real.hasDerivAt_cosh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((2 * env "c"))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      show m - 1 - 1 = m -
          2 by ring]
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "d" + (env "e" * t))) ^ (m - 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "d" + (env "e" * t))) ^ (m) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 4 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 2) = Pm
      generalize Real.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Real.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      field_simp
      linear_combination (0) * hP + (env "d"*Pm*S + env "e"*Pm*S*t) * hr1

set_option maxHeartbeats 1000000 in
theorem rubi6113r11Nondeg_complex : rubi6113r11Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6113r11Nondeg.conditions rubi6113r11Nondeg.body
    rubi6113r11Nondeg.result rubi6113r11Nondeg.integrals
  intro env hc t hF
  have hr1 : (env "b" * env "e") + (((-2) * env "c") * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r11Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc2 := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r11Nondeg])
  have hn2_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r11Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi6113r11Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi6113r11Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r11Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emmm2, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r11Nondeg, Defined, eval, recEnv, Interp.complex, emmm1, ivm1C, iv2C] at h hn2_1 ⊢
    try tauto
  · simp only [rubi6113r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m - 2) *
        Complex.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emmm2, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6113r11Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r11Nondeg.result) =
            fun w => (((env "e" * ((env "d" + (env "e" * w))) ^ (m - 1)) *
            Complex.cosh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) *
            ((2 * env "c"))⁻¹) +
            ((((-1) * (env "e") ^ 2) * (env "m" + (-1))) * ((2 * env "c"))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi6113r11Nondeg, eval, recEnv, Interp.complex, emmm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi6113r11Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Complex.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r11Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "e")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul ((Complex.hasDerivAt_cosh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((2 * env "c"))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      show m - 1 - 1 = m -
          2 by ring]
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "d" + (env "e" * t))) ^ (m - 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "d" + (env "e" * t))) ^ (m) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 4 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 2) = Pm
      generalize Complex.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Complex.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      field_simp
      linear_combination (0) * hP + (env "d"*Pm*S + env "e"*Pm*S*t) * hr1

/-! ## rubi6113r12Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi6113r12Nondeg_real : rubi6113r12Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6113r12Nondeg.conditions rubi6113r12Nondeg.body
    rubi6113r12Nondeg.result rubi6113r12Nondeg.integrals
  intro env hc t hF
  have hr1 : (env "b" * env "e") + (((-2) * env "c") * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r12Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc2 := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r12Nondeg])
  have hn2_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r12Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi6113r12Nondeg])
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6113r12Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r12Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm2, iv2R] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r12Nondeg, Defined, eval, recEnv, Interp.real, emmm1, ivm1R, iv2R] at h hn2_1 ⊢
    try tauto
  · simp only [rubi6113r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m - 2) *
        Real.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm2, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6113r12Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r12Nondeg.result) =
            fun w => (((env "e" * ((env "d" + (env "e" * w))) ^ (m - 1)) *
            Real.sinh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) * ((2 * env "c"))⁻¹) +
            ((((-1) * (env "e") ^ 2) * (env "m" + (-1))) * ((2 * env "c"))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi6113r12Nondeg, eval, recEnv, Interp.real, emmm1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi6113r12Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Real.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r12Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "e")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul ((Real.hasDerivAt_sinh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((2 * env "c"))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      show m - 1 - 1 = m -
          2 by ring]
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "d" + (env "e" * t))) ^ (m - 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "d" + (env "e" * t))) ^ (m) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 4 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 2) = Pm
      generalize Real.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Real.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      field_simp
      linear_combination (0) * hP + (C*env "d"*Pm + C*env "e"*Pm*t) * hr1

set_option maxHeartbeats 1000000 in
theorem rubi6113r12Nondeg_complex : rubi6113r12Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6113r12Nondeg.conditions rubi6113r12Nondeg.body
    rubi6113r12Nondeg.result rubi6113r12Nondeg.integrals
  intro env hc t hF
  have hr1 : (env "b" * env "e") + (((-2) * env "c") * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)) (by simp [rubi6113r12Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc2 := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [rubi6113r12Nondeg])
  have hn2_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi6113r12Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb0 : 1 < m := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi6113r12Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (1 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hlem1 : m ≤ 1 → m < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm2 : intValue? (env "m" + -2) = some (m - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi6113r12Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) := by
    intro w h
    simp [rubi6113r12Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    try tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emmm2, iv2C] at h ⊢
    try tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi6113r12Nondeg, Defined, eval, recEnv, Interp.complex, emmm1, ivm1C, iv2C] at h hn2_1 ⊢
    try tauto
  · simp only [rubi6113r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m - 2) *
        Complex.sinh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emmm2, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6113r12Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi6113r12Nondeg.result) =
            fun w => (((env "e" * ((env "d" + (env "e" * w))) ^ (m - 1)) *
            Complex.sinh (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)))) *
            ((2 * env "c"))⁻¹) +
            ((((-1) * (env "e") ^ 2) * (env "m" + (-1))) * ((2 * env "c"))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi6113r12Nondeg, eval, recEnv, Interp.complex, emmm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi6113r12Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        Complex.cosh (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) := by
      simp [rubi6113r12Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (env "e")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m -
        1) _ (hdzm (m -
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul ((Complex.hasDerivAt_sinh _).comp t (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((2 * env "c"))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      show m - 1 - 1 = m -
          2 by ring]
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.cosh_sq_sub_sinh_sq ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ m - 2 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have el1m : ((env "d" + (env "e" * t))) ^ (m - 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 1 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 1 hdmm
        rwa [show m - 2 + ((1 : ℕ) : ℤ) = m - 1 by push_cast; ring] at this
      have el2m : ((env "d" + (env "e" * t))) ^ (m) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 2 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 2 hdmm
        rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring] at this
      have el3m : ((env "d" + (env "e" * t))) ^ (m + 1) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 3 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 3 hdmm
        rwa [show m - 2 + ((3 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have el4m : ((env "d" + (env "e" * t))) ^ (m + 2) = ((env "d" + (env "e" * t))) ^ (m - 2) *
          ((env "d" + (env "e" * t))) ^ 4 := by
        have := zsplit ((env "d" + (env "e" * t))) (m - 2) 4 hdmm
        rwa [show m - 2 + ((4 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [el1m, el2m]
      generalize ((env "d" + (env "e" * t))) ^ (m - 2) = Pm
      generalize Complex.sinh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = S at hP ⊢
      generalize Complex.cosh ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) = C at hP ⊢
      field_simp
      linear_combination (0) * hP + (C*env "d"*Pm + C*env "e"*Pm*t) * hr1

end OSR.IntegrationRec298
