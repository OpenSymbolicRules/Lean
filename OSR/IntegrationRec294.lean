import OSR.IntegrationNum1

/-! # Strengthened variants with two integer exponents: explicit terms plus a residual integral

Proofs of RUBI rules whose result is an explicit term with powers `y^m z^n` plus at most one residual
integral. The derivative of the explicit term is built from the rule expression; the integrand is
recovered with `sin² + cos² = 1` (when trigonometric) and the stated parameter relations, separately
for each exponent equal to `0` or not (`linear_combination` coefficients computed by Gröbner
reduction). Rules with `csc`, `cot` or `arctan` are proved over ℝ only. -/

namespace OSR.IntegrationRec294

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

/-! ## rubi1213r27Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1213r27Nondeg_real : rubi1213r27Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1213r27Nondeg.conditions rubi1213r27Nondeg.body
    rubi1213r27Nondeg.result rubi1213r27Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "c" * (env "d") ^ 2) + (env "a" * (env "e") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r27Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1213r27Nondeg])
  have hn3_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_3 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r27Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r27Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have hb1 : k < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1213r27Nondeg])
    have h' : ((k : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hb2 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi1213r27Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hltk : k < 1 → k < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1213r27Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧ (k < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r27Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm1, emk1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r27Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        iv2R] at h hn3_1 hn3_2 hn3_3 ⊢
    tauto
  · simp only [rubi1213r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m - 1) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (k + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm1, emk1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1213r27Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r27Nondeg.result) =
            fun w => (((((env "d" * env "g") + (env "e" * env "f")) *
            ((env "d" + (env "e" * w))) ^ (m)) * ((env "a" + (env "c" * (w) ^ 2))) ^ (k + 1)) *
            ((((2 * env "c") * env "d") * (env "p" + 1)))⁻¹) +
            ((((-1) * env "e") *
            ((env "m" * ((env "d" * env "g") + (env "e" * env "f"))) +
            (((2 * env "e") * env "f") * (env "p" + 1)))) *
            ((((2 * env "c") * env "d") * (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1213r27Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1213r27Nondeg.body =
        (((env "d" + (env "e" * t))) ^ (m) * (env "f" + (env "g" * t))) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1213r27Nondeg, eval, Interp.real, hkm, hkk, iv2R]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) → (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((env "d" * env "g") +
        (env "e" *
        env "f")))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((((2 * env "c") * env "d") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn3_3c : ((k : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_3
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb2 (by omega)
      · subst hm0
        exact absurd hb2 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb1 (by omega)
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
        simp only [e0m]
        have hdmk : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "a" + (env "c" * (t) ^ 2))) ^ k =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "a" + (env "c" * (t) ^ 2))) ^ (k + 1) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "a" + (env "c" * (t) ^ 2))) ^ (k + 2) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        linear_combination (-2*env "a"*env "f"*Pk*Pm*((k : ℤ) : ℝ) - 2*env "a"*env "f"*Pk*Pm -
            2*env "c"*env "f"*Pk*Pm*t^2*((k : ℤ) : ℝ) - 2*env "c"*env "f"*Pk*Pm*t^2) * hr0

set_option maxHeartbeats 1000000 in
theorem rubi1213r27Nondeg_complex : rubi1213r27Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1213r27Nondeg.conditions rubi1213r27Nondeg.body
    rubi1213r27Nondeg.result rubi1213r27Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "c" * (env "d") ^ 2) + (env "a" * (env "e") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r27Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1213r27Nondeg])
  have hn3_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_3 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r27Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r27Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have hb1 : k < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1213r27Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkk, Complex.ext_iff] at h
    have h' : ((k : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hb2 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi1213r27Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hltk : k < 1 → k < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1213r27Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧ (k < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r27Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emmm1, emk1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r27Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emk1, ivm1C,
        iv2C] at h hn3_1 hn3_2 hn3_3 ⊢
    tauto
  · simp only [rubi1213r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m - 1) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (k + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emmm1, emk1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1213r27Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r27Nondeg.result) =
            fun w => (((((env "d" * env "g") + (env "e" * env "f")) *
            ((env "d" + (env "e" * w))) ^ (m)) * ((env "a" + (env "c" * (w) ^ 2))) ^ (k + 1)) *
            ((((2 * env "c") * env "d") * (env "p" + 1)))⁻¹) +
            ((((-1) * env "e") *
            ((env "m" * ((env "d" * env "g") + (env "e" * env "f"))) +
            (((2 * env "e") * env "f") * (env "p" + 1)))) *
            ((((2 * env "c") * env "d") * (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1213r27Nondeg, eval, recEnv, Interp.complex, hkm, emk1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1213r27Nondeg.body =
        (((env "d" + (env "e" * t))) ^ (m) * (env "f" + (env "g" * t))) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1213r27Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) → (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((env "d" * env "g") +
        (env "e" *
        env "f")))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((((2 * env "c") * env "d") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn3_3c : ((k : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_3
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb2 (by omega)
      · subst hm0
        exact absurd hb2 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb1 (by omega)
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
        simp only [e0m]
        have hdmk : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "a" + (env "c" * (t) ^ 2))) ^ k =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "a" + (env "c" * (t) ^ 2))) ^ (k + 1) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "a" + (env "c" * (t) ^ 2))) ^ (k + 2) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        linear_combination (-2*env "a"*env "f"*Pk*Pm*((k : ℤ) : ℂ) - 2*env "a"*env "f"*Pk*Pm -
            2*env "c"*env "f"*Pk*Pm*t^2*((k : ℤ) : ℂ) - 2*env "c"*env "f"*Pk*Pm*t^2) * hr0

/-! ## rubi1213r59Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1213r59Nondeg_real : rubi1213r59Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1213r59Nondeg.conditions rubi1213r59Nondeg.body
    rubi1213r59Nondeg.result rubi1213r59Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "c" * (env "d") ^ 2) + (env "a" * (env "e") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r59Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1213r59Nondeg])
  have hn5_1 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_2 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_3 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r59Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r59Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have hb1 : k < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1213r59Nondeg])
    have h' : ((k : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hb2 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi1213r59Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hltk : k < 1 → k < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1213r59Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧ (k < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r59Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r59Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm1, emk1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r59Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        iv2R] at h hn0 hn5_1 hn5_2 hn5_3 ⊢
    tauto
  · simp only [rubi1213r59Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "d" + (env "e" * t))) ^ (m - 1) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (k + 1)) *
        (((((env "a" * env "e") * env "g") * env "m") +
        (((((-1) * env "c") * env "d") * env "f") * ((2 * env "p") + 3))) +
        ((((((-1) * env "c") * env "e") * env "f") * ((env "m" + (2 * env "p")) + 3)) * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm1, emk1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1213r59Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r59Nondeg.result) =
            fun w => (((((env "d" + (env "e" * w))) ^ (m) *
            ((env "a" + (env "c" * (w) ^ 2))) ^ (k + 1)) *
            ((env "a" * env "g") + ((((-1) * env "c") * env "f") * w))) *
            ((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹) +
            ((-1) * ((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1213r59Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1213r59Nondeg.body =
        (((env "d" + (env "e" * t))) ^ (m) * (env "f" + (env "g" * t))) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1213r59Nondeg, eval, Interp.real, hkm, hkk, iv2R]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) → (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul ((hasDerivAt_const t ((env "a" * env "g"))).add ((hasDerivAt_const t ((((-1) * env "c") * env "f"))).mul (hasDerivAt_id' t)))).mul (hasDerivAt_const t (((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn5_3c : ((k : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn5_3
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb2 (by omega)
      · subst hm0
        exact absurd hb2 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb1 (by omega)
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
        simp only [e0m]
        have hdmk : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "a" + (env "c" * (t) ^ 2))) ^ k =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "a" + (env "c" * (t) ^ 2))) ^ (k + 1) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "a" + (env "c" * (t) ^ 2))) ^ (k + 2) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        ring

set_option maxHeartbeats 1000000 in
theorem rubi1213r59Nondeg_complex : rubi1213r59Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1213r59Nondeg.conditions rubi1213r59Nondeg.body
    rubi1213r59Nondeg.result rubi1213r59Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "c" * (env "d") ^ 2) + (env "a" * (env "e") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r59Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1213r59Nondeg])
  have hn5_1 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_2 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_3 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r59Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r59Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have hb1 : k < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1213r59Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkk, Complex.ext_iff] at h
    have h' : ((k : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hb2 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi1213r59Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hltk : k < 1 → k < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1213r59Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧ (k < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r59Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r59Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emmm1, emk1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r59Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emk1, ivm1C,
        iv2C] at h hn0 hn5_1 hn5_2 hn5_3 ⊢
    tauto
  · simp only [rubi1213r59Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "d" + (env "e" * t))) ^ (m - 1) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (k + 1)) *
        (((((env "a" * env "e") * env "g") * env "m") +
        (((((-1) * env "c") * env "d") * env "f") * ((2 * env "p") + 3))) +
        ((((((-1) * env "c") * env "e") * env "f") * ((env "m" + (2 * env "p")) + 3)) * t))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emmm1, emk1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1213r59Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r59Nondeg.result) =
            fun w => (((((env "d" + (env "e" * w))) ^ (m) *
            ((env "a" + (env "c" * (w) ^ 2))) ^ (k + 1)) *
            ((env "a" * env "g") + ((((-1) * env "c") * env "f") * w))) *
            ((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹) +
            ((-1) * ((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1213r59Nondeg, eval, recEnv, Interp.complex, hkm, emk1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1213r59Nondeg.body =
        (((env "d" + (env "e" * t))) ^ (m) * (env "f" + (env "g" * t))) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1213r59Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "d" + (env "e" * t)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) → (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul ((hasDerivAt_const t ((env "a" * env "g"))).add ((hasDerivAt_const t ((((-1) * env "c") * env "f"))).mul (hasDerivAt_id' t)))).mul (hasDerivAt_const t (((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn5_3c : ((k : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn5_3
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb2 (by omega)
      · subst hm0
        exact absurd hb2 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb1 (by omega)
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
        simp only [e0m]
        have hdmk : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "a" + (env "c" * (t) ^ 2))) ^ k =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "a" + (env "c" * (t) ^ 2))) ^ (k + 1) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "a" + (env "c" * (t) ^ 2))) ^ (k + 2) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        ring

/-! ## rubi1213r6Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1213r6Nondeg_real : rubi1213r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1213r6Nondeg.conditions rubi1213r6Nondeg.body
    rubi1213r6Nondeg.result rubi1213r6Nondeg.integrals
  intro env hc t hF
  have hr0 : ((2 * env "c") * env "f") + (((-1) * env "b") * env "g") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))) (.int 0)) (by simp [rubi1213r6Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1213r6Nondeg])
  have hn3_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r6Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r6Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have hb1 : k < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1213r6Nondeg])
    have h' : ((k : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hb2 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi1213r6Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hltk : k < 1 → k < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1213r6Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r6Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm1, emk1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r6Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1, ivm1R,
        iv2R] at h hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi1213r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m - 1) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm1, emk1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1213r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r6Nondeg.result) =
            fun w => (((env "g" * ((env "d" + (env "e" * w))) ^ (m)) *
            (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (k + 1)) *
            (((2 * env "c") * (env "p" + 1)))⁻¹) +
            (((((-1) * env "e") * env "g") * env "m") * (((2 * env "c") * (env "p" + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi1213r6Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1213r6Nondeg.body =
        (((env "d" + (env "e" * t))) ^ (m) * (env "f" + (env "g" * t))) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1213r6Nondeg, eval, Interp.real, hkm, hkk, iv2R]
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
    refine (((((hasDerivAt_const t (env "g")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t ((((2 * env "c") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn3_2c : ((k : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb2 (by omega)
      · subst hm0
        exact absurd hb2 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb1 (by omega)
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
        simp only [e0m]
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
        field_simp
        linear_combination (-env "a"*env "d"*Pk*Pm*((k : ℤ) : ℝ) - env "a"*env "d"*Pk*Pm -
            env "a"*env "e"*Pk*Pm*t*((k : ℤ) : ℝ) - env "a"*env "e"*Pk*Pm*t -
            env "b"*env "d"*Pk*Pm*t*((k : ℤ) : ℝ) - env "b"*env "d"*Pk*Pm*t -
            env "b"*env "e"*Pk*Pm*t^2*((k : ℤ) : ℝ) - env "b"*env "e"*Pk*Pm*t^2 -
            env "c"*env "d"*Pk*Pm*t^2*((k : ℤ) : ℝ) - env "c"*env "d"*Pk*Pm*t^2 -
            env "c"*env "e"*Pk*Pm*t^3*((k : ℤ) : ℝ) - env "c"*env "e"*Pk*Pm*t^3) * hr0

set_option maxHeartbeats 1000000 in
theorem rubi1213r6Nondeg_complex : rubi1213r6Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1213r6Nondeg.conditions rubi1213r6Nondeg.body
    rubi1213r6Nondeg.result rubi1213r6Nondeg.integrals
  intro env hc t hF
  have hr0 : ((2 * env "c") * env "f") + (((-1) * env "b") * env "g") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))) (.int 0)) (by simp [rubi1213r6Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1213r6Nondeg])
  have hn3_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r6Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r6Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have hb1 : k < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1213r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkk, Complex.ext_iff] at h
    have h' : ((k : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hb2 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi1213r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hltk : k < 1 → k < 0 := by omega
  have emm1 : intValue? (env "m" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm2 : intValue? (env "m" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emmm1 : intValue? (env "m" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have hom1 : m + 1 < 0 → m < 0 := by omega
  have hom2 : m + 2 < 0 → m < 0 := by omega
  have emk1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "p" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1213r6Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r6Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emmm1, emk1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r6Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emk1, ivm1C,
        iv2C] at h hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi1213r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m - 1) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emmm1, emk1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1213r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r6Nondeg.result) =
            fun w => (((env "g" * ((env "d" + (env "e" * w))) ^ (m)) *
            (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (k + 1)) *
            (((2 * env "c") * (env "p" + 1)))⁻¹) +
            (((((-1) * env "e") * env "g") * env "m") * (((2 * env "c") * (env "p" + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi1213r6Nondeg, eval, recEnv, Interp.complex, hkm, emk1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1213r6Nondeg.body =
        (((env "d" + (env "e" * t))) ^ (m) * (env "f" + (env "g" * t))) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1213r6Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
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
    refine (((((hasDerivAt_const t (env "g")).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t ((((2 * env "c") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn3_2c : ((k : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb2 (by omega)
      · subst hm0
        exact absurd hb2 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb1 (by omega)
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
        simp only [e0m]
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
        field_simp
        linear_combination (-env "a"*env "d"*Pk*Pm*((k : ℤ) : ℂ) - env "a"*env "d"*Pk*Pm -
            env "a"*env "e"*Pk*Pm*t*((k : ℤ) : ℂ) - env "a"*env "e"*Pk*Pm*t -
            env "b"*env "d"*Pk*Pm*t*((k : ℤ) : ℂ) - env "b"*env "d"*Pk*Pm*t -
            env "b"*env "e"*Pk*Pm*t^2*((k : ℤ) : ℂ) - env "b"*env "e"*Pk*Pm*t^2 -
            env "c"*env "d"*Pk*Pm*t^2*((k : ℤ) : ℂ) - env "c"*env "d"*Pk*Pm*t^2 -
            env "c"*env "e"*Pk*Pm*t^3*((k : ℤ) : ℂ) - env "c"*env "e"*Pk*Pm*t^3) * hr0

end OSR.IntegrationRec294
