import OSR.IntegrationNum1

/-! # Strengthened variants with two integer exponents: explicit terms plus a residual integral

Proofs of RUBI rules whose result is an explicit term with powers `y^m z^n` plus at most one residual
integral. The derivative of the explicit term is built from the rule expression; the integrand is
recovered with `sin² + cos² = 1` (when trigonometric) and the stated parameter relations, separately
for each exponent equal to `0` or not (`linear_combination` coefficients computed by Gröbner
reduction). Rules with `csc`, `cot` or `arctan` are proved over ℝ only. -/

namespace OSR.IntegrationRec297

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

/-! ## rubi1216r17Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1216r17Nondeg_real : rubi1216r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1216r17Nondeg.conditions rubi1216r17Nondeg.body
    rubi1216r17Nondeg.result rubi1216r17Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "e") ^ 2 + (((-4) * env "d") * env "f") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0)) (by simp [rubi1216r17Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1216r17Nondeg])
  have hn3_1 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_3 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r17Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r17Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1216r17Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hb2 : 0 < k := by
    have h := hc (.gt (.var "q") (.int 0)) (by simp [rubi1216r17Nondeg])
    have h' : (0 : ℝ) < ((k : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hltk : k < 1 → k < 0 := by omega
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
  have emk1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "q" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "q" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "q" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1216r17Nondeg.body →
      (m < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) ∧
          (k < 0 → ((env "d" + (env "e" * w)) + (env "f" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1216r17Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emm1, emmk1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1216r17Nondeg, Defined, eval, recEnv, Interp.real, hkk, emm1, ivm1R,
        iv2R] at h hn0 hn3_1 hn3_2 hn3_3 ⊢
    tauto
  · simp only [rubi1216r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1) *
        (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1)) *
        ((((((env "g" * env "c") * env "d") * ((2 * env "p") + 3)) +
        (((((-1) * env "a") * env "h") * env "e") * env "q")) +
        (((((env "g" * env "c") * env "e") * (((2 * env "p") + env "q") + 3)) +
        ((((((-1) * env "a") * 2) * env "h") * env "f") * env "q")) * t)) +
        ((((env "g" * env "c") * env "f") * (((2 * env "p") + (2 * env "q")) + 3)) *
        (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emm1, emmk1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1216r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1216r17Nondeg.result) =
            fun w => (((((env "a" * env "h") + ((((-1) * env "g") * env "c") * w)) *
            ((env "a" + (env "c" * (w) ^ 2))) ^ (m + 1)) *
            (((env "d" + (env "e" * w)) + (env "f" * (w) ^ 2))) ^ (k)) *
            ((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹) +
            (2 * ((((4 * env "a") * env "c") * (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1216r17Nondeg, eval, recEnv, Interp.real, hkk, emm1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1216r17Nondeg.body =
        (((env "a" + (env "c" * (t) ^ 2))) ^ (m) *
        (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k)) * (env "g" + (env "h" * t)) := by
      simp [rubi1216r17Nondeg, eval, Interp.real, hkm, hkk, iv2R]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t ((env "a" *
        env "h"))).add ((hasDerivAt_const t ((((-1) * env "g") *
        env "c"))).mul (hasDerivAt_id' t))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) (((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "f")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn3_3c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_3
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb2 (by omega)
      · have hdmm : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "c" * (t) ^ 2))) ^ m =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 2) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m]
        have hdmk : ((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ k =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k + 1) =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k + 2) =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        generalize (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        ring

set_option maxHeartbeats 1000000 in
theorem rubi1216r17Nondeg_complex : rubi1216r17Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1216r17Nondeg.conditions rubi1216r17Nondeg.body
    rubi1216r17Nondeg.result rubi1216r17Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "e") ^ 2 + (((-4) * env "d") * env "f") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0)) (by simp [rubi1216r17Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1216r17Nondeg])
  have hn3_1 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_3 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r17Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1216r17Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1216r17Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hb2 : 0 < k := by
    have h := hc (.gt (.var "q") (.int 0)) (by simp [rubi1216r17Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkk, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((k : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
  have hltk : k < 1 → k < 0 := by omega
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
  have emk1 : intValue? (env "q" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emk2 : intValue? (env "q" + 2) = some (k + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk1 : intValue? (env "q" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have emmk2 : intValue? (env "q" + -2) = some (k - 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkk]; push_cast; ring)
  have hok1 : k + 1 < 0 → k < 0 := by omega
  have hok2 : k + 2 < 0 → k < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1216r17Nondeg.body →
      (m < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) ∧
          (k < 0 → ((env "d" + (env "e" * w)) + (env "f" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1216r17Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1216r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emm1, emmk1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1216r17Nondeg, Defined, eval, recEnv, Interp.complex, hkk, emm1, ivm1C,
        iv2C] at h hn0 hn3_1 hn3_2 hn3_3 ⊢
    tauto
  · simp only [rubi1216r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1) *
        (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1)) *
        ((((((env "g" * env "c") * env "d") * ((2 * env "p") + 3)) +
        (((((-1) * env "a") * env "h") * env "e") * env "q")) +
        (((((env "g" * env "c") * env "e") * (((2 * env "p") + env "q") + 3)) +
        ((((((-1) * env "a") * 2) * env "h") * env "f") * env "q")) * t)) +
        ((((env "g" * env "c") * env "f") * (((2 * env "p") + (2 * env "q")) + 3)) *
        (t) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emm1, emmk1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1216r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1216r17Nondeg.result) =
            fun w => (((((env "a" * env "h") + ((((-1) * env "g") * env "c") * w)) *
            ((env "a" + (env "c" * (w) ^ 2))) ^ (m + 1)) *
            (((env "d" + (env "e" * w)) + (env "f" * (w) ^ 2))) ^ (k)) *
            ((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹) +
            (2 * ((((4 * env "a") * env "c") * (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1216r17Nondeg, eval, recEnv, Interp.complex, hkk, emm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1216r17Nondeg.body =
        (((env "a" + (env "c" * (t) ^ 2))) ^ (m) *
        (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k)) * (env "g" + (env "h" * t)) := by
      simp [rubi1216r17Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
    rw [hfun, hEF]
    obtain ⟨hBm0, hBk0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    have hdzk : ∀ E : ℤ, (E < 0 → k < 0) →
        ((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBk0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t ((env "a" *
        env "h"))).add ((hasDerivAt_const t ((((-1) * env "g") *
        env "c"))).mul (hasDerivAt_id' t))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) (((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "f")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((((2 * env "a") * env "c") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn3_3c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_3
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb2 (by omega)
      · have hdmm : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
          by_cases hm : m < 0
          · exact Or.inl (hBm0 hm)
          · exact Or.inr (by omega)
        have e0m : ((env "a" + (env "c" * (t) ^ 2))) ^ m =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
          rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
        have e1m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
          rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
        have e2m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 2) =
            ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 :=
            by
          have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
          rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
        simp only [e0m, e1m]
        have hdmk : ((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ k =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 1 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k + 1) =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 2 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k + 2) =
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) *
            (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ 3 := by
          have := zsplit (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) (k - 1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
        generalize (((env "d" + (env "e" * t)) + (env "f" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        ring

/-! ## rubi416r31Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi416r31Nondeg_real : rubi416r31Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r31Nondeg.conditions rubi416r31Nondeg.body
    rubi416r31Nondeg.result rubi416r31Nondeg.integrals
  intro env hc t hF
  have hn1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r31Nondeg])
  have hn1v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r31Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi416r31Nondeg])
  have hn2_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r31Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb0 : 0 < m := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi416r31Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r31Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r31Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r31Nondeg, Defined, eval, recEnv, Interp.real, hkm,
        ivm1R] at h hn1 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi416r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
        (((((env "a" * ((env "b" * env "B") + (env "c" * env "C"))) * env "n") +
        (((env "a") ^ 2 * env "A") * (env "n" + 1))) +
        (((env "n" *
        ((((env "a") ^ 2 * env "B") + (((-1) * env "B") * (env "c") ^ 2)) +
        ((env "b" * env "c") * env "C"))) + (((env "a" * env "b") * env "A") * (env "n" + 1))) *
        Real.cos ((env "d" + (env "e" * t))))) +
        (((env "n" *
        ((((env "b" * env "B") * env "c") + ((env "a") ^ 2 * env "C")) +
        (((-1) * (env "b") ^ 2) * env "C"))) + (((env "a" * env "c") * env "A") * (env "n" + 1))) *
        Real.sin ((env "d" + (env "e" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi416r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r31Nondeg.result) =
            fun w => ((((((env "B" * env "c") + (((-1) * env "b") * env "C")) +
            ((((-1) * env "a") * env "C") * Real.cos ((env "d" + (env "e" * w))))) +
            ((env "a" * env "B") * Real.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * (env "n" + 1)))⁻¹) + (1 * ((env "a" * (env "n" + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi416r31Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r31Nondeg.body =
        ((env "A" + (env "B" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "C" * Real.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r31Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((env "B" * env "c") +
        (((-1) * env "b") * env "C")))).add ((hasDerivAt_const t ((((-1) * env "a") *
        env "C"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t ((env "a" * env "B"))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = Pm
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "B"*env "a"*env "b"*env "e"*Pm*((m : ℤ) : ℝ) -
          env "C"*env "a"*env "c"*env "e"*Pm*((m : ℤ) : ℝ)) * hP

set_option maxHeartbeats 1000000 in
theorem rubi416r31Nondeg_complex : rubi416r31Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi416r31Nondeg.conditions rubi416r31Nondeg.body
    rubi416r31Nondeg.result rubi416r31Nondeg.integrals
  intro env hc t hF
  have hn1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r31Nondeg])
  have hn1v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r31Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi416r31Nondeg])
  have hn2_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r31Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb0 : 0 < m := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi416r31Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r31Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r31Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r31Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emmm1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r31Nondeg, Defined, eval, recEnv, Interp.complex, hkm,
        ivm1C] at h hn1 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi416r31Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
        (((((env "a" * ((env "b" * env "B") + (env "c" * env "C"))) * env "n") +
        (((env "a") ^ 2 * env "A") * (env "n" + 1))) +
        (((env "n" *
        ((((env "a") ^ 2 * env "B") + (((-1) * env "B") * (env "c") ^ 2)) +
        ((env "b" * env "c") * env "C"))) + (((env "a" * env "b") * env "A") * (env "n" + 1))) *
        Complex.cos ((env "d" + (env "e" * t))))) +
        (((env "n" *
        ((((env "b" * env "B") * env "c") + ((env "a") ^ 2 * env "C")) +
        (((-1) * (env "b") ^ 2) * env "C"))) + (((env "a" * env "c") * env "A") * (env "n" + 1))) *
        Complex.sin ((env "d" + (env "e" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emmm1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi416r31Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r31Nondeg.result) =
            fun w => ((((((env "B" * env "c") + (((-1) * env "b") * env "C")) +
            ((((-1) * env "a") * env "C") * Complex.cos ((env "d" + (env "e" * w))))) +
            ((env "a" * env "B") * Complex.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * (env "n" + 1)))⁻¹) + (1 * ((env "a" * (env "n" + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi416r31Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r31Nondeg.body =
        ((env "A" + (env "B" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "C" * Complex.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r31Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((env "B" * env "c") +
        (((-1) * env "b") * env "C")))).add ((hasDerivAt_const t ((((-1) * env "a") *
        env "C"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t ((env "a" * env "B"))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = Pm
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "B"*env "a"*env "b"*env "e"*Pm*((m : ℤ) : ℂ) -
          env "C"*env "a"*env "c"*env "e"*Pm*((m : ℤ) : ℂ)) * hP

/-! ## rubi416r32Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi416r32Nondeg_real : rubi416r32Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r32Nondeg.conditions rubi416r32Nondeg.body
    rubi416r32Nondeg.result rubi416r32Nondeg.integrals
  intro env hc t hF
  have hn1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r32Nondeg])
  have hn1v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r32Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi416r32Nondeg])
  have hn2_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r32Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb0 : 0 < m := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi416r32Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r32Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r32Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r32Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r32Nondeg, Defined, eval, recEnv, Interp.real, hkm,
        ivm1R] at h hn1 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi416r32Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
        ((((((env "a" * env "c") * env "C") * env "n") +
        (((env "a") ^ 2 * env "A") * (env "n" + 1))) +
        (((((env "c" * env "b") * env "C") * env "n") +
        (((env "a" * env "b") * env "A") * (env "n" + 1))) *
        Real.cos ((env "d" + (env "e" * t))))) +
        ((((((env "a") ^ 2 * env "C") * env "n") +
        ((((-1) * (env "b") ^ 2) * env "C") * env "n")) +
        (((env "a" * env "c") * env "A") * (env "n" + 1))) *
        Real.sin ((env "d" + (env "e" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi416r32Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r32Nondeg.result) =
            fun w => ((((-1) *
            ((env "b" * env "C") + ((env "a" * env "C") * Real.cos ((env "d" + (env "e" * w)))))) *
            (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * (env "n" + 1)))⁻¹) + (1 * ((env "a" * (env "n" + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi416r32Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r32Nondeg.body =
        (env "A" + (env "C" * Real.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r32Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul ((hasDerivAt_const t ((env "b" *
        env "C"))).add ((hasDerivAt_const t ((env "a" *
        env "C"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = Pm
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "C"*env "a"*env "c"*env "e"*Pm*((m : ℤ) : ℝ)) * hP

set_option maxHeartbeats 1000000 in
theorem rubi416r32Nondeg_complex : rubi416r32Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi416r32Nondeg.conditions rubi416r32Nondeg.body
    rubi416r32Nondeg.result rubi416r32Nondeg.integrals
  intro env hc t hF
  have hn1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r32Nondeg])
  have hn1v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r32Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi416r32Nondeg])
  have hn2_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r32Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb0 : 0 < m := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi416r32Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r32Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r32Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r32Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emmm1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r32Nondeg, Defined, eval, recEnv, Interp.complex, hkm,
        ivm1C] at h hn1 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi416r32Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
        ((((((env "a" * env "c") * env "C") * env "n") +
        (((env "a") ^ 2 * env "A") * (env "n" + 1))) +
        (((((env "c" * env "b") * env "C") * env "n") +
        (((env "a" * env "b") * env "A") * (env "n" + 1))) *
        Complex.cos ((env "d" + (env "e" * t))))) +
        ((((((env "a") ^ 2 * env "C") * env "n") +
        ((((-1) * (env "b") ^ 2) * env "C") * env "n")) +
        (((env "a" * env "c") * env "A") * (env "n" + 1))) *
        Complex.sin ((env "d" + (env "e" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emmm1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi416r32Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r32Nondeg.result) =
            fun w => ((((-1) *
            ((env "b" * env "C") +
            ((env "a" * env "C") * Complex.cos ((env "d" + (env "e" * w)))))) *
            (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * (env "n" + 1)))⁻¹) + (1 * ((env "a" * (env "n" + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi416r32Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r32Nondeg.body =
        (env "A" + (env "C" * Complex.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r32Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul ((hasDerivAt_const t ((env "b" *
        env "C"))).add ((hasDerivAt_const t ((env "a" *
        env "C"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = Pm
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "C"*env "a"*env "c"*env "e"*Pm*((m : ℤ) : ℂ)) * hP

/-! ## rubi416r33Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi416r33Nondeg_real : rubi416r33Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r33Nondeg.conditions rubi416r33Nondeg.body
    rubi416r33Nondeg.result rubi416r33Nondeg.integrals
  intro env hc t hF
  have hn1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r33Nondeg])
  have hn1v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r33Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi416r33Nondeg])
  have hn2_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r33Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb0 : 0 < m := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi416r33Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r33Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r33Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r33Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r33Nondeg, Defined, eval, recEnv, Interp.real, hkm,
        ivm1R] at h hn1 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi416r33Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
        ((((((env "a" * env "b") * env "B") * env "n") +
        (((env "a") ^ 2 * env "A") * (env "n" + 1))) +
        ((((((env "a") ^ 2 * env "B") * env "n") +
        ((((-1) * (env "c") ^ 2) * env "B") * env "n")) +
        (((env "a" * env "b") * env "A") * (env "n" + 1))) *
        Real.cos ((env "d" + (env "e" * t))))) +
        (((((env "b" * env "c") * env "B") * env "n") +
        (((env "a" * env "c") * env "A") * (env "n" + 1))) *
        Real.sin ((env "d" + (env "e" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi416r33Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r33Nondeg.result) =
            fun w => ((((env "B" * env "c") +
            ((env "a" * env "B") * Real.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * (env "n" + 1)))⁻¹) + (1 * ((env "a" * (env "n" + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi416r33Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r33Nondeg.body =
        (env "A" + (env "B" * Real.cos ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r33Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((env "B" *
        env "c"))).add ((hasDerivAt_const t ((env "a" *
        env "B"))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = Pm
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "B"*env "a"*env "b"*env "e"*Pm*((m : ℤ) : ℝ)) * hP

set_option maxHeartbeats 1000000 in
theorem rubi416r33Nondeg_complex : rubi416r33Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi416r33Nondeg.conditions rubi416r33Nondeg.body
    rubi416r33Nondeg.result rubi416r33Nondeg.integrals
  intro env hc t hF
  have hn1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r33Nondeg])
  have hn1v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r33Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi416r33Nondeg])
  have hn2_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r33Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb0 : 0 < m := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi416r33Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r33Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r33Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r33Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emmm1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r33Nondeg, Defined, eval, recEnv, Interp.complex, hkm,
        ivm1C] at h hn1 hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi416r33Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
        ((((((env "a" * env "b") * env "B") * env "n") +
        (((env "a") ^ 2 * env "A") * (env "n" + 1))) +
        ((((((env "a") ^ 2 * env "B") * env "n") +
        ((((-1) * (env "c") ^ 2) * env "B") * env "n")) +
        (((env "a" * env "b") * env "A") * (env "n" + 1))) *
        Complex.cos ((env "d" + (env "e" * t))))) +
        (((((env "b" * env "c") * env "B") * env "n") +
        (((env "a" * env "c") * env "A") * (env "n" + 1))) *
        Complex.sin ((env "d" + (env "e" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emmm1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi416r33Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r33Nondeg.result) =
            fun w => ((((env "B" * env "c") +
            ((env "a" * env "B") * Complex.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * (env "n" + 1)))⁻¹) + (1 * ((env "a" * (env "n" + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi416r33Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r33Nondeg.body =
        (env "A" + (env "B" * Complex.cos ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r33Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((env "B" *
        env "c"))).add ((hasDerivAt_const t ((env "a" *
        env "B"))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = Pm
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "B"*env "a"*env "b"*env "e"*Pm*((m : ℤ) : ℂ)) * hP

/-! ## rubi416r5Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi416r5Nondeg_real : rubi416r5Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r5Nondeg.conditions rubi416r5Nondeg.body
    rubi416r5Nondeg.result rubi416r5Nondeg.integrals
  intro env hc t hF
  have hr0 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r5Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.int 1))) (.int 0)) (by simp [rubi416r5Nondeg])
  have hn2_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : (2 * env "n") + 1 ≠ 0 := by
    have h := hc2
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r5Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi416r5Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r5Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r5Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emm1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r5Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R] at h hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi416r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emm1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi416r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r5Nondeg.result) =
            fun w => ((((env "c" * Real.cos ((env "d" + (env "e" * w)))) +
            (((-1) * env "b") * Real.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * ((2 * env "n") + 1)))⁻¹) +
            ((env "n" + 1) * ((env "a" * ((2 * env "n") + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi416r5Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r5Nondeg.body =
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r5Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).add ((hasDerivAt_const t (((-1) * env "b"))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * ((2 * env "n") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2_2c : (2 * ((m : ℤ) : ℝ)) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb1 (by omega)
    · have hdmm : ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m]
      generalize (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = Pm
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      have hdn0 : ((m : ℤ) : ℝ) * 2 + 1 ≠ 0 := fun h0 => hn2_2c (by linear_combination (1) * h0)
      field_simp
      linear_combination (env "b"^2*env "e"*Pm*((m : ℤ) : ℝ) +
          env "c"^2*env "e"*Pm*((m : ℤ) : ℝ)) * hP + (-env "e"*Pm*((m : ℤ) : ℝ)) * hr0

set_option maxHeartbeats 1000000 in
theorem rubi416r5Nondeg_complex : rubi416r5Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi416r5Nondeg.conditions rubi416r5Nondeg.body
    rubi416r5Nondeg.result rubi416r5Nondeg.integrals
  intro env hc t hF
  have hr0 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r5Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.int 1))) (.int 0)) (by simp [rubi416r5Nondeg])
  have hn2_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_2 : (2 * env "n") + 1 ≠ 0 := by
    have h := hc2
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r5Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi416r5Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r5Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r5Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emm1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r5Nondeg, Defined, eval, recEnv, Interp.complex, hkm,
        ivm1C] at h hn2_0 hn2_1 hn2_2 ⊢
    tauto
  · simp only [rubi416r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emm1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi416r5Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r5Nondeg.result) =
            fun w => ((((env "c" * Complex.cos ((env "d" + (env "e" * w)))) +
            (((-1) * env "b") * Complex.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * ((2 * env "n") + 1)))⁻¹) +
            ((env "n" + 1) * ((env "a" * ((2 * env "n") + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi416r5Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r5Nondeg.body =
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r5Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).add ((hasDerivAt_const t (((-1) * env "b"))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * ((2 * env "n") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2_2c : (2 * ((m : ℤ) : ℂ)) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb1 (by omega)
    · have hdmm : ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m]
      generalize (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = Pm
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      have hdn0 : ((m : ℤ) : ℂ) * 2 + 1 ≠ 0 := fun h0 => hn2_2c (by linear_combination (1) * h0)
      field_simp
      linear_combination (env "b"^2*env "e"*Pm*((m : ℤ) : ℂ) +
          env "c"^2*env "e"*Pm*((m : ℤ) : ℂ)) * hP + (-env "e"*Pm*((m : ℤ) : ℂ)) * hr0

/-! ## rubi417r2Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi417r2Nondeg_real : rubi417r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi417r2Nondeg.conditions rubi417r2Nondeg.body
    rubi417r2Nondeg.result rubi417r2Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi417r2Nondeg])
  have hn1_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_2 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi417r2Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb0 : 0 < m := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi417r2Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi417r2Nondeg.body →
      (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w)))) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi417r2Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi417r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi417r2Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R, iv2R] at h hn1_1 hn1_2 ⊢
    tauto
  · simp only [rubi417r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
        (((env "a" * env "B") + (((2 * env "a") * env "A") * (env "p" + 1))) +
        (((((2 * env "A") * env "b") * (env "p" + 1)) +
        (env "B" * ((env "b" + ((2 * env "a") * env "p")) + ((2 * env "b") * env "p")))) *
        (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi417r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi417r2Nondeg.result) =
            fun w => ((((((-1) * env "B") * Real.cos ((env "e" + (env "f" * w)))) *
            Real.sin ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w)))) ^ 2))) ^ (m)) *
            (((2 * env "f") * (env "p" + 1)))⁻¹) + (1 * ((2 * (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi417r2Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi417r2Nondeg.body =
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m) *
        (env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi417r2Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "B"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).pow 2))))).mul (hasDerivAt_const t ((((2 * env "f") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply]
    have hn1_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ m -
        1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ m =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 1) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m + 2) =
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "B"*env "a"*env "f"*Pm -
          2*env "B"*env "b"*env "f"*Pm*S^2*((m : ℤ) : ℝ) - env "B"*env "b"*env "f"*Pm*S^2) * hP

set_option maxHeartbeats 1000000 in
theorem rubi417r2Nondeg_complex : rubi417r2Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi417r2Nondeg.conditions rubi417r2Nondeg.body
    rubi417r2Nondeg.result rubi417r2Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi417r2Nondeg])
  have hn1_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_2 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi417r2Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb0 : 0 < m := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi417r2Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi417r2Nondeg.body →
      (m < 0 → (env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * w)))) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi417r2Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi417r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emmm1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi417r2Nondeg, Defined, eval, recEnv, Interp.complex, hkm, ivm1C,
        iv2C] at h hn1_1 hn1_2 ⊢
    tauto
  · simp only [rubi417r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" +
        (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
        (((env "a" * env "B") + (((2 * env "a") * env "A") * (env "p" + 1))) +
        (((((2 * env "A") * env "b") * (env "p" + 1)) +
        (env "B" * ((env "b" + ((2 * env "a") * env "p")) + ((2 * env "b") * env "p")))) *
        (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emmm1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi417r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi417r2Nondeg.result) =
            fun w => ((((((-1) * env "B") * Complex.cos ((env "e" + (env "f" * w)))) *
            Complex.sin ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * w)))) ^ 2))) ^ (m)) *
            (((2 * env "f") * (env "p" + 1)))⁻¹) + (1 * ((2 * (env "p" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi417r2Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi417r2Nondeg.body =
        ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m) *
        (env "A" + (env "B" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi417r2Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "B"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).pow 2))))).mul (hasDerivAt_const t ((((2 * env "f") * (env "p" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply]
    have hn1_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb0 (by omega)
    · have hdmm : (env "a" +
        (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ m =
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 1 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m +
          1) = ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 2 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m +
          2) = ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m - 1) *
          ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ 3 := by
        have := zsplit ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) (m -
            1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize ((env "a" + (env "b" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) ^ (m -
          1) = Pm
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "B"*env "a"*env "f"*Pm -
          2*env "B"*env "b"*env "f"*Pm*S^2*((m : ℤ) : ℂ) - env "B"*env "b"*env "f"*Pm*S^2) * hP

/-! ## rubi4512r49Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4512r49Nondeg_real : rubi4512r49Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4512r49Nondeg.conditions rubi4512r49Nondeg.body
    rubi4512r49Nondeg.result rubi4512r49Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4512r49Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4512r49Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4512r49Nondeg])
  have hn2_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  have hn2_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc2
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4512r49Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb1 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi4512r49Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4512r49Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4512r49Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4512r49Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm1, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4512r49Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R,
        Fn.csc] at h hn0 hn2_0 hn2_1 ⊢
    tauto
  · simp only [rubi4512r49Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1)) *
        (env "b" + (env "a" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm1, Fn.csc, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4512r49Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4512r49Nondeg.result) =
            fun w => ((((-1) *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m)) *
            ((env "f" * (env "m" + 1)))⁻¹) + (env "m" * ((env "m" + 1))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4512r49Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4512r49Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2 *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) := by
      simp [rubi4512r49Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t (((env "f" * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hn2_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_1
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb1 (by omega)
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
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "a"*env "f"*Pm*S + env "b"*env "f"*Pm*((m : ℤ) : ℝ) +
          env "b"*env "f"*Pm) * hP

/-! ## rubi4531r29Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4531r29Nondeg_real : rubi4531r29Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r29Nondeg.conditions rubi4531r29Nondeg.body
    rubi4531r29Nondeg.result rubi4531r29Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "A" * env "b") + (((-1) * env "a") * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r29Nondeg])
  have hn0v : (env "A" * env "b") + (-env "a" * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r29Nondeg])
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r29Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r29Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.var "n")) (.int 0)) (by simp [rubi4531r29Nondeg])
  have hn3_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r29Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  have hb2 : m ≤ -1 := by
    have h := hc (.ge (.int (-1)) (.var "n")) (by simp [rubi4531r29Nondeg])
    have h' : ((m : ℤ) : ℝ) ≤ (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      rcases h with h | h <;> linarith
    exact_mod_cast h'
  have hltm : m < 1 → m < 0 := by omega
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r29Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4531r29Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r29Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emm1, iv2R, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4531r29Nondeg, Defined, eval, recEnv, Interp.real, emm1, ivm1R, iv2R,
        Fn.csc] at h hn0 hn1 hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi4531r29Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m +
        1) * ((((env "a" * (((2 * env "A") * env "b") + (env "a" * env "B"))) * env "n") +
        ((((((2 * env "a") * env "b") * env "B") * env "n") +
        (env "A" * (((env "b") ^ 2 * env "n") + ((env "a") ^ 2 * (env "n" + 1))))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        ((((env "b") ^ 2 * env "B") * env "n") *
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emm1, iv2R, Fn.csc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4531r29Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4531r29Nondeg.result) =
            fun w => (((((env "a") ^ 2 * env "A") * Real.cos ((env "e" + (env "f" * w)))) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (m + 1)) *
            (((env "d" * env "f") * env "n"))⁻¹) + (1 * ((env "d" * env "n"))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4531r29Nondeg, eval, recEnv, Interp.real, emm1, ivm1R, iv2R, Fn.csc,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r29Nondeg.body =
        (((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ 2 *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m)) *
        (env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) := by
      simp [rubi4531r29Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((env "a") ^ 2 *
        env "A"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdzm (m + 1) (by omega))) ((hasDerivAt_const t (env "d")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)))).mul (hasDerivAt_const t ((((env "d" * env "f") * env "n"))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.inv_apply,

      add_sub_cancel_right]
    have hn3_2c : ((m : ℤ) : ℝ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd (by norm_num) hn3_2c
    · have hdmm : (env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ m =
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 1 := by
        have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m + 1) =
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 2 := by
        have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m + 2) =
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 3 := by
        have := zsplit ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m]
      generalize ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^2*env "d"*env "f"*Pm*S*((m : ℤ) : ℝ) -
          env "A"*env "a"^2*env "d"*env "f"*Pm*S) * hP

/-! ## rubi4531r7Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4531r7Nondeg_real : rubi4531r7Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r7Nondeg.conditions rubi4531r7Nondeg.body
    rubi4531r7Nondeg.result rubi4531r7Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "A" * env "b") + (((-1) * env "a") * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r7Nondeg])
  have hn0v : (env "A" * env "b") + (-env "a" * env "B") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)) (by simp [rubi4531r7Nondeg])
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r7Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4531r7Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi4531r7Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "m" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4531r7Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h
  have hb2 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi4531r7Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4531r7Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) := by
    intro w h
    simp [rubi4531r7Nondeg, Defined, eval, Interp.real, hkm, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emmm1, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4531r7Nondeg, Defined, eval, recEnv, Interp.real, hkm, ivm1R,
        Fn.csc] at h hn0 hn1 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi4531r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1)) *
        ((((env "b" * env "B") * env "m") + ((env "a" * env "A") * (env "m" + 1))) +
        ((((env "a" * env "B") * env "m") + ((env "A" * env "b") * (env "m" + 1))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emmm1, Fn.csc, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4531r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4531r7Nondeg.result) =
            fun w => (((((-1) * env "B") *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m)) *
            ((env "f" * (env "m" + 1)))⁻¹) + (1 * ((env "m" + 1))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4531r7Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4531r7Nondeg.body =
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹ *
        ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m)) *
        (env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) := by
      simp [rubi4531r7Nondeg, eval, Interp.real, hkm, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t (((-1) *
        env "B"))).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0))))).mul (hasDerivAt_const t (((env "f" * (env "m" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hn3_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd hb2 (by omega)
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
      generalize ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (env "B"*env "a"*env "f"*Pm*S + env "B"*env "b"*env "f"*Pm*((m : ℤ) : ℝ) +
          env "B"*env "b"*env "f"*Pm) * hP

/-! ## rubi4541r3Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4541r3Nondeg_real : rubi4541r3Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4541r3Nondeg.conditions rubi4541r3Nondeg.body
    rubi4541r3Nondeg.result
  intro env hc t hF
  have hr0 : (env "C" * env "m") + (env "A" * (env "m" + 1)) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "C") (.var "m")) (.app2 .mul (.var "A") (.app2 .add (.var "m") (.int 1)))) (.int 0)) (by simp [rubi4541r3Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc1 := hc (.ne (.app2 .mul (.var "f") (.var "m")) (.int 0)) (by simp [rubi4541r3Nondeg])
  have hn1_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_1 : env "m" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4541r3Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4541r3Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4541r3Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4541r3Nondeg, Defined, eval, Interp.real, hkm, ivm1R, Fn.csc] at h hn1_0 hn1_1 ⊢
    tauto
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w)
        rubi4541r3Nondeg.result) =
            fun w => (((env "A" *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (m)) *
            ((env "f" * env "m"))⁻¹) := by
      funext w
      simp [rubi4541r3Nondeg, eval, Interp.real, hkm, ivm1R, Fn.csc, Real.cot_eq_cos_div_sin,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4541r3Nondeg.body =
        ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m) *
        (env "A" + (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4541r3Nondeg, eval, Interp.real, hkm, iv2R, Fn.csc]
    rw [hfun, hEF]
    obtain ⟨hs0, hBm0⟩ := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine ((((hasDerivAt_const t (env "A")).mul (((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).div ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))) hs0)).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "b")).mul (((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))).inv hs0)))).mul (hasDerivAt_const t (((env "f" * env "m"))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
    have hr0c : (env "C" * ((m : ℤ) : ℝ)) + (env "A" * (((m : ℤ) : ℝ) + 1)) - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm]; exact hr0
    have hn1_1c : ((m : ℤ) : ℝ) ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_1
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      exact absurd (by norm_num) hn1_1c
    · have hdmm : (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ m =
          ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 1 := by
        have := zsplit ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m + 1) =
          ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 2 := by
        have := zsplit ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m + 2) =
          ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) *
          ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ 3 := by
        have := zsplit ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m]
      generalize ((env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (m - 1) = Pm
      generalize Real.sin (env "e" + env "f" * t) = S at hs0 hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "b"*env "f"*Pm*((m : ℤ) : ℝ) - env "A"*env "b"*env "f"*Pm) *
          hP + (-env "b"*env "f"*Pm) * hr0c

/-! ## rubi4542r25Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4542r25Nondeg_real : rubi4542r25Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r25Nondeg.conditions rubi4542r25Nondeg.body
    rubi4542r25Nondeg.result rubi4542r25Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r25Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r25Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int 0)) (by simp [rubi4542r25Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : (env "m" + env "n") + 1 ≠ 0 := by
    have h := hc3
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r25Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r25Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc] at h
  have hb1 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi4542r25Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hb2 : -1 < k := by
    have h := hc (.gt (.var "n") (.int (-1))) (by simp [rubi4542r25Nondeg])
    have h' : (-1 : ℝ) < ((k : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r25Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) ∧
          (k < 0 → (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4542r25Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r25Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emmm1, iv2R, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r25Nondeg, Defined, eval, recEnv, Interp.real, hkm, hkk, ivm1R,
        Fn.csc] at h hn0 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi4542r25Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k)) *
        (((((env "a" * env "A") * ((env "m" + env "n") + 1)) + ((env "a" * env "C") * env "n")) +
        (((((env "A" * env "b") + (env "a" * env "B")) * ((env "m" + env "n") + 1)) +
        ((env "b" * env "C") * (env "m" + env "n"))) * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        ((((env "b" * env "B") * ((env "m" + env "n") + 1)) + ((env "a" * env "C") * env "m")) *
        ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emmm1, iv2R, Fn.csc, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r25Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r25Nondeg.result) =
            fun w => ((((((-1) * env "C") *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m)) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (k)) *
            ((env "f" * ((env "m" + env "n") + 1)))⁻¹) + (1 * (((env "m" + env "n") + 1))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4542r25Nondeg, eval, recEnv, Interp.real, hkm, hkk, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r25Nondeg.body =
        (((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k)) *
        ((env "A" + (env "B" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r25Nondeg, eval, Interp.real, hkm, hkk, iv2R, Fn.csc]
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
    have hn3_1c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
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
        linear_combination (env "C"*env "a"*Pm*S + env "C"*env "b"*Pm*((m : ℤ) : ℝ) +
            env "C"*env "b"*Pm) * hP
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
        linear_combination (env "C"*env "a"*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) +
            env "C"*env "a"*env "d"*env "f"*Pk*Pm*S +
            env "C"*env "b"*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) +
            env "C"*env "b"*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) +
            env "C"*env "b"*env "d"*env "f"*Pk*Pm) * hP

/-! ## rubi4542r26Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4542r26Nondeg_real : rubi4542r26Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4542r26Nondeg.conditions rubi4542r26Nondeg.body
    rubi4542r26Nondeg.result rubi4542r26Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r26Nondeg])
  have hn0v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4542r26Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int 0)) (by simp [rubi4542r26Nondeg])
  have hn3_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : (env "m" + env "n") + 1 ≠ 0 := by
    have h := hc3
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r26Nondeg, Defined, eval, Interp.real, hkm, iv2R, Fn.csc] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4542r26Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc] at h
  have hb1 : 0 < m := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi4542r26Nondeg])
    have h' : (0 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hb2 : -1 < k := by
    have h := hc (.gt (.var "n") (.int (-1))) (by simp [rubi4542r26Nondeg])
    have h' : (-1 : ℝ) < ((k : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4542r26Nondeg.body →
      Real.sin (env "e" + env "f" * w) ≠ 0 ∧
          (m < 0 → (env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ≠ 0) ∧
          (k < 0 → (env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹) ≠ 0) := by
    intro w h
    simp [rubi4542r26Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R, Fn.csc] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4542r26Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emmm1, iv2R, Fn.csc] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4542r26Nondeg, Defined, eval, recEnv, Interp.real, hkm, hkk, ivm1R,
        Fn.csc] at h hn0 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi4542r26Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m - 1) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k)) *
        (((((env "a" * env "A") * ((env "m" + env "n") + 1)) + ((env "a" * env "C") * env "n")) +
        ((env "b" * ((env "A" * ((env "m" + env "n") + 1)) + (env "C" * (env "m" + env "n")))) *
        (Real.sin ((env "e" + (env "f" * t))))⁻¹)) +
        (((env "a" * env "C") * env "m") * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emmm1, iv2R, Fn.csc, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4542r26Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4542r26Nondeg.result) =
            fun w => ((((((-1) * env "C") *
            (Real.cos ((env "e" + (env "f" * w))) / Real.sin ((env "e" + (env "f" * w))))) *
            ((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * w))))⁻¹))) ^ (m)) *
            ((env "d" * (Real.sin ((env "e" + (env "f" * w))))⁻¹)) ^ (k)) *
            ((env "f" * ((env "m" + env "n") + 1)))⁻¹) + (1 * (((env "m" + env "n") + 1))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4542r26Nondeg, eval, recEnv, Interp.real, hkm, hkk, ivm1R, Fn.csc,
          Real.cot_eq_cos_div_sin, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4542r26Nondeg.body =
        (((env "a" + (env "b" * (Real.sin ((env "e" + (env "f" * t))))⁻¹))) ^ (m) *
        ((env "d" * (Real.sin ((env "e" + (env "f" * t))))⁻¹)) ^ (k)) *
        (env "A" + (env "C" * ((Real.sin ((env "e" + (env "f" * t))))⁻¹) ^ 2)) := by
      simp [rubi4542r26Nondeg, eval, Interp.real, hkm, hkk, iv2R, Fn.csc]
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
    have hn3_1c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        exact absurd hb1 (by omega)
      · subst hm0
        exact absurd hb1 (by omega)
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
        linear_combination (env "C"*env "a"*Pm*S + env "C"*env "b"*Pm*((m : ℤ) : ℝ) +
            env "C"*env "b"*Pm) * hP
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
        linear_combination (env "C"*env "a"*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) +
            env "C"*env "a"*env "d"*env "f"*Pk*Pm*S +
            env "C"*env "b"*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) +
            env "C"*env "b"*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) +
            env "C"*env "b"*env "d"*env "f"*Pk*Pm) * hP

/-! ## rubi4131r18Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4131r18Nondeg_real : rubi4131r18Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4131r18Nondeg.conditions rubi4131r18Nondeg.body
    rubi4131r18Nondeg.result rubi4131r18Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4131r18Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4131r18Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4131r18Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn2 : (env "c") ^ 2 + ((-1) * (env "d") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4131r18Nondeg])
  have hn2v : (env "c") ^ 2 + -(env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4131r18Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int 0)) (by simp [rubi4131r18Nondeg])
  have hn5_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_1 : (env "m" + env "n") + 1 ≠ 0 := by
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
    simp [rubi4131r18Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4131r18Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
  have hb3 : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi4131r18Nondeg])
    have h' : (0 : ℝ) < ((k : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltk : k < 1 → k < 0 := by omega
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4131r18Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4131r18Nondeg, Defined, eval, Interp.real, hkm, hkk] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4131r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, emmk1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4131r18Nondeg, Defined, eval, recEnv, Interp.real, hkm, hkk,
        ivm1R] at h hn0 hn2 hn5_0 hn5_1 hda hdb ⊢
    tauto
  · simp only [rubi4131r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1)) *
        (((((env "A" * env "b") * env "c") * ((env "m" + env "n") + 1)) +
        (env "B" * (((env "a" * env "c") * env "m") + ((env "b" * env "d") * env "n")))) +
        (((((env "A" * env "b") * env "d") * ((env "m" + env "n") + 1)) +
        (env "B" * (((env "a" * env "d") * env "m") + ((env "b" * env "c") * env "n")))) *
        Real.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, emmk1, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4131r18Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4131r18Nondeg.result) =
            fun w => ((((((-1) * env "B") * Real.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w)))))) ^ (k)) *
            ((env "f" * ((env "m" + env "n") + 1)))⁻¹) +
            (1 * ((env "b" * ((env "m" + env "n") + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4131r18Nondeg, eval, recEnv, Interp.real, hkm, hkk, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4131r18Nondeg.body =
        (((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k)) *
        (env "A" + (env "B" * Real.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4131r18Nondeg, eval, Interp.real, hkm, hkk]
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
        env "B"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((env "f" * ((env "m" + env "n") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn5_1c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn5_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb3 (by omega)
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 1 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "B"*env "d"*Pk*((k : ℤ) : ℝ)) * hP + (0) * hr1
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
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 1 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "B"*env "a"*env "b"*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) -
            env "B"*env "b"^2*env "c"*env "f"*Pk*Pm*((m : ℤ) : ℝ) -
            env "B"*env "b"^2*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) -
            env "B"*env "b"^2*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ)) * hP +
            (env "B"*env "c"*env "f"*Pk*Pm*((m : ℤ) : ℝ) +
            env "B"*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ)) * hr1

set_option maxHeartbeats 1000000 in
theorem rubi4131r18Nondeg_complex : rubi4131r18Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4131r18Nondeg.conditions rubi4131r18Nondeg.body
    rubi4131r18Nondeg.result rubi4131r18Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4131r18Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4131r18Nondeg])
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4131r18Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hn2 : (env "c") ^ 2 + ((-1) * (env "d") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4131r18Nondeg])
  have hn2v : (env "c") ^ 2 + -(env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4131r18Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int 0)) (by simp [rubi4131r18Nondeg])
  have hn5_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_1 : (env "m" + env "n") + 1 ≠ 0 := by
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
    simp [rubi4131r18Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4131r18Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
  have hb3 : 0 < k := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi4131r18Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkk, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((k : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltk : k < 1 → k < 0 := by omega
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4131r18Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4131r18Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4131r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, emmk1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4131r18Nondeg, Defined, eval, recEnv, Interp.complex, hkm, hkk,
        ivm1C] at h hn0 hn2 hn5_0 hn5_1 hda hdb ⊢
    tauto
  · simp only [rubi4131r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1)) *
        (((((env "A" * env "b") * env "c") * ((env "m" + env "n") + 1)) +
        (env "B" * (((env "a" * env "c") * env "m") + ((env "b" * env "d") * env "n")))) +
        (((((env "A" * env "b") * env "d") * ((env "m" + env "n") + 1)) +
        (env "B" * (((env "a" * env "d") * env "m") + ((env "b" * env "c") * env "n")))) *
        Complex.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, emmk1, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4131r18Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4131r18Nondeg.result) =
            fun w => ((((((-1) * env "B") * Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (k)) *
            ((env "f" * ((env "m" + env "n") + 1)))⁻¹) +
            (1 * ((env "b" * ((env "m" + env "n") + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi4131r18Nondeg, eval, recEnv, Interp.complex, hkm, hkk, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4131r18Nondeg.body =
        (((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k)) *
        (env "A" + (env "B" * Complex.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4131r18Nondeg, eval, Interp.complex, hkm, hkk]
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
        env "B"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((env "f" * ((env "m" + env "n") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn5_1c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn5_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb3 (by omega)
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        have hden : ((k : ℤ) : ℂ) + 1 ≠ 0 := by exact_mod_cast (show k + 1 ≠ 0 by omega)
        rw [div_eq_iff hden]
        linear_combination (-env "B"*env "d"*Pk*((k : ℤ) : ℂ)) * hP + (0) * hr1
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
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (-env "B"*env "a"*env "b"*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℂ) -
            env "B"*env "b"^2*env "c"*env "f"*Pk*Pm*((m : ℤ) : ℂ) -
            env "B"*env "b"^2*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) -
            env "B"*env "b"^2*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ)) * hP +
            (env "B"*env "c"*env "f"*Pk*Pm*((m : ℤ) : ℂ) +
            env "B"*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ)) * hr1

/-! ## rubi1212r35Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1212r35Nondeg_real : rubi1212r35Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1212r35Nondeg.conditions rubi1212r35Nondeg.body
    rubi1212r35Nondeg.result rubi1212r35Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1212r35Nondeg])
  have hr1 : ((env "c" * (env "d") ^ 2) + ((((-1) * env "b") * env "d") * env "e")) +
      (env "a" * (env "e") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r35Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn4 : (env "m" + env "p") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0)) (by simp [rubi1212r35Nondeg])
  have hc6 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int 0)) (by simp [rubi1212r35Nondeg])
  have hn6_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc6
  have hn6_1 : (env "m" + env "p") + 1 ≠ 0 := by
    have h := hc6
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r35Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r35Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have hb2 : 0 < k := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi1212r35Nondeg])
    have h' : (0 : ℝ) < ((k : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltk : k < 1 → k < 0 := by omega
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1212r35Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1212r35Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r35Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emm2, emmk1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1212r35Nondeg, Defined, eval, recEnv, Interp.real, hkk, emm1, ivm1R,
        iv2R] at h hn0 hn4 hn6_0 hn6_1 ⊢
    tauto
  · simp only [rubi1212r35Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 2) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emm2, emmk1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1212r35Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1212r35Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (k)) *
            ((env "e" * ((env "m" + env "p") + 1)))⁻¹) +
            ((((-1) * env "c") * env "p") * (((env "e") ^ 2 * ((env "m" + env "p") + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi1212r35Nondeg, eval, recEnv, Interp.real, hkk, emm1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1212r35Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1212r35Nondeg, eval, Interp.real, hkm, hkk, iv2R]
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
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((env "e" * ((env "m" + env "p") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn4c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn4
    have hn6_1c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn6_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb2 (by omega)
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
        simp only [e0k]
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        linear_combination (-Pk*((k : ℤ) : ℝ)) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb2 (by omega)
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
        simp only [e0k]
        generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        linear_combination (-env "d"*Pk*Pm*((k : ℤ) : ℝ) - env "e"*Pk*Pm*t*((k : ℤ) : ℝ)) * hr1

set_option maxHeartbeats 1000000 in
theorem rubi1212r35Nondeg_complex : rubi1212r35Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1212r35Nondeg.conditions rubi1212r35Nondeg.body
    rubi1212r35Nondeg.result rubi1212r35Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1212r35Nondeg])
  have hr1 : ((env "c" * (env "d") ^ 2) + ((((-1) * env "b") * env "d") * env "e")) +
      (env "a" * (env "e") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r35Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hn4 : (env "m" + env "p") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0)) (by simp [rubi1212r35Nondeg])
  have hc6 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int 0)) (by simp [rubi1212r35Nondeg])
  have hn6_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc6
  have hn6_1 : (env "m" + env "p") + 1 ≠ 0 := by
    have h := hc6
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r35Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r35Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have hb2 : 0 < k := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi1212r35Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkk, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((k : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltk : k < 1 → k < 0 := by omega
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1212r35Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1212r35Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r35Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emm2, emmk1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1212r35Nondeg, Defined, eval, recEnv, Interp.complex, hkk, emm1, ivm1C,
        iv2C] at h hn0 hn4 hn6_0 hn6_1 ⊢
    tauto
  · simp only [rubi1212r35Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 2) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emm2, emmk1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1212r35Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1212r35Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (k)) *
            ((env "e" * ((env "m" + env "p") + 1)))⁻¹) +
            ((((-1) * env "c") * env "p") * (((env "e") ^ 2 * ((env "m" + env "p") + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi1212r35Nondeg, eval, recEnv, Interp.complex, hkk, emm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1212r35Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1212r35Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
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
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((env "e" * ((env "m" + env "p") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn4c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn4
    have hn6_1c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn6_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb2 (by omega)
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
        simp only [e0k]
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        have hden : ((k : ℤ) : ℂ) + 1 ≠ 0 := by exact_mod_cast (show k + 1 ≠ 0 by omega)
        rw [div_eq_iff hden]
        linear_combination (-Pk*((k : ℤ) : ℂ)) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb2 (by omega)
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
        simp only [e0k]
        generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
        generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        linear_combination (-env "d"*Pk*Pm*((k : ℤ) : ℂ) - env "e"*Pk*Pm*t*((k : ℤ) : ℂ)) * hr1

/-! ## rubi1212r36Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1212r36Nondeg_real : rubi1212r36Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1212r36Nondeg.conditions rubi1212r36Nondeg.body
    rubi1212r36Nondeg.result rubi1212r36Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "c" * (env "d") ^ 2) + (env "a" * (env "e") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r36Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn3 : (env "m" + env "p") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0)) (by simp [rubi1212r36Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int 0)) (by simp [rubi1212r36Nondeg])
  have hn5_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_1 : (env "m" + env "p") + 1 ≠ 0 := by
    have h := hc5
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r36Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r36Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
  have hb1 : 0 < k := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi1212r36Nondeg])
    have h' : (0 : ℝ) < ((k : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkk]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have hltk : k < 1 → k < 0 := by omega
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1212r36Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧ (k < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1212r36Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r36Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, emm2, emmk1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1212r36Nondeg, Defined, eval, recEnv, Interp.real, hkk, emm1, ivm1R,
        iv2R] at h hn3 hn5_0 hn5_1 ⊢
    tauto
  · simp only [rubi1212r36Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 2) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, emm2, emmk1, iv2R, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1212r36Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1212r36Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            ((env "a" + (env "c" * (w) ^ 2))) ^ (k)) * ((env "e" * ((env "m" + env "p") + 1)))⁻¹) +
            ((((-1) * env "c") * env "p") * (((env "e") ^ 2 * ((env "m" + env "p") + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi1212r36Nondeg, eval, recEnv, Interp.real, hkk, emm1, ivm1R, iv2R,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1212r36Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) * ((env "a" + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1212r36Nondeg, eval, Interp.real, hkm, hkk, iv2R]
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
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((env "e" * ((env "m" + env "p") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn3c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn3
    have hn5_1c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn5_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb1 (by omega)
      · subst hm0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
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
        simp only [e0k]
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        linear_combination (-Pk*((k : ℤ) : ℝ)) * hr0
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
        simp only [e0m, e1m, e2m]
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
        simp only [e0k]
        generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        linear_combination (-env "d"*Pk*Pm*((k : ℤ) : ℝ) - env "e"*Pk*Pm*t*((k : ℤ) : ℝ)) * hr0

set_option maxHeartbeats 1000000 in
theorem rubi1212r36Nondeg_complex : rubi1212r36Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1212r36Nondeg.conditions rubi1212r36Nondeg.body
    rubi1212r36Nondeg.result rubi1212r36Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "c" * (env "d") ^ 2) + (env "a" * (env "e") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r36Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hn3 : (env "m" + env "p") + 1 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0)) (by simp [rubi1212r36Nondeg])
  have hc5 :=
      hc (.ne (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int 0)) (by simp [rubi1212r36Nondeg])
  have hn5_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc5
  have hn5_1 : (env "m" + env "p") + 1 ≠ 0 := by
    have h := hc5
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r36Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r36Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
  have hb1 : 0 < k := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi1212r36Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkk, Complex.ext_iff] at h
    have h' : (0 : ℝ) < ((k : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have hltk : k < 1 → k < 0 := by omega
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1212r36Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧ (k < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1212r36Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r36Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, emm2, emmk1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1212r36Nondeg, Defined, eval, recEnv, Interp.complex, hkk, emm1, ivm1C,
        iv2C] at h hn3 hn5_0 hn5_1 ⊢
    tauto
  · simp only [rubi1212r36Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "d" + (env "e" * t))) ^ (m + 2) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, emm2, emmk1, iv2C, sub_eq_add_neg, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1212r36Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1212r36Nondeg.result) =
            fun w => ((((env "d" + (env "e" * w))) ^ (m + 1) *
            ((env "a" + (env "c" * (w) ^ 2))) ^ (k)) * ((env "e" * ((env "m" + env "p") + 1)))⁻¹) +
            ((((-1) * env "c") * env "p") * (((env "e") ^ 2 * ((env "m" + env "p") + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi1212r36Nondeg, eval, recEnv, Interp.complex, hkk, emm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1212r36Nondeg.body =
        ((env "d" + (env "e" * t))) ^ (m) * ((env "a" + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1212r36Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
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
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((env "e" * ((env "m" + env "p") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hn3c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn3
    have hn5_1c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hn5_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact absurd hb1 (by omega)
      · subst hm0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
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
        simp only [e0k]
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        have hden : ((k : ℤ) : ℂ) + 1 ≠ 0 := by exact_mod_cast (show k + 1 ≠ 0 by omega)
        rw [div_eq_iff hden]
        linear_combination (-Pk*((k : ℤ) : ℂ)) * hr0
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
        simp only [e0m, e1m, e2m]
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
        simp only [e0k]
        generalize ((env "d" + (env "e" * t))) ^ (m - 1) = Pm
        generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (k - 1) = Pk
        field_simp
        linear_combination (-env "d"*Pk*Pm*((k : ℤ) : ℂ) - env "e"*Pk*Pm*t*((k : ℤ) : ℂ)) * hr0

/-! ## rubi1213r17Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1213r17Nondeg_real : rubi1213r17Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1213r17Nondeg.conditions rubi1213r17Nondeg.body
    rubi1213r17Nondeg.result rubi1213r17Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1213r17Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 0)) (by simp [rubi1213r17Nondeg])
  have hn2_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_2 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc2
  have hn2_3 : (2 * env "p") + 3 ≠ 0 := by
    have h := hc2
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    tauto
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r17Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb1 : -1 < m := by
    have h := hc (.gt (.var "p") (.int (-1))) (by simp [rubi1213r17Nondeg])
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1213r17Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r17Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r17Nondeg, Defined, eval, recEnv, Interp.real, emm1, ivm1R,
        iv2R] at h hn0 hn2_1 hn2_2 hn2_3 ⊢
    tauto
  · simp only [rubi1213r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m)) t :=
        by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1213r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r17Nondeg.result) =
            fun w => ((((-1) *
            (((((env "b" * env "e") * env "g") * (env "p" + 2)) +
            ((((-1) * env "c") * ((env "e" * env "f") + (env "d" * env "g"))) *
            ((2 * env "p") + 3))) +
            ((((((-2) * env "c") * env "e") * env "g") * (env "p" + 1)) * w))) *
            (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (m + 1)) *
            ((((2 * (env "c") ^ 2) * (env "p" + 1)) * ((2 * env "p") + 3)))⁻¹) +
            (((((((env "b") ^ 2 * env "e") * env "g") * (env "p" + 2)) +
            (((((-2) * env "a") * env "c") * env "e") * env "g")) +
            ((env "c" *
            ((((2 * env "c") * env "d") * env "f") +
            (((-1) * env "b") * ((env "e" * env "f") + (env "d" * env "g"))))) *
            ((2 * env "p") + 3))) * (((2 * (env "c") ^ 2) * ((2 * env "p") + 3)))⁻¹) * Φ "I1" w :=
            by
      funext w
      simp [rubi1213r17Nondeg, eval, recEnv, Interp.real, emm1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1213r17Nondeg.body =
        ((env "d" + (env "e" * t)) * (env "f" + (env "g" * t))) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m) := by
      simp [rubi1213r17Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul ((hasDerivAt_const t (((((env "b" * env "e") *
        env "g") * (env "p" + 2)) +
        ((((-1) * env "c") * ((env "e" * env "f") + (env "d" * env "g"))) *
        ((2 * env "p") + 3))))).add ((hasDerivAt_const t ((((((-2) * env "c") * env "e") *
        env "g") *
        (env "p" + 1)))).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((((2 * (env "c") ^ 2) * (env "p" + 1)) * ((2 * env "p") + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    have hn2_3c : (2 * ((m : ℤ) : ℝ)) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_3
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      field_simp
      ring
    · have hdmm : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ m =
          (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
          (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 1) =
          (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
          (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 2) =
          (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
          (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m]
      generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
      have hdn0 : ((m : ℤ) : ℝ) * 2 + 3 ≠ 0 := fun h0 => hn2_3c (by linear_combination (1) * h0)
      field_simp
      ring

set_option maxHeartbeats 1000000 in
theorem rubi1213r17Nondeg_complex : rubi1213r17Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1213r17Nondeg.conditions rubi1213r17Nondeg.body
    rubi1213r17Nondeg.result rubi1213r17Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1213r17Nondeg])
  have hc2 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 0)) (by simp [rubi1213r17Nondeg])
  have hn2_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc2
  have hn2_2 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc2
  have hn2_3 : (2 * env "p") + 3 ≠ 0 := by
    have h := hc2
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    tauto
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r17Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb1 : -1 < m := by
    have h := hc (.gt (.var "p") (.int (-1))) (by simp [rubi1213r17Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1213r17Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r17Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r17Nondeg, Defined, eval, recEnv, Interp.complex, emm1, ivm1C,
        iv2C] at h hn0 hn2_1 hn2_2 hn2_3 ⊢
    tauto
  · simp only [rubi1213r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m)) t :=
        by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1213r17Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r17Nondeg.result) =
            fun w => ((((-1) *
            (((((env "b" * env "e") * env "g") * (env "p" + 2)) +
            ((((-1) * env "c") * ((env "e" * env "f") + (env "d" * env "g"))) *
            ((2 * env "p") + 3))) +
            ((((((-2) * env "c") * env "e") * env "g") * (env "p" + 1)) * w))) *
            (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (m + 1)) *
            ((((2 * (env "c") ^ 2) * (env "p" + 1)) * ((2 * env "p") + 3)))⁻¹) +
            (((((((env "b") ^ 2 * env "e") * env "g") * (env "p" + 2)) +
            (((((-2) * env "a") * env "c") * env "e") * env "g")) +
            ((env "c" *
            ((((2 * env "c") * env "d") * env "f") +
            (((-1) * env "b") * ((env "e" * env "f") + (env "d" * env "g"))))) *
            ((2 * env "p") + 3))) * (((2 * (env "c") ^ 2) * ((2 * env "p") + 3)))⁻¹) * Φ "I1" w :=
            by
      funext w
      simp [rubi1213r17Nondeg, eval, recEnv, Interp.complex, emm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1213r17Nondeg.body =
        ((env "d" + (env "e" * t)) * (env "f" + (env "g" * t))) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m) := by
      simp [rubi1213r17Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul ((hasDerivAt_const t (((((env "b" * env "e") *
        env "g") * (env "p" + 2)) +
        ((((-1) * env "c") * ((env "e" * env "f") + (env "d" * env "g"))) *
        ((2 * env "p") + 3))))).add ((hasDerivAt_const t ((((((-2) * env "c") * env "e") *
        env "g") *
        (env "p" + 1)))).mul (hasDerivAt_id' t)))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((((2 * (env "c") ^ 2) * (env "p" + 1)) * ((2 * env "p") + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn2_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_2
    have hn2_3c : (2 * ((m : ℤ) : ℂ)) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn2_3
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      field_simp
      ring
    · have hdmm : ((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ m =
          (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
          (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 1) =
          (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
          (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m + 2) =
          (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) *
          (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m]
      generalize (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
      have hdn0 : ((m : ℤ) : ℂ) * 2 + 3 ≠ 0 := fun h0 => hn2_3c (by linear_combination (1) * h0)
      field_simp
      ring

/-! ## rubi1213r18Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1213r18Nondeg_real : rubi1213r18Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1213r18Nondeg.conditions rubi1213r18Nondeg.body
    rubi1213r18Nondeg.result rubi1213r18Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 0)) (by simp [rubi1213r18Nondeg])
  have hn1_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_2 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_3 : (2 * env "p") + 3 ≠ 0 := by
    have h := hc1
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r18Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb0 : -1 < m := by
    have h := hc (.gt (.var "p") (.int (-1))) (by simp [rubi1213r18Nondeg])
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1213r18Nondeg.body →
      (m < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r18Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r18Nondeg, Defined, eval, recEnv, Interp.real, emm1, ivm1R,
        iv2R] at h hn1_1 hn1_2 hn1_3 ⊢
    tauto
  · simp only [rubi1213r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" + (env "c" * (t) ^ 2))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1213r18Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r18Nondeg.result) =
            fun w => ((((((env "e" * env "f") + (env "d" * env "g")) * ((2 * env "p") + 3)) +
            ((((2 * env "e") * env "g") * (env "p" + 1)) * w)) *
            ((env "a" + (env "c" * (w) ^ 2))) ^ (m + 1)) *
            ((((2 * env "c") * (env "p" + 1)) * ((2 * env "p") + 3)))⁻¹) +
            (((-1) *
            (((env "a" * env "e") * env "g") +
            (((((-1) * env "c") * env "d") * env "f") * ((2 * env "p") + 3)))) *
            ((env "c" * ((2 * env "p") + 3)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1213r18Nondeg, eval, recEnv, Interp.real, emm1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1213r18Nondeg.body =
        ((env "d" + (env "e" * t)) * (env "f" + (env "g" * t))) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (m) := by
      simp [rubi1213r18Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((((env "e" * env "f") + (env "d" * env "g")) *
        ((2 * env "p") + 3)))).add ((hasDerivAt_const t ((((2 * env "e") * env "g") *
        (env "p" + 1)))).mul (hasDerivAt_id' t))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((((2 * env "c") * (env "p" + 1)) * ((2 * env "p") + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn1_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_2
    have hn1_3c : (2 * ((m : ℤ) : ℝ)) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_3
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      field_simp
      ring
    · have hdmm : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "a" + (env "c" * (t) ^ 2))) ^ m =
          ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 := by
        have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1) =
          ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 := by
        have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 2) =
          ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 := by
        have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m]
      generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
      field_simp
      ring

set_option maxHeartbeats 1000000 in
theorem rubi1213r18Nondeg_complex : rubi1213r18Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1213r18Nondeg.conditions rubi1213r18Nondeg.body
    rubi1213r18Nondeg.result rubi1213r18Nondeg.integrals
  intro env hc t hF
  have hc1 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 0)) (by simp [rubi1213r18Nondeg])
  have hn1_1 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_2 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc1
  have hn1_3 : (2 * env "p") + 3 ≠ 0 := by
    have h := hc1
    simp [Cond.Holds, Defined, eval] at h
    tauto
  rcases hkm : intValue? (env "p") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r18Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb0 : -1 < m := by
    have h := hc (.gt (.var "p") (.int (-1))) (by simp [rubi1213r18Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : (-1 : ℝ) < ((m : ℤ) : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1213r18Nondeg.body →
      (m < 0 → (env "a" + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r18Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r18Nondeg, Defined, eval, recEnv, Interp.complex, emm1, ivm1C,
        iv2C] at h hn1_1 hn1_2 hn1_3 ⊢
    tauto
  · simp only [rubi1213r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "a" + (env "c" * (t) ^ 2))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1213r18Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r18Nondeg.result) =
            fun w => ((((((env "e" * env "f") + (env "d" * env "g")) * ((2 * env "p") + 3)) +
            ((((2 * env "e") * env "g") * (env "p" + 1)) * w)) *
            ((env "a" + (env "c" * (w) ^ 2))) ^ (m + 1)) *
            ((((2 * env "c") * (env "p" + 1)) * ((2 * env "p") + 3)))⁻¹) +
            (((-1) *
            (((env "a" * env "e") * env "g") +
            (((((-1) * env "c") * env "d") * env "f") * ((2 * env "p") + 3)))) *
            ((env "c" * ((2 * env "p") + 3)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi1213r18Nondeg, eval, recEnv, Interp.complex, emm1, ivm1C, iv2C,
          -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1213r18Nondeg.body =
        ((env "d" + (env "e" * t)) * (env "f" + (env "g" * t))) *
        ((env "a" + (env "c" * (t) ^ 2))) ^ (m) := by
      simp [rubi1213r18Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    obtain hBm0 := hD t hF.self_of_nhds
    have hdzm : ∀ E : ℤ, (E < 0 → m < 0) → (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hBm0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((((env "e" * env "f") + (env "d" * env "g")) *
        ((2 * env "p") + 3)))).add ((hasDerivAt_const t ((((2 * env "e") * env "g") *
        (env "p" + 1)))).mul (hasDerivAt_id' t))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t (((((2 * env "c") * (env "p" + 1)) * ((2 * env "p") + 3)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      add_sub_cancel_right]
    have hn1_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_2
    have hn1_3c : (2 * ((m : ℤ) : ℂ)) + 3 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn1_3
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero]
      field_simp
      ring
    · have hdmm : (env "a" + (env "c" * (t) ^ 2)) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hBm0 hm)
        · exact Or.inr (by omega)
      have e0m : ((env "a" + (env "c" * (t) ^ 2))) ^ m =
          ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 1 := by
        have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 1 hdmm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 1) =
          ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 2 := by
        have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 2 hdmm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2m : ((env "a" + (env "c" * (t) ^ 2))) ^ (m + 2) =
          ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) * ((env "a" + (env "c" * (t) ^ 2))) ^ 3 := by
        have := zsplit ((env "a" + (env "c" * (t) ^ 2))) (m - 1) 3 hdmm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0m, e1m]
      generalize ((env "a" + (env "c" * (t) ^ 2))) ^ (m - 1) = Pm
      field_simp
      ring

/-! ## rubi1213r5Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi1213r5Nondeg_real : rubi1213r5Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi1213r5Nondeg.conditions rubi1213r5Nondeg.body
    rubi1213r5Nondeg.result
  intro env hc t hF
  have hr0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1213r5Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hr1 : (env "m" + (2 * env "p")) + 3 - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1213r5Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hr2 : ((2 * env "c") * env "f") + (((-1) * env "b") * env "g") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))) (.int 0)) (by simp [rubi1213r5Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g")))) (.int 0)) (by simp [rubi1213r5Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : (env "e" * env "f") + (((-1) * env "d") * env "g") ≠ 0 := by
    have h := hc3
    simp [Cond.Holds, Defined, eval] at h
    intro h0; apply h.2; linear_combination h0
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (1) * hr0 - (-4*env "c") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn3_0 (by linear_combination (1) * hzb)
  have hdc : env "c" ≠ 0 := by
    intro hzc
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (1) * hr0 - (-4*env "a") * hzc
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn3_0 (by linear_combination (1) * hzb)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r5Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r5Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1213r5Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r5Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r5Nondeg, Defined, eval, Interp.real, emm1, emk1, ivm1R,
        iv2R] at h hn3_0 hn3_1 hn3_2 hda hdc ⊢
    tauto
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w)
        rubi1213r5Nondeg.result) =
            fun w => ((((((-1) * env "f") * env "g") * ((env "d" + (env "e" * w))) ^ (m + 1)) *
            (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (k + 1)) *
            (((env "b" * (env "p" + 1)) *
            ((env "e" * env "f") + (((-1) * env "d") * env "g"))))⁻¹) := by
      funext w
      simp [rubi1213r5Nondeg, eval, Interp.real, emm1, emk1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1213r5Nondeg.body =
        (((env "d" + (env "e" * t))) ^ (m) * (env "f" + (env "g" * t))) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1213r5Nondeg, eval, Interp.real, hkm, hkk, iv2R]
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
    refine ((((hasDerivAt_const t ((((-1) * env "f") *
        env "g"))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t ((((env "b" * (env "p" + 1)) * ((env "e" * env "f") + (((-1) * env "d") * env "g"))))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hr1c : (((m : ℤ) : ℝ) + (2 * ((k : ℤ) : ℝ))) + 3 - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hr1
    have hn3_1c : ((k : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        field_simp
        have hden : env "f" * env "e" + -(env "g" * env "d") ≠ 0 :=
            fun h0 => hn3_2 (by linear_combination (1) * h0)
        rw [div_eq_iff hden]
        linear_combination (0) * hr0 +
            (-env "a"*env "e"*env "f"*env "g"/3 + env "b"*env "d"*env "g"^2*t/3 -
            env "b"*env "e"*env "f"^2/3 - env "b"*env "e"*env "f"*env "g"*t -
            2*env "c"*env "d"*env "f"*env "g"*t/3 - env "c"*env "e"*env "f"*env "g"*t^2) * hr1c +
            (0) * hr2
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
        field_simp
        have hden : env "f" * env "e" + -(env "g" * env "d") ≠ 0 :=
            fun h0 => hn3_2 (by linear_combination (1) * h0)
        rw [div_eq_iff hden]
        refine mul_left_cancel₀ hn3_0 ?_
        linear_combination (env "a"*env "e"*env "f"^2*Pk/2 +
            env "b"*env "d"*env "f"*env "g"*Pk*t*((k : ℤ) : ℝ)/2 +
            3*env "b"*env "d"*env "f"*env "g"*Pk*t/4 + env "b"*env "e"*env "f"^2*Pk*t/2 +
            env "b"*env "e"*env "f"*env "g"*Pk*t^2*((k : ℤ) : ℝ)/2 +
            env "b"*env "e"*env "f"*env "g"*Pk*t^2) * hr0 +
            (env "a"*env "b"^2*env "d"*env "g"^2*Pk*t/2 -
            env "a"*env "b"^2*env "e"*env "f"^2*Pk/2 -
            env "a"*env "b"^2*env "e"*env "f"*env "g"*Pk*t -
            env "b"^3*env "d"*env "f"*env "g"*Pk*t/4 + env "b"^3*env "d"*env "g"^2*Pk*t^2/2 -
            env "b"^3*env "e"*env "f"^2*Pk*t/2 - 5*env "b"^3*env "e"*env "f"*env "g"*Pk*t^2/4 -
            env "b"^2*env "c"*env "d"*env "f"*env "g"*Pk*t^2 +
            env "b"^2*env "c"*env "d"*env "g"^2*Pk*t^3/2 -
            env "b"^2*env "c"*env "e"*env "f"^2*Pk*t^2/2 -
            2*env "b"^2*env "c"*env "e"*env "f"*env "g"*Pk*t^3 -
            env "b"*env "c"^2*env "d"*env "f"*env "g"*Pk*t^3 -
            env "b"*env "c"^2*env "e"*env "f"*env "g"*Pk*t^4) * hr1c +
            (env "a"^2*env "e"*env "f"*Pk + env "a"*env "b"*env "d"*env "g"*Pk*t/2 +
            env "a"*env "b"*env "e"*env "f"*Pk*t + env "b"^2*env "d"*env "g"*Pk*t^2/2 +
            env "b"^2*env "e"*env "f"*Pk*t^2/4 + env "b"*env "c"*env "d"*env "g"*Pk*t^3/2) * hr2
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
        field_simp
        have hden : env "f" * env "e" + -(env "g" * env "d") ≠ 0 :=
            fun h0 => hn3_2 (by linear_combination (1) * h0)
        rw [div_eq_iff hden]
        refine mul_left_cancel₀ hn3_0 ?_
        linear_combination (-env "d"*env "e"*env "f"^2*Pm - env "e"^2*env "f"^2*Pm*t) * hr0 +
            (-env "a"*env "b"*env "d"*env "e"*env "f"*env "g"*Pm -
            env "a"*env "b"*env "e"^2*env "f"*env "g"*Pm*t -
            env "b"^2*env "d"*env "e"*env "f"*env "g"*Pm*t -
            env "b"^2*env "e"^2*env "f"*env "g"*Pm*t^2 -
            env "b"*env "c"*env "d"*env "e"*env "f"*env "g"*Pm*t^2 -
            env "b"*env "c"*env "e"^2*env "f"*env "g"*Pm*t^3) * hr1c +
            (-2*env "a"*env "d"*env "e"*env "f"*Pm - 2*env "a"*env "e"^2*env "f"*Pm*t -
            env "b"*env "d"^2*env "g"*Pm*t - env "b"*env "d"*env "e"*env "g"*Pm*t^2) * hr2
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
        have hdn0 : env "e" * env "f" + -(env "d" * env "g") ≠ 0 :=
            fun h0 => hn3_2 (by linear_combination (1) * h0)
        field_simp
        refine mul_left_cancel₀ hn3_0 ?_
        linear_combination (env "a"*env "d"*env "e"*env "f"^2*Pk*Pm*((m : ℤ) : ℝ)/2 +
            env "a"*env "d"*env "e"*env "f"^2*Pk*Pm/2 +
            env "a"*env "e"^2*env "f"^2*Pk*Pm*t*((m : ℤ) : ℝ)/2 +
            env "a"*env "e"^2*env "f"^2*Pk*Pm*t/2 +
            env "b"*env "d"^2*env "f"*env "g"*Pk*Pm*t*((k : ℤ) : ℝ)/2 +
            env "b"*env "d"^2*env "f"*env "g"*Pk*Pm*t*((m : ℤ) : ℝ)/4 +
            3*env "b"*env "d"^2*env "f"*env "g"*Pk*Pm*t/4 +
            env "b"*env "d"*env "e"*env "f"^2*Pk*Pm*t*((m : ℤ) : ℝ)/2 +
            env "b"*env "d"*env "e"*env "f"^2*Pk*Pm*t/2 +
            env "b"*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t^2*((k : ℤ) : ℝ) +
            3*env "b"*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t^2*((m : ℤ) : ℝ)/4 +
            7*env "b"*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t^2/4 +
            env "b"*env "e"^2*env "f"^2*Pk*Pm*t^2*((m : ℤ) : ℝ)/2 +
            env "b"*env "e"^2*env "f"^2*Pk*Pm*t^2/2 +
            env "b"*env "e"^2*env "f"*env "g"*Pk*Pm*t^3*((k : ℤ) : ℝ)/2 +
            env "b"*env "e"^2*env "f"*env "g"*Pk*Pm*t^3*((m : ℤ) : ℝ)/2 +
            env "b"*env "e"^2*env "f"*env "g"*Pk*Pm*t^3) * hr0 +
            (env "a"*env "b"^2*env "d"^2*env "g"^2*Pk*Pm*t/2 -
            env "a"*env "b"^2*env "d"*env "e"*env "f"^2*Pk*Pm/2 -
            env "a"*env "b"^2*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t +
            env "a"*env "b"^2*env "d"*env "e"*env "g"^2*Pk*Pm*t^2/2 -
            env "a"*env "b"^2*env "e"^2*env "f"^2*Pk*Pm*t/2 -
            env "a"*env "b"^2*env "e"^2*env "f"*env "g"*Pk*Pm*t^2 -
            env "b"^3*env "d"^2*env "f"*env "g"*Pk*Pm*t/4 +
            env "b"^3*env "d"^2*env "g"^2*Pk*Pm*t^2/2 -
            env "b"^3*env "d"*env "e"*env "f"^2*Pk*Pm*t/2 -
            3*env "b"^3*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t^2/2 +
            env "b"^3*env "d"*env "e"*env "g"^2*Pk*Pm*t^3/2 -
            env "b"^3*env "e"^2*env "f"^2*Pk*Pm*t^2/2 -
            5*env "b"^3*env "e"^2*env "f"*env "g"*Pk*Pm*t^3/4 -
            env "b"^2*env "c"*env "d"^2*env "f"*env "g"*Pk*Pm*t^2 +
            env "b"^2*env "c"*env "d"^2*env "g"^2*Pk*Pm*t^3/2 -
            env "b"^2*env "c"*env "d"*env "e"*env "f"^2*Pk*Pm*t^2/2 -
            3*env "b"^2*env "c"*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t^3 +
            env "b"^2*env "c"*env "d"*env "e"*env "g"^2*Pk*Pm*t^4/2 -
            env "b"^2*env "c"*env "e"^2*env "f"^2*Pk*Pm*t^3/2 -
            2*env "b"^2*env "c"*env "e"^2*env "f"*env "g"*Pk*Pm*t^4 -
            env "b"*env "c"^2*env "d"^2*env "f"*env "g"*Pk*Pm*t^3 -
            2*env "b"*env "c"^2*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t^4 -
            env "b"*env "c"^2*env "e"^2*env "f"*env "g"*Pk*Pm*t^5) * hr1c +
            (env "a"^2*env "d"*env "e"*env "f"*Pk*Pm*((m : ℤ) : ℝ) +
            env "a"^2*env "d"*env "e"*env "f"*Pk*Pm +
            env "a"^2*env "e"^2*env "f"*Pk*Pm*t*((m : ℤ) : ℝ) +
            env "a"^2*env "e"^2*env "f"*Pk*Pm*t +
            env "a"*env "b"*env "d"^2*env "g"*Pk*Pm*t*((m : ℤ) : ℝ)/2 +
            env "a"*env "b"*env "d"^2*env "g"*Pk*Pm*t/2 +
            env "a"*env "b"*env "d"*env "e"*env "f"*Pk*Pm*t*((m : ℤ) : ℝ) +
            env "a"*env "b"*env "d"*env "e"*env "f"*Pk*Pm*t +
            env "a"*env "b"*env "d"*env "e"*env "g"*Pk*Pm*t^2*((m : ℤ) : ℝ)/2 +
            env "a"*env "b"*env "d"*env "e"*env "g"*Pk*Pm*t^2/2 +
            env "a"*env "b"*env "e"^2*env "f"*Pk*Pm*t^2*((m : ℤ) : ℝ) +
            env "a"*env "b"*env "e"^2*env "f"*Pk*Pm*t^2 +
            env "b"^2*env "d"^2*env "g"*Pk*Pm*t^2*((m : ℤ) : ℝ)/2 +
            env "b"^2*env "d"^2*env "g"*Pk*Pm*t^2/2 +
            env "b"^2*env "d"*env "e"*env "f"*Pk*Pm*t^2*((m : ℤ) : ℝ)/4 +
            env "b"^2*env "d"*env "e"*env "f"*Pk*Pm*t^2/4 +
            env "b"^2*env "d"*env "e"*env "g"*Pk*Pm*t^3*((m : ℤ) : ℝ)/2 +
            env "b"^2*env "d"*env "e"*env "g"*Pk*Pm*t^3/2 +
            env "b"^2*env "e"^2*env "f"*Pk*Pm*t^3*((m : ℤ) : ℝ)/4 +
            env "b"^2*env "e"^2*env "f"*Pk*Pm*t^3/4 +
            env "b"*env "c"*env "d"^2*env "g"*Pk*Pm*t^3*((m : ℤ) : ℝ)/2 +
            env "b"*env "c"*env "d"^2*env "g"*Pk*Pm*t^3/2 +
            env "b"*env "c"*env "d"*env "e"*env "g"*Pk*Pm*t^4*((m : ℤ) : ℝ)/2 +
            env "b"*env "c"*env "d"*env "e"*env "g"*Pk*Pm*t^4/2) * hr2

set_option maxHeartbeats 1000000 in
theorem rubi1213r5Nondeg_complex : rubi1213r5Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi1213r5Nondeg.conditions rubi1213r5Nondeg.body
    rubi1213r5Nondeg.result
  intro env hc t hF
  have hr0 : (env "b") ^ 2 + (((-4) * env "a") * env "c") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1213r5Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hr1 : (env "m" + (2 * env "p")) + 3 - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1213r5Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hr2 : ((2 * env "c") * env "f") + (((-1) * env "b") * env "g") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))) (.int 0)) (by simp [rubi1213r5Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g")))) (.int 0)) (by simp [rubi1213r5Nondeg])
  have hn3_0 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "p" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : (env "e" * env "f") + (((-1) * env "d") * env "g") ≠ 0 := by
    have h := hc3
    simp [Cond.Holds, Defined, eval] at h
    intro h0; apply h.2; linear_combination h0
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (1) * hr0 - (-4*env "c") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn3_0 (by linear_combination (1) * hzb)
  have hdc : env "c" ≠ 0 := by
    intro hzc
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (1) * hr0 - (-4*env "a") * hzc
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn3_0 (by linear_combination (1) * hzb)
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r5Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r5Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1213r5Nondeg.body →
      (m < 0 → (env "d" + (env "e" * w)) ≠ 0) ∧
          (k < 0 → ((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2)) ≠ 0) := by
    intro w h
    simp [rubi1213r5Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi1213r5Nondeg, Defined, eval, Interp.complex, emm1, emk1, ivm1C,
        iv2C] at h hn3_0 hn3_1 hn3_2 hda hdc ⊢
    tauto
  · have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi1213r5Nondeg.result) =
            fun w => ((((((-1) * env "f") * env "g") * ((env "d" + (env "e" * w))) ^ (m + 1)) *
            (((env "a" + (env "b" * w)) + (env "c" * (w) ^ 2))) ^ (k + 1)) *
            (((env "b" * (env "p" + 1)) *
            ((env "e" * env "f") + (((-1) * env "d") * env "g"))))⁻¹) := by
      funext w
      simp [rubi1213r5Nondeg, eval, Interp.complex, emm1, emk1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1213r5Nondeg.body =
        (((env "d" + (env "e" * t))) ^ (m) * (env "f" + (env "g" * t))) *
        (((env "a" + (env "b" * t)) + (env "c" * (t) ^ 2))) ^ (k) := by
      simp [rubi1213r5Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
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
    refine ((((hasDerivAt_const t ((((-1) * env "f") *
        env "g"))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m +
        1) _ (hdzm (m +
        1) (by omega))) ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul (hasDerivAt_id' t))).add ((hasDerivAt_const t (env "c")).mul ((hasDerivAt_id' t).pow 2))))).mul (hasDerivAt_const t ((((env "b" * (env "p" + 1)) * ((env "e" * env "f") + (((-1) * env "d") * env "g"))))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, add_sub_cancel_right]
    have hr1c : (((m : ℤ) : ℂ) + (2 * ((k : ℤ) : ℂ))) + 3 - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hr1
    have hn3_1c : ((k : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkk]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        field_simp
        have hden : env "f" * env "e" + -(env "g" * env "d") ≠ 0 :=
            fun h0 => hn3_2 (by linear_combination (1) * h0)
        rw [div_eq_iff hden]
        linear_combination (0) * hr0 +
            (-env "a"*env "e"*env "f"*env "g"/3 + env "b"*env "d"*env "g"^2*t/3 -
            env "b"*env "e"*env "f"^2/3 - env "b"*env "e"*env "f"*env "g"*t -
            2*env "c"*env "d"*env "f"*env "g"*t/3 - env "c"*env "e"*env "f"*env "g"*t^2) * hr1c +
            (0) * hr2
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
        field_simp
        have hden : env "f" * env "e" + -(env "g" * env "d") ≠ 0 :=
            fun h0 => hn3_2 (by linear_combination (1) * h0)
        rw [div_eq_iff hden]
        refine mul_left_cancel₀ hn3_0 ?_
        linear_combination (env "a"*env "e"*env "f"^2*Pk/2 +
            env "b"*env "d"*env "f"*env "g"*Pk*t*((k : ℤ) : ℂ)/2 +
            3*env "b"*env "d"*env "f"*env "g"*Pk*t/4 + env "b"*env "e"*env "f"^2*Pk*t/2 +
            env "b"*env "e"*env "f"*env "g"*Pk*t^2*((k : ℤ) : ℂ)/2 +
            env "b"*env "e"*env "f"*env "g"*Pk*t^2) * hr0 +
            (env "a"*env "b"^2*env "d"*env "g"^2*Pk*t/2 -
            env "a"*env "b"^2*env "e"*env "f"^2*Pk/2 -
            env "a"*env "b"^2*env "e"*env "f"*env "g"*Pk*t -
            env "b"^3*env "d"*env "f"*env "g"*Pk*t/4 + env "b"^3*env "d"*env "g"^2*Pk*t^2/2 -
            env "b"^3*env "e"*env "f"^2*Pk*t/2 - 5*env "b"^3*env "e"*env "f"*env "g"*Pk*t^2/4 -
            env "b"^2*env "c"*env "d"*env "f"*env "g"*Pk*t^2 +
            env "b"^2*env "c"*env "d"*env "g"^2*Pk*t^3/2 -
            env "b"^2*env "c"*env "e"*env "f"^2*Pk*t^2/2 -
            2*env "b"^2*env "c"*env "e"*env "f"*env "g"*Pk*t^3 -
            env "b"*env "c"^2*env "d"*env "f"*env "g"*Pk*t^3 -
            env "b"*env "c"^2*env "e"*env "f"*env "g"*Pk*t^4) * hr1c +
            (env "a"^2*env "e"*env "f"*Pk + env "a"*env "b"*env "d"*env "g"*Pk*t/2 +
            env "a"*env "b"*env "e"*env "f"*Pk*t + env "b"^2*env "d"*env "g"*Pk*t^2/2 +
            env "b"^2*env "e"*env "f"*Pk*t^2/4 + env "b"*env "c"*env "d"*env "g"*Pk*t^3/2) * hr2
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
        field_simp
        have hden : env "f" * env "e" + -(env "g" * env "d") ≠ 0 :=
            fun h0 => hn3_2 (by linear_combination (1) * h0)
        rw [div_eq_iff hden]
        refine mul_left_cancel₀ hn3_0 ?_
        linear_combination (-env "d"*env "e"*env "f"^2*Pm - env "e"^2*env "f"^2*Pm*t) * hr0 +
            (-env "a"*env "b"*env "d"*env "e"*env "f"*env "g"*Pm -
            env "a"*env "b"*env "e"^2*env "f"*env "g"*Pm*t -
            env "b"^2*env "d"*env "e"*env "f"*env "g"*Pm*t -
            env "b"^2*env "e"^2*env "f"*env "g"*Pm*t^2 -
            env "b"*env "c"*env "d"*env "e"*env "f"*env "g"*Pm*t^2 -
            env "b"*env "c"*env "e"^2*env "f"*env "g"*Pm*t^3) * hr1c +
            (-2*env "a"*env "d"*env "e"*env "f"*Pm - 2*env "a"*env "e"^2*env "f"*Pm*t -
            env "b"*env "d"^2*env "g"*Pm*t - env "b"*env "d"*env "e"*env "g"*Pm*t^2) * hr2
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
        have hdn0 : env "e" * env "f" + -(env "d" * env "g") ≠ 0 :=
            fun h0 => hn3_2 (by linear_combination (1) * h0)
        field_simp
        refine mul_left_cancel₀ hn3_0 ?_
        linear_combination (env "a"*env "d"*env "e"*env "f"^2*Pk*Pm*((m : ℤ) : ℂ)/2 +
            env "a"*env "d"*env "e"*env "f"^2*Pk*Pm/2 +
            env "a"*env "e"^2*env "f"^2*Pk*Pm*t*((m : ℤ) : ℂ)/2 +
            env "a"*env "e"^2*env "f"^2*Pk*Pm*t/2 +
            env "b"*env "d"^2*env "f"*env "g"*Pk*Pm*t*((k : ℤ) : ℂ)/2 +
            env "b"*env "d"^2*env "f"*env "g"*Pk*Pm*t*((m : ℤ) : ℂ)/4 +
            3*env "b"*env "d"^2*env "f"*env "g"*Pk*Pm*t/4 +
            env "b"*env "d"*env "e"*env "f"^2*Pk*Pm*t*((m : ℤ) : ℂ)/2 +
            env "b"*env "d"*env "e"*env "f"^2*Pk*Pm*t/2 +
            env "b"*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t^2*((k : ℤ) : ℂ) +
            3*env "b"*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t^2*((m : ℤ) : ℂ)/4 +
            7*env "b"*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t^2/4 +
            env "b"*env "e"^2*env "f"^2*Pk*Pm*t^2*((m : ℤ) : ℂ)/2 +
            env "b"*env "e"^2*env "f"^2*Pk*Pm*t^2/2 +
            env "b"*env "e"^2*env "f"*env "g"*Pk*Pm*t^3*((k : ℤ) : ℂ)/2 +
            env "b"*env "e"^2*env "f"*env "g"*Pk*Pm*t^3*((m : ℤ) : ℂ)/2 +
            env "b"*env "e"^2*env "f"*env "g"*Pk*Pm*t^3) * hr0 +
            (env "a"*env "b"^2*env "d"^2*env "g"^2*Pk*Pm*t/2 -
            env "a"*env "b"^2*env "d"*env "e"*env "f"^2*Pk*Pm/2 -
            env "a"*env "b"^2*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t +
            env "a"*env "b"^2*env "d"*env "e"*env "g"^2*Pk*Pm*t^2/2 -
            env "a"*env "b"^2*env "e"^2*env "f"^2*Pk*Pm*t/2 -
            env "a"*env "b"^2*env "e"^2*env "f"*env "g"*Pk*Pm*t^2 -
            env "b"^3*env "d"^2*env "f"*env "g"*Pk*Pm*t/4 +
            env "b"^3*env "d"^2*env "g"^2*Pk*Pm*t^2/2 -
            env "b"^3*env "d"*env "e"*env "f"^2*Pk*Pm*t/2 -
            3*env "b"^3*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t^2/2 +
            env "b"^3*env "d"*env "e"*env "g"^2*Pk*Pm*t^3/2 -
            env "b"^3*env "e"^2*env "f"^2*Pk*Pm*t^2/2 -
            5*env "b"^3*env "e"^2*env "f"*env "g"*Pk*Pm*t^3/4 -
            env "b"^2*env "c"*env "d"^2*env "f"*env "g"*Pk*Pm*t^2 +
            env "b"^2*env "c"*env "d"^2*env "g"^2*Pk*Pm*t^3/2 -
            env "b"^2*env "c"*env "d"*env "e"*env "f"^2*Pk*Pm*t^2/2 -
            3*env "b"^2*env "c"*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t^3 +
            env "b"^2*env "c"*env "d"*env "e"*env "g"^2*Pk*Pm*t^4/2 -
            env "b"^2*env "c"*env "e"^2*env "f"^2*Pk*Pm*t^3/2 -
            2*env "b"^2*env "c"*env "e"^2*env "f"*env "g"*Pk*Pm*t^4 -
            env "b"*env "c"^2*env "d"^2*env "f"*env "g"*Pk*Pm*t^3 -
            2*env "b"*env "c"^2*env "d"*env "e"*env "f"*env "g"*Pk*Pm*t^4 -
            env "b"*env "c"^2*env "e"^2*env "f"*env "g"*Pk*Pm*t^5) * hr1c +
            (env "a"^2*env "d"*env "e"*env "f"*Pk*Pm*((m : ℤ) : ℂ) +
            env "a"^2*env "d"*env "e"*env "f"*Pk*Pm +
            env "a"^2*env "e"^2*env "f"*Pk*Pm*t*((m : ℤ) : ℂ) +
            env "a"^2*env "e"^2*env "f"*Pk*Pm*t +
            env "a"*env "b"*env "d"^2*env "g"*Pk*Pm*t*((m : ℤ) : ℂ)/2 +
            env "a"*env "b"*env "d"^2*env "g"*Pk*Pm*t/2 +
            env "a"*env "b"*env "d"*env "e"*env "f"*Pk*Pm*t*((m : ℤ) : ℂ) +
            env "a"*env "b"*env "d"*env "e"*env "f"*Pk*Pm*t +
            env "a"*env "b"*env "d"*env "e"*env "g"*Pk*Pm*t^2*((m : ℤ) : ℂ)/2 +
            env "a"*env "b"*env "d"*env "e"*env "g"*Pk*Pm*t^2/2 +
            env "a"*env "b"*env "e"^2*env "f"*Pk*Pm*t^2*((m : ℤ) : ℂ) +
            env "a"*env "b"*env "e"^2*env "f"*Pk*Pm*t^2 +
            env "b"^2*env "d"^2*env "g"*Pk*Pm*t^2*((m : ℤ) : ℂ)/2 +
            env "b"^2*env "d"^2*env "g"*Pk*Pm*t^2/2 +
            env "b"^2*env "d"*env "e"*env "f"*Pk*Pm*t^2*((m : ℤ) : ℂ)/4 +
            env "b"^2*env "d"*env "e"*env "f"*Pk*Pm*t^2/4 +
            env "b"^2*env "d"*env "e"*env "g"*Pk*Pm*t^3*((m : ℤ) : ℂ)/2 +
            env "b"^2*env "d"*env "e"*env "g"*Pk*Pm*t^3/2 +
            env "b"^2*env "e"^2*env "f"*Pk*Pm*t^3*((m : ℤ) : ℂ)/4 +
            env "b"^2*env "e"^2*env "f"*Pk*Pm*t^3/4 +
            env "b"*env "c"*env "d"^2*env "g"*Pk*Pm*t^3*((m : ℤ) : ℂ)/2 +
            env "b"*env "c"*env "d"^2*env "g"*Pk*Pm*t^3/2 +
            env "b"*env "c"*env "d"*env "e"*env "g"*Pk*Pm*t^4*((m : ℤ) : ℂ)/2 +
            env "b"*env "c"*env "d"*env "e"*env "g"*Pk*Pm*t^4/2) * hr2

/-! ## rubi4121r9Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4121r9Nondeg_real : rubi4121r9Nondeg.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi4121r9Nondeg.conditions rubi4121r9Nondeg.body
    rubi4121r9Nondeg.result
  intro env hc t hF
  have hr0 : (env "b" * env "c") + (env "a" * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0)) (by simp [rubi4121r9Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4121r9Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hr2 : (env "m" + env "n") + 1 - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)) (.int 0)) (by simp [rubi4121r9Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4121r9Nondeg])
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
    simp [rubi4121r9Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r9Nondeg, Defined, eval, Interp.real, hkm, hkk] at h
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4121r9Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4121r9Nondeg, Defined, eval, Interp.real, hkm, hkk] at h ⊢
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r9Nondeg, Defined, eval, Interp.real, hkm, hkk,
        ivm1R] at h hn4_0 hn4_1 hn4_2 hdb ⊢
    tauto
  · have hfun : (fun w => eval Interp.real (Function.update env "x" w)
        rubi4121r9Nondeg.result) =
            fun w => ((((env "b" * Real.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w)))))) ^ (k)) *
            (((env "a" * env "f") * ((2 * env "m") + 1)))⁻¹) := by
      funext w
      simp [rubi4121r9Nondeg, eval, Interp.real, hkm, hkk, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4121r9Nondeg.body =
        ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k) := by
      simp [rubi4121r9Nondeg, eval, Interp.real, hkm, hkk]
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
    refine (((((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "f") * ((2 * env "m") + 1)))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hr2c : (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) + 1 - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hr2
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
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (0) * hP + (0) * hr0 + (0) * hr1 + (-env "a" - env "b"*S) * hr2c
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 1 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        refine mul_left_cancel₀ hn4_0 ?_
        linear_combination (env "a"*env "b"*env "d"*Pk*((k : ℤ) : ℝ)) * hP +
            (-env "a"*Pk*S - env "b"*Pk*S^2*((k : ℤ) : ℝ) - env "b"*Pk*S^2 +
            env "b"*Pk*((k : ℤ) : ℝ)) * hr0 + (-env "c"*Pk) * hr1 +
            (env "b"^2*env "c"*Pk*S^2 - env "b"^2*env "c"*Pk) * hr2c
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 :=
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
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        have hden : ((m : ℤ) : ℝ) * 2 + 1 ≠ 0 := fun h0 => hn4_2c (by linear_combination (1) * h0)
        rw [div_eq_iff hden]
        linear_combination (env "b"^2*Pm*((m : ℤ) : ℝ)) * hP + (0) * hr0 +
            (-2*Pm*((m : ℤ) : ℝ) - Pm) * hr1 +
            (-2*env "a"*env "b"*Pm*S - env "b"^2*Pm*S^2 - env "b"^2*Pm) * hr2c
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
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 1 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        have hdn0 : ((m : ℤ) : ℝ) * 2 + 1 ≠ 0 := fun h0 => hn4_2c (by linear_combination (1) * h0)
        field_simp
        linear_combination (env "a"*env "b"*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) +
            env "b"^2*env "c"*env "f"*Pk*Pm*((m : ℤ) : ℝ) +
            env "b"^2*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) +
            env "b"^2*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ)) * hP +
            (-2*env "a"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) - 2*env "a"*env "f"*Pk*Pm*S -
            env "b"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) - env "b"*env "f"*Pk*Pm*S^2 -
            env "b"*env "f"*Pk*Pm*((m : ℤ) : ℝ) - env "b"*env "f"*Pk*Pm) * hr0 +
            (-2*env "c"*env "f"*Pk*Pm*((m : ℤ) : ℝ) - env "c"*env "f"*Pk*Pm +
            env "d"*env "f"*Pk*Pm*S) * hr1 +
            (-env "a"*env "b"*env "d"*env "f"*Pk*Pm*S^2 + env "a"*env "b"*env "d"*env "f"*Pk*Pm -
            env "b"^2*env "d"*env "f"*Pk*Pm*S^3 + env "b"^2*env "d"*env "f"*Pk*Pm*S) * hr2c

set_option maxHeartbeats 1000000 in
theorem rubi4121r9Nondeg_complex : rubi4121r9Nondeg.Holds .complex := by
  show AntiderivHoldsUnder Interp.complex "x" rubi4121r9Nondeg.conditions rubi4121r9Nondeg.body
    rubi4121r9Nondeg.result
  intro env hc t hF
  have hr0 : (env "b" * env "c") + (env "a" * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0)) (by simp [rubi4121r9Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4121r9Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hr2 : (env "m" + env "n") + 1 - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)) (.int 0)) (by simp [rubi4121r9Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4121r9Nondeg])
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
    simp [rubi4121r9Nondeg, Defined, eval, Interp.complex, hkm] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4121r9Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4121r9Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4121r9Nondeg, Defined, eval, Interp.complex, hkm, hkk] at h ⊢
    tauto
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4121r9Nondeg, Defined, eval, Interp.complex, hkm, hkk,
        ivm1C] at h hn4_0 hn4_1 hn4_2 hdb ⊢
    tauto
  · have hfun : (fun w => eval Interp.complex (Function.update env "x" w)
        rubi4121r9Nondeg.result) =
            fun w => ((((env "b" * Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (k)) *
            (((env "a" * env "f") * ((2 * env "m") + 1)))⁻¹) := by
      funext w
      simp [rubi4121r9Nondeg, eval, Interp.complex, hkm, hkk, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4121r9Nondeg.body =
        ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k) := by
      simp [rubi4121r9Nondeg, eval, Interp.complex, hkm, hkk]
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
    refine (((((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k) _ (hdzk (k) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "f") * ((2 * env "m") + 1)))⁻¹))).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hr2c : (((m : ℤ) : ℂ) + ((k : ℤ) : ℂ)) + 1 - (0) = 0 :=
        by rw [← (intValue?_eq _ _).1 hkm, ← (intValue?_eq _ _).1 hkk]; exact hr2
    have hn4_2c : (2 * ((m : ℤ) : ℂ)) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn4_2
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        linear_combination (0) * hP + (0) * hr0 + (0) * hr1 + (-env "a" - env "b"*S) * hr2c
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        refine mul_left_cancel₀ hn4_0 ?_
        linear_combination (env "a"*env "b"*env "d"*Pk*((k : ℤ) : ℂ)) * hP +
            (-env "a"*Pk*S - env "b"*Pk*S^2*((k : ℤ) : ℂ) - env "b"*Pk*S^2 +
            env "b"*Pk*((k : ℤ) : ℂ)) * hr0 + (-env "c"*Pk) * hr1 +
            (env "b"^2*env "c"*Pk*S^2 - env "b"^2*env "c"*Pk) * hr2c
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m -
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
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        have hden : ((m : ℤ) : ℂ) * 2 + 1 ≠ 0 := fun h0 => hn4_2c (by linear_combination (1) * h0)
        rw [div_eq_iff hden]
        linear_combination (env "b"^2*Pm*((m : ℤ) : ℂ)) * hP + (0) * hr0 +
            (-2*Pm*((m : ℤ) : ℂ) - Pm) * hr1 +
            (-2*env "a"*env "b"*Pm*S - env "b"^2*Pm*S^2 - env "b"^2*Pm) * hr2c
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
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        have hdn0 : ((m : ℤ) : ℂ) * 2 + 1 ≠ 0 := fun h0 => hn4_2c (by linear_combination (1) * h0)
        field_simp
        linear_combination (env "a"*env "b"*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℂ) +
            env "b"^2*env "c"*env "f"*Pk*Pm*((m : ℤ) : ℂ) +
            env "b"^2*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) +
            env "b"^2*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ)) * hP +
            (-2*env "a"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) - 2*env "a"*env "f"*Pk*Pm*S -
            env "b"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) - env "b"*env "f"*Pk*Pm*S^2 -
            env "b"*env "f"*Pk*Pm*((m : ℤ) : ℂ) - env "b"*env "f"*Pk*Pm) * hr0 +
            (-2*env "c"*env "f"*Pk*Pm*((m : ℤ) : ℂ) - env "c"*env "f"*Pk*Pm +
            env "d"*env "f"*Pk*Pm*S) * hr1 +
            (-env "a"*env "b"*env "d"*env "f"*Pk*Pm*S^2 + env "a"*env "b"*env "d"*env "f"*Pk*Pm -
            env "b"^2*env "d"*env "f"*Pk*Pm*S^3 + env "b"^2*env "d"*env "f"*Pk*Pm*S) * hr2c

/-! ## rubi4142r7Nondeg -/

set_option maxHeartbeats 1000000 in
theorem rubi4142r7Nondeg_real : rubi4142r7Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4142r7Nondeg.conditions rubi4142r7Nondeg.body
    rubi4142r7Nondeg.result rubi4142r7Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "b" * env "c") + (env "a" * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0)) (by simp [rubi4142r7Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r7Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4142r7Nondeg])
  have hn4_1 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_2 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_3 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_4 : (2 * env "m") + 1 ≠ 0 := by
    have h := hc4
    simp [Cond.Holds, Defined, eval] at h
    tauto
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn4_1 (by linear_combination (1) * hzb)
  have hdd : env "d" ≠ 0 := by
    intro hzd
    have hmono : env "b"*env "c" = 0 := by linear_combination (1) * hr0 - (env "a") * hzd
    simp [hn4_1, hn4_2] at hmono
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r7Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r7Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h
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
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4142r7Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4142r7Nondeg, Defined, eval, Interp.real, hkm, hkk, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkk, emm1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4142r7Nondeg, Defined, eval, recEnv, Interp.real, hkm, emk1,
        ivm1R] at h hn4_1 hn4_2 hn4_3 hn4_4 hda hdd ⊢
    tauto
  · simp only [rubi4142r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k)) *
        ((((env "A" *
        (((env "c") ^ 2 * (env "m" + 1)) + ((env "d") ^ 2 * (((2 * env "m") + env "n") + 2)))) +
        (((((-1) * env "B") * env "c") * env "d") * ((env "m" + ((-1) * env "n")) + (-1)))) +
        (((-1) * env "C") *
        (((env "c") ^ 2 * env "m") + (((-1) * (env "d") ^ 2) * (env "n" + 1))))) +
        ((env "d" *
        ((((env "A" * env "c") + (env "B" * env "d")) * ((env "m" + env "n") + 2)) +
        ((((-1) * env "c") * env "C") * ((3 * env "m") + ((-1) * env "n"))))) *
        Real.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkk, emm1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4142r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r7Nondeg.result) =
            fun w => (((((((env "a" * env "A") + (((-1) * env "b") * env "B")) +
            (env "a" * env "C")) * Real.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w)))))) ^ (k + 1)) *
            (((((2 * env "b") * env "c") * env "f") * ((2 * env "m") + 1)))⁻¹) +
            ((-1) * (((((2 * env "b") * env "c") * env "d") * ((2 * env "m") + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4142r7Nondeg, eval, recEnv, Interp.real, hkm, emk1, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4142r7Nondeg.body =
        (((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k)) *
        ((env "A" + (env "B" * Real.sin ((env "e" + (env "f" * t))))) +
        (env "C" * (Real.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4142r7Nondeg, eval, Interp.real, hkm, hkk, iv2R]
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
    refine ((((((hasDerivAt_const t ((((env "a" * env "A") + (((-1) * env "b") * env "B")) +
        (env "a" *
        env "C")))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((((2 * env "b") * env "c") * env "f") * ((2 * env "m") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hn4_4c : (2 * ((m : ℤ) : ℝ)) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn4_4
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zero_sub, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        refine mul_left_cancel₀ hn4_1 ?_
        linear_combination (env "A"*env "a"*env "b"*env "d"^2 - env "B"*env "b"^2*env "d"^2 +
            env "C"*env "a"*env "b"*env "d"^2) * hP +
            (-env "A"*env "a"*env "c" - 2*env "A"*env "a"*env "d"*S - env "A"*env "b"*env "c"*S -
            2*env "A"*env "b"*env "d"*S^2 - env "A"*env "b"*env "d" - env "B"*env "a"*env "d" -
            2*env "B"*env "b"*env "d"*S - env "C"*env "a"*env "d"*S -
            2*env "C"*env "b"*env "d"*S^2) * hr0 +
            (env "A"*env "c"*env "d" + 2*env "A"*env "d"^2*S + env "B"*env "d"^2 +
            env "C"*env "d"^2*S) * hr1
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 1 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        refine mul_left_cancel₀ hn4_1 ?_
        linear_combination (env "A"*env "a"*env "b"*env "c"*env "d"^2*Pk*((k : ℤ) : ℝ) +
            env "A"*env "a"*env "b"*env "c"*env "d"^2*Pk +
            env "A"*env "a"*env "b"*env "d"^3*Pk*S*((k : ℤ) : ℝ) +
            env "A"*env "a"*env "b"*env "d"^3*Pk*S -
            env "B"*env "b"^2*env "c"*env "d"^2*Pk*((k : ℤ) : ℝ) -
            env "B"*env "b"^2*env "c"*env "d"^2*Pk -
            env "B"*env "b"^2*env "d"^3*Pk*S*((k : ℤ) : ℝ) - env "B"*env "b"^2*env "d"^3*Pk*S +
            env "C"*env "a"*env "b"*env "c"*env "d"^2*Pk*((k : ℤ) : ℝ) +
            env "C"*env "a"*env "b"*env "c"*env "d"^2*Pk +
            env "C"*env "a"*env "b"*env "d"^3*Pk*S*((k : ℤ) : ℝ) +
            env "C"*env "a"*env "b"*env "d"^3*Pk*S) * hP +
            (-env "A"*env "a"*env "c"^2*Pk - env "A"*env "a"*env "c"*env "d"*Pk*S*((k : ℤ) : ℝ) -
            3*env "A"*env "a"*env "c"*env "d"*Pk*S -
            env "A"*env "a"*env "d"^2*Pk*S^2*((k : ℤ) : ℝ) - 2*env "A"*env "a"*env "d"^2*Pk*S^2 -
            env "A"*env "b"*env "c"^2*Pk*S - env "A"*env "b"*env "c"*env "d"*Pk*S^2*((k : ℤ) : ℝ) -
            3*env "A"*env "b"*env "c"*env "d"*Pk*S^2 - env "A"*env "b"*env "c"*env "d"*Pk -
            env "A"*env "b"*env "d"^2*Pk*S^3*((k : ℤ) : ℝ) - 2*env "A"*env "b"*env "d"^2*Pk*S^3 -
            env "A"*env "b"*env "d"^2*Pk*S - env "B"*env "a"*env "c"*env "d"*Pk*((k : ℤ) : ℝ) -
            env "B"*env "a"*env "c"*env "d"*Pk - env "B"*env "a"*env "d"^2*Pk*S*((k : ℤ) : ℝ) -
            env "B"*env "a"*env "d"^2*Pk*S - env "B"*env "b"*env "c"*env "d"*Pk*S*((k : ℤ) : ℝ) -
            2*env "B"*env "b"*env "c"*env "d"*Pk*S -
            env "B"*env "b"*env "d"^2*Pk*S^2*((k : ℤ) : ℝ) - 2*env "B"*env "b"*env "d"^2*Pk*S^2 -
            env "C"*env "a"*env "c"*env "d"*Pk*S*((k : ℤ) : ℝ) -
            env "C"*env "a"*env "c"*env "d"*Pk*S - env "C"*env "a"*env "d"^2*Pk*S^2*((k : ℤ) : ℝ) -
            env "C"*env "a"*env "d"^2*Pk*S^2 -
            env "C"*env "b"*env "c"*env "d"*Pk*S^2*((k : ℤ) : ℝ) -
            2*env "C"*env "b"*env "c"*env "d"*Pk*S^2 -
            env "C"*env "b"*env "d"^2*Pk*S^3*((k : ℤ) : ℝ) - 2*env "C"*env "b"*env "d"^2*Pk*S^3) *
            hr0 + (env "A"*env "c"^2*env "d"*Pk + env "A"*env "c"*env "d"^2*Pk*S*((k : ℤ) : ℝ) +
            3*env "A"*env "c"*env "d"^2*Pk*S + env "A"*env "d"^3*Pk*S^2*((k : ℤ) : ℝ) +
            2*env "A"*env "d"^3*Pk*S^2 + env "B"*env "c"*env "d"^2*Pk*((k : ℤ) : ℝ) +
            env "B"*env "c"*env "d"^2*Pk + env "B"*env "d"^3*Pk*S*((k : ℤ) : ℝ) +
            env "B"*env "d"^3*Pk*S + env "C"*env "c"*env "d"^2*Pk*S*((k : ℤ) : ℝ) +
            env "C"*env "c"*env "d"^2*Pk*S + env "C"*env "d"^3*Pk*S^2*((k : ℤ) : ℝ) +
            env "C"*env "d"^3*Pk*S^2) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 :=
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
        simp only [e0m, e1m]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        have hden : ((m : ℤ) : ℝ) * 2 + 1 ≠ 0 := fun h0 => hn4_4c (by linear_combination (1) * h0)
        rw [div_eq_iff hden]
        linear_combination (env "A"*env "a"^2*env "d"^2*Pm +
            env "A"*env "a"*env "b"*env "c"*env "d"*Pm*((m : ℤ) : ℝ) +
            env "A"*env "a"*env "b"*env "d"^2*Pm*S*((m : ℤ) : ℝ) +
            env "A"*env "a"*env "b"*env "d"^2*Pm*S - env "B"*env "a"*env "b"*env "d"^2*Pm -
            env "B"*env "b"^2*env "c"*env "d"*Pm*((m : ℤ) : ℝ) -
            env "B"*env "b"^2*env "d"^2*Pm*S*((m : ℤ) : ℝ) - env "B"*env "b"^2*env "d"^2*Pm*S +
            env "C"*env "a"^2*env "d"^2*Pm +
            env "C"*env "a"*env "b"*env "c"*env "d"*Pm*((m : ℤ) : ℝ) +
            env "C"*env "a"*env "b"*env "d"^2*Pm*S*((m : ℤ) : ℝ) +
            env "C"*env "a"*env "b"*env "d"^2*Pm*S) * hP +
            (-2*env "A"*env "a"*env "c"*Pm*S*((m : ℤ) : ℝ) - 2*env "A"*env "a"*env "c"*Pm*S -
            2*env "A"*env "a"*env "d"*Pm*S^2*((m : ℤ) : ℝ) - 4*env "A"*env "a"*env "d"*Pm*S^2 -
            2*env "A"*env "a"*env "d"*Pm*((m : ℤ) : ℝ) - env "A"*env "a"*env "d"*Pm -
            env "A"*env "b"*env "c"*Pm*S^2*((m : ℤ) : ℝ) - env "A"*env "b"*env "c"*Pm*S^2 -
            env "A"*env "b"*env "c"*Pm*((m : ℤ) : ℝ) - env "A"*env "b"*env "c"*Pm -
            env "A"*env "b"*env "d"*Pm*S^3*((m : ℤ) : ℝ) - 2*env "A"*env "b"*env "d"*Pm*S^3 -
            3*env "A"*env "b"*env "d"*Pm*S*((m : ℤ) : ℝ) - 3*env "A"*env "b"*env "d"*Pm*S -
            2*env "B"*env "a"*env "d"*Pm*S*((m : ℤ) : ℝ) - 3*env "B"*env "a"*env "d"*Pm*S -
            2*env "B"*env "b"*env "d"*Pm*S^2*((m : ℤ) : ℝ) - 2*env "B"*env "b"*env "d"*Pm*S^2 -
            env "B"*env "b"*env "d"*Pm + 2*env "C"*env "a"*env "c"*Pm*S*((m : ℤ) : ℝ) -
            3*env "C"*env "a"*env "d"*Pm*S^2 + env "C"*env "b"*env "c"*Pm*S^2*((m : ℤ) : ℝ) +
            env "C"*env "b"*env "c"*Pm*((m : ℤ) : ℝ) -
            env "C"*env "b"*env "d"*Pm*S^3*((m : ℤ) : ℝ) - 2*env "C"*env "b"*env "d"*Pm*S^3 +
            env "C"*env "b"*env "d"*Pm*S*((m : ℤ) : ℝ) - env "C"*env "b"*env "d"*Pm*S) * hr0 +
            (-env "A"*env "c"^2*Pm*((m : ℤ) : ℝ) - env "A"*env "c"^2*Pm +
            env "A"*env "c"*env "d"*Pm*S*((m : ℤ) : ℝ) - env "A"*env "c"*env "d"*Pm*S +
            2*env "A"*env "d"^2*Pm*S^2*((m : ℤ) : ℝ) + 2*env "A"*env "d"^2*Pm*S^2 +
            env "B"*env "c"*env "d"*Pm*((m : ℤ) : ℝ) - env "B"*env "c"*env "d"*Pm +
            env "B"*env "d"^2*Pm*S*((m : ℤ) : ℝ) + env "B"*env "d"^2*Pm*S +
            env "C"*env "c"^2*Pm*((m : ℤ) : ℝ) + env "C"*env "c"*env "d"*Pm*S*((m : ℤ) : ℝ) -
            env "C"*env "c"*env "d"*Pm*S + env "C"*env "d"^2*Pm*S^2) * hr1
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
        simp only [e0m, e1m]
        have hdmk : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k - 1 :=
            by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
        have hdn0 : ((m : ℤ) : ℝ) * 2 + 1 ≠ 0 := fun h0 => hn4_4c (by linear_combination (1) * h0)
        field_simp
        linear_combination (env "A"*env "a"^2*env "c"*env "d"^2*env "f"*Pk*Pm*((k : ℤ) : ℝ) +
            env "A"*env "a"^2*env "c"*env "d"^2*env "f"*Pk*Pm +
            env "A"*env "a"^2*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) +
            env "A"*env "a"^2*env "d"^3*env "f"*Pk*Pm*S +
            env "A"*env "a"*env "b"*env "c"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) +
            env "A"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) +
            2*env "A"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) +
            env "A"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S +
            env "A"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) +
            env "A"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) +
            env "A"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S^2 -
            env "B"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*((k : ℤ) : ℝ) -
            env "B"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm -
            env "B"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) -
            env "B"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S -
            env "B"*env "b"^2*env "c"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) -
            env "B"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) -
            2*env "B"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) -
            env "B"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S -
            env "B"*env "b"^2*env "d"^3*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) -
            env "B"*env "b"^2*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) -
            env "B"*env "b"^2*env "d"^3*env "f"*Pk*Pm*S^2 +
            env "C"*env "a"^2*env "c"*env "d"^2*env "f"*Pk*Pm*((k : ℤ) : ℝ) +
            env "C"*env "a"^2*env "c"*env "d"^2*env "f"*Pk*Pm +
            env "C"*env "a"^2*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) +
            env "C"*env "a"^2*env "d"^3*env "f"*Pk*Pm*S +
            env "C"*env "a"*env "b"*env "c"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) +
            env "C"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) +
            2*env "C"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) +
            env "C"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S +
            env "C"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) +
            env "C"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) +
            env "C"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S^2) * hP +
            (-2*env "A"*env "a"*env "c"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) -
            2*env "A"*env "a"*env "c"^2*env "f"*Pk*Pm*S -
            2*env "A"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) -
            4*env "A"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) -
            6*env "A"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S^2 -
            2*env "A"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) -
            env "A"*env "a"*env "c"*env "d"*env "f"*Pk*Pm -
            2*env "A"*env "a"*env "d"^2*env "f"*Pk*Pm*S^3*((k : ℤ) : ℝ) -
            2*env "A"*env "a"*env "d"^2*env "f"*Pk*Pm*S^3*((m : ℤ) : ℝ) -
            4*env "A"*env "a"*env "d"^2*env "f"*Pk*Pm*S^3 -
            2*env "A"*env "a"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) -
            env "A"*env "a"*env "d"^2*env "f"*Pk*Pm*S -
            env "A"*env "b"*env "c"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) -
            env "A"*env "b"*env "c"^2*env "f"*Pk*Pm*S^2 -
            env "A"*env "b"*env "c"^2*env "f"*Pk*Pm*((m : ℤ) : ℝ) -
            env "A"*env "b"*env "c"^2*env "f"*Pk*Pm -
            env "A"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^3*((k : ℤ) : ℝ) -
            2*env "A"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^3*((m : ℤ) : ℝ) -
            3*env "A"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^3 -
            env "A"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) -
            4*env "A"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) -
            4*env "A"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S -
            env "A"*env "b"*env "d"^2*env "f"*Pk*Pm*S^4*((k : ℤ) : ℝ) -
            env "A"*env "b"*env "d"^2*env "f"*Pk*Pm*S^4*((m : ℤ) : ℝ) -
            2*env "A"*env "b"*env "d"^2*env "f"*Pk*Pm*S^4 -
            env "A"*env "b"*env "d"^2*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) -
            3*env "A"*env "b"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) -
            3*env "A"*env "b"*env "d"^2*env "f"*Pk*Pm*S^2 -
            2*env "B"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) -
            2*env "B"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) -
            3*env "B"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S -
            2*env "B"*env "a"*env "d"^2*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) -
            2*env "B"*env "a"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) -
            3*env "B"*env "a"*env "d"^2*env "f"*Pk*Pm*S^2 -
            env "B"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) -
            2*env "B"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) -
            2*env "B"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^2 -
            env "B"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) -
            env "B"*env "b"*env "c"*env "d"*env "f"*Pk*Pm -
            env "B"*env "b"*env "d"^2*env "f"*Pk*Pm*S^3*((k : ℤ) : ℝ) -
            2*env "B"*env "b"*env "d"^2*env "f"*Pk*Pm*S^3*((m : ℤ) : ℝ) -
            2*env "B"*env "b"*env "d"^2*env "f"*Pk*Pm*S^3 -
            env "B"*env "b"*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) -
            env "B"*env "b"*env "d"^2*env "f"*Pk*Pm*S +
            2*env "C"*env "a"*env "c"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) -
            2*env "C"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) +
            2*env "C"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) -
            3*env "C"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S^2 -
            2*env "C"*env "a"*env "d"^2*env "f"*Pk*Pm*S^3*((k : ℤ) : ℝ) -
            3*env "C"*env "a"*env "d"^2*env "f"*Pk*Pm*S^3 +
            env "C"*env "b"*env "c"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) +
            env "C"*env "b"*env "c"^2*env "f"*Pk*Pm*((m : ℤ) : ℝ) -
            env "C"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^3*((k : ℤ) : ℝ) -
            2*env "C"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^3 -
            env "C"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) +
            2*env "C"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) -
            env "C"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S -
            env "C"*env "b"*env "d"^2*env "f"*Pk*Pm*S^4*((k : ℤ) : ℝ) -
            env "C"*env "b"*env "d"^2*env "f"*Pk*Pm*S^4*((m : ℤ) : ℝ) -
            2*env "C"*env "b"*env "d"^2*env "f"*Pk*Pm*S^4 -
            env "C"*env "b"*env "d"^2*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) +
            env "C"*env "b"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) -
            env "C"*env "b"*env "d"^2*env "f"*Pk*Pm*S^2) * hr0 +
            (-env "A"*env "c"^3*env "f"*Pk*Pm*((m : ℤ) : ℝ) - env "A"*env "c"^3*env "f"*Pk*Pm -
            env "A"*env "c"^2*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) -
            2*env "A"*env "c"^2*env "d"*env "f"*Pk*Pm*S +
            3*env "A"*env "c"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) +
            env "A"*env "c"*env "d"^2*env "f"*Pk*Pm*S^2 +
            env "A"*env "d"^3*env "f"*Pk*Pm*S^3*((k : ℤ) : ℝ) +
            2*env "A"*env "d"^3*env "f"*Pk*Pm*S^3*((m : ℤ) : ℝ) +
            2*env "A"*env "d"^3*env "f"*Pk*Pm*S^3 -
            env "B"*env "c"^2*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℝ) +
            env "B"*env "c"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℝ) -
            env "B"*env "c"^2*env "d"*env "f"*Pk*Pm +
            2*env "B"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) +
            env "B"*env "d"^3*env "f"*Pk*Pm*S^2*((k : ℤ) : ℝ) +
            env "B"*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) +
            env "B"*env "d"^3*env "f"*Pk*Pm*S^2 + env "C"*env "c"^3*env "f"*Pk*Pm*((m : ℤ) : ℝ) -
            env "C"*env "c"^2*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℝ) +
            2*env "C"*env "c"^2*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℝ) -
            env "C"*env "c"^2*env "d"*env "f"*Pk*Pm*S +
            env "C"*env "c"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℝ) +
            env "C"*env "d"^3*env "f"*Pk*Pm*S^3*((k : ℤ) : ℝ) +
            env "C"*env "d"^3*env "f"*Pk*Pm*S^3) * hr1

set_option maxHeartbeats 1000000 in
theorem rubi4142r7Nondeg_complex : rubi4142r7Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4142r7Nondeg.conditions rubi4142r7Nondeg.body
    rubi4142r7Nondeg.result rubi4142r7Nondeg.integrals
  intro env hc t hF
  have hr0 : (env "b" * env "c") + (env "a" * env "d") - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0)) (by simp [rubi4142r7Nondeg])
    simp [Cond.Holds, Defined, eval] at h
    linear_combination h
  have hr1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4142r7Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int 0)) (by simp [rubi4142r7Nondeg])
  have hn4_1 : env "b" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_2 : env "c" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_3 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc4
  have hn4_4 : (2 * env "m") + 1 ≠ 0 := by
    have h := hc4
    simp [Cond.Holds, Defined, eval] at h
    tauto
  have hda : env "a" ≠ 0 := by
    intro hza
    have hzb : env "b" = 0 := by
      have h2 : env "b" ^ 2 = 0 := by linear_combination (-1) * hr1 - (-env "a") * hza
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    exact hn4_1 (by linear_combination (1) * hzb)
  have hdd : env "d" ≠ 0 := by
    intro hzd
    have hmono : env "b"*env "c" = 0 := by linear_combination (1) * hr0 - (env "a") * hzd
    simp [hn4_1, hn4_2] at hmono
  rcases hkm : intValue? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r7Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  rcases hkk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4142r7Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h
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
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4142r7Nondeg.body →
      (m < 0 → (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) ∧
          (k < 0 → (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4142r7Nondeg, Defined, eval, Interp.complex, hkm, hkk, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4142r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkk, emm1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4142r7Nondeg, Defined, eval, recEnv, Interp.complex, hkm, emk1,
        ivm1C] at h hn4_1 hn4_2 hn4_3 hn4_4 hda hdd ⊢
    tauto
  · simp only [rubi4142r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k)) *
        ((((env "A" *
        (((env "c") ^ 2 * (env "m" + 1)) + ((env "d") ^ 2 * (((2 * env "m") + env "n") + 2)))) +
        (((((-1) * env "B") * env "c") * env "d") * ((env "m" + ((-1) * env "n")) + (-1)))) +
        (((-1) * env "C") *
        (((env "c") ^ 2 * env "m") + (((-1) * (env "d") ^ 2) * (env "n" + 1))))) +
        ((env "d" *
        ((((env "A" * env "c") + (env "B" * env "d")) * ((env "m" + env "n") + 2)) +
        ((((-1) * env "c") * env "C") * ((3 * env "m") + ((-1) * env "n"))))) *
        Complex.sin ((env "e" + (env "f" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkk, emm1, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4142r7Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4142r7Nondeg.result) =
            fun w => (((((((env "a" * env "A") + (((-1) * env "b") * env "B")) +
            (env "a" * env "C")) * Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m)) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (k + 1)) *
            (((((2 * env "b") * env "c") * env "f") * ((2 * env "m") + 1)))⁻¹) +
            ((-1) * (((((2 * env "b") * env "c") * env "d") * ((2 * env "m") + 1)))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4142r7Nondeg, eval, recEnv, Interp.complex, hkm, emk1, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4142r7Nondeg.body =
        (((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m) *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k)) *
        ((env "A" + (env "B" * Complex.sin ((env "e" + (env "f" * t))))) +
        (env "C" * (Complex.sin ((env "e" + (env "f" * t)))) ^ 2)) := by
      simp [rubi4142r7Nondeg, eval, Interp.complex, hkm, hkk, iv2C]
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
    refine ((((((hasDerivAt_const t ((((env "a" * env "A") + (((-1) * env "b") * env "B")) +
        (env "a" *
        env "C")))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdzm (m) (by omega))) ((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (hdzk (k + 1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((((2 * env "b") * env "c") * env "f") * ((2 * env "m") + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, add_sub_cancel_right]
    have hn4_4c : (2 * ((m : ℤ) : ℂ)) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn4_4
    rw [(intValue?_eq _ _).1 hkm] at *
    rw [(intValue?_eq _ _).1 hkk] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hm0
        subst hk0
        simp only [zero_add, zero_sub, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        refine mul_left_cancel₀ hn4_1 ?_
        linear_combination (env "A"*env "a"*env "b"*env "d"^2 - env "B"*env "b"^2*env "d"^2 +
            env "C"*env "a"*env "b"*env "d"^2) * hP +
            (-env "A"*env "a"*env "c" - 2*env "A"*env "a"*env "d"*S - env "A"*env "b"*env "c"*S -
            2*env "A"*env "b"*env "d"*S^2 - env "A"*env "b"*env "d" - env "B"*env "a"*env "d" -
            2*env "B"*env "b"*env "d"*S - env "C"*env "a"*env "d"*S -
            2*env "C"*env "b"*env "d"*S^2) * hr0 +
            (env "A"*env "c"*env "d" + 2*env "A"*env "d"^2*S + env "B"*env "d"^2 +
            env "C"*env "d"^2*S) * hr1
      · subst hm0
        simp only [zero_add, zero_sub, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmk : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        refine mul_left_cancel₀ hn4_1 ?_
        linear_combination (env "A"*env "a"*env "b"*env "c"*env "d"^2*Pk*((k : ℤ) : ℂ) +
            env "A"*env "a"*env "b"*env "c"*env "d"^2*Pk +
            env "A"*env "a"*env "b"*env "d"^3*Pk*S*((k : ℤ) : ℂ) +
            env "A"*env "a"*env "b"*env "d"^3*Pk*S -
            env "B"*env "b"^2*env "c"*env "d"^2*Pk*((k : ℤ) : ℂ) -
            env "B"*env "b"^2*env "c"*env "d"^2*Pk -
            env "B"*env "b"^2*env "d"^3*Pk*S*((k : ℤ) : ℂ) - env "B"*env "b"^2*env "d"^3*Pk*S +
            env "C"*env "a"*env "b"*env "c"*env "d"^2*Pk*((k : ℤ) : ℂ) +
            env "C"*env "a"*env "b"*env "c"*env "d"^2*Pk +
            env "C"*env "a"*env "b"*env "d"^3*Pk*S*((k : ℤ) : ℂ) +
            env "C"*env "a"*env "b"*env "d"^3*Pk*S) * hP +
            (-env "A"*env "a"*env "c"^2*Pk - env "A"*env "a"*env "c"*env "d"*Pk*S*((k : ℤ) : ℂ) -
            3*env "A"*env "a"*env "c"*env "d"*Pk*S -
            env "A"*env "a"*env "d"^2*Pk*S^2*((k : ℤ) : ℂ) - 2*env "A"*env "a"*env "d"^2*Pk*S^2 -
            env "A"*env "b"*env "c"^2*Pk*S - env "A"*env "b"*env "c"*env "d"*Pk*S^2*((k : ℤ) : ℂ) -
            3*env "A"*env "b"*env "c"*env "d"*Pk*S^2 - env "A"*env "b"*env "c"*env "d"*Pk -
            env "A"*env "b"*env "d"^2*Pk*S^3*((k : ℤ) : ℂ) - 2*env "A"*env "b"*env "d"^2*Pk*S^3 -
            env "A"*env "b"*env "d"^2*Pk*S - env "B"*env "a"*env "c"*env "d"*Pk*((k : ℤ) : ℂ) -
            env "B"*env "a"*env "c"*env "d"*Pk - env "B"*env "a"*env "d"^2*Pk*S*((k : ℤ) : ℂ) -
            env "B"*env "a"*env "d"^2*Pk*S - env "B"*env "b"*env "c"*env "d"*Pk*S*((k : ℤ) : ℂ) -
            2*env "B"*env "b"*env "c"*env "d"*Pk*S -
            env "B"*env "b"*env "d"^2*Pk*S^2*((k : ℤ) : ℂ) - 2*env "B"*env "b"*env "d"^2*Pk*S^2 -
            env "C"*env "a"*env "c"*env "d"*Pk*S*((k : ℤ) : ℂ) -
            env "C"*env "a"*env "c"*env "d"*Pk*S - env "C"*env "a"*env "d"^2*Pk*S^2*((k : ℤ) : ℂ) -
            env "C"*env "a"*env "d"^2*Pk*S^2 -
            env "C"*env "b"*env "c"*env "d"*Pk*S^2*((k : ℤ) : ℂ) -
            2*env "C"*env "b"*env "c"*env "d"*Pk*S^2 -
            env "C"*env "b"*env "d"^2*Pk*S^3*((k : ℤ) : ℂ) - 2*env "C"*env "b"*env "d"^2*Pk*S^3) *
            hr0 + (env "A"*env "c"^2*env "d"*Pk + env "A"*env "c"*env "d"^2*Pk*S*((k : ℤ) : ℂ) +
            3*env "A"*env "c"*env "d"^2*Pk*S + env "A"*env "d"^3*Pk*S^2*((k : ℤ) : ℂ) +
            2*env "A"*env "d"^3*Pk*S^2 + env "B"*env "c"*env "d"^2*Pk*((k : ℤ) : ℂ) +
            env "B"*env "c"*env "d"^2*Pk + env "B"*env "d"^3*Pk*S*((k : ℤ) : ℂ) +
            env "B"*env "d"^3*Pk*S + env "C"*env "c"*env "d"^2*Pk*S*((k : ℤ) : ℂ) +
            env "C"*env "c"*env "d"^2*Pk*S + env "C"*env "d"^3*Pk*S^2*((k : ℤ) : ℂ) +
            env "C"*env "d"^3*Pk*S^2) * hr1
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
            add_zero]
        have hdmm : (env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m -
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
        simp only [e0m, e1m]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        field_simp
        have hden : ((m : ℤ) : ℂ) * 2 + 1 ≠ 0 := fun h0 => hn4_4c (by linear_combination (1) * h0)
        rw [div_eq_iff hden]
        linear_combination (env "A"*env "a"^2*env "d"^2*Pm +
            env "A"*env "a"*env "b"*env "c"*env "d"*Pm*((m : ℤ) : ℂ) +
            env "A"*env "a"*env "b"*env "d"^2*Pm*S*((m : ℤ) : ℂ) +
            env "A"*env "a"*env "b"*env "d"^2*Pm*S - env "B"*env "a"*env "b"*env "d"^2*Pm -
            env "B"*env "b"^2*env "c"*env "d"*Pm*((m : ℤ) : ℂ) -
            env "B"*env "b"^2*env "d"^2*Pm*S*((m : ℤ) : ℂ) - env "B"*env "b"^2*env "d"^2*Pm*S +
            env "C"*env "a"^2*env "d"^2*Pm +
            env "C"*env "a"*env "b"*env "c"*env "d"*Pm*((m : ℤ) : ℂ) +
            env "C"*env "a"*env "b"*env "d"^2*Pm*S*((m : ℤ) : ℂ) +
            env "C"*env "a"*env "b"*env "d"^2*Pm*S) * hP +
            (-2*env "A"*env "a"*env "c"*Pm*S*((m : ℤ) : ℂ) - 2*env "A"*env "a"*env "c"*Pm*S -
            2*env "A"*env "a"*env "d"*Pm*S^2*((m : ℤ) : ℂ) - 4*env "A"*env "a"*env "d"*Pm*S^2 -
            2*env "A"*env "a"*env "d"*Pm*((m : ℤ) : ℂ) - env "A"*env "a"*env "d"*Pm -
            env "A"*env "b"*env "c"*Pm*S^2*((m : ℤ) : ℂ) - env "A"*env "b"*env "c"*Pm*S^2 -
            env "A"*env "b"*env "c"*Pm*((m : ℤ) : ℂ) - env "A"*env "b"*env "c"*Pm -
            env "A"*env "b"*env "d"*Pm*S^3*((m : ℤ) : ℂ) - 2*env "A"*env "b"*env "d"*Pm*S^3 -
            3*env "A"*env "b"*env "d"*Pm*S*((m : ℤ) : ℂ) - 3*env "A"*env "b"*env "d"*Pm*S -
            2*env "B"*env "a"*env "d"*Pm*S*((m : ℤ) : ℂ) - 3*env "B"*env "a"*env "d"*Pm*S -
            2*env "B"*env "b"*env "d"*Pm*S^2*((m : ℤ) : ℂ) - 2*env "B"*env "b"*env "d"*Pm*S^2 -
            env "B"*env "b"*env "d"*Pm + 2*env "C"*env "a"*env "c"*Pm*S*((m : ℤ) : ℂ) -
            3*env "C"*env "a"*env "d"*Pm*S^2 + env "C"*env "b"*env "c"*Pm*S^2*((m : ℤ) : ℂ) +
            env "C"*env "b"*env "c"*Pm*((m : ℤ) : ℂ) -
            env "C"*env "b"*env "d"*Pm*S^3*((m : ℤ) : ℂ) - 2*env "C"*env "b"*env "d"*Pm*S^3 +
            env "C"*env "b"*env "d"*Pm*S*((m : ℤ) : ℂ) - env "C"*env "b"*env "d"*Pm*S) * hr0 +
            (-env "A"*env "c"^2*Pm*((m : ℤ) : ℂ) - env "A"*env "c"^2*Pm +
            env "A"*env "c"*env "d"*Pm*S*((m : ℤ) : ℂ) - env "A"*env "c"*env "d"*Pm*S +
            2*env "A"*env "d"^2*Pm*S^2*((m : ℤ) : ℂ) + 2*env "A"*env "d"^2*Pm*S^2 +
            env "B"*env "c"*env "d"*Pm*((m : ℤ) : ℂ) - env "B"*env "c"*env "d"*Pm +
            env "B"*env "d"^2*Pm*S*((m : ℤ) : ℂ) + env "B"*env "d"^2*Pm*S +
            env "C"*env "c"^2*Pm*((m : ℤ) : ℂ) + env "C"*env "c"*env "d"*Pm*S*((m : ℤ) : ℂ) -
            env "C"*env "c"*env "d"*Pm*S + env "C"*env "d"^2*Pm*S^2) * hr1
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
        simp only [e0m, e1m]
        have hdmk : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ k -
            1 := by
          by_cases hm : k < 0
          · exact Or.inl (hBk0 hm)
          · exact Or.inr (by omega)
        have e0k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ k =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 1 hdmk
          rwa [show k - 1 + ((1 : ℕ) : ℤ) = k by push_cast; ring] at this
        have e1k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 1) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 2 hdmk
          rwa [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring] at this
        have e2k : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k + 2) =
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
          have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (k -
              1) 3 hdmk
          rwa [show k - 1 + ((3 : ℕ) : ℤ) = k + 2 by push_cast; ring] at this
        simp only [e0k, e1k]
        generalize ((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = Pm
        generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (k - 1) = Pk
        generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
        generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
        have hdn0 : ((m : ℤ) : ℂ) * 2 + 1 ≠ 0 := fun h0 => hn4_4c (by linear_combination (1) * h0)
        field_simp
        linear_combination (env "A"*env "a"^2*env "c"*env "d"^2*env "f"*Pk*Pm*((k : ℤ) : ℂ) +
            env "A"*env "a"^2*env "c"*env "d"^2*env "f"*Pk*Pm +
            env "A"*env "a"^2*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) +
            env "A"*env "a"^2*env "d"^3*env "f"*Pk*Pm*S +
            env "A"*env "a"*env "b"*env "c"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℂ) +
            env "A"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) +
            2*env "A"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) +
            env "A"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S +
            env "A"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) +
            env "A"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) +
            env "A"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S^2 -
            env "B"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*((k : ℤ) : ℂ) -
            env "B"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm -
            env "B"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) -
            env "B"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S -
            env "B"*env "b"^2*env "c"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℂ) -
            env "B"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) -
            2*env "B"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) -
            env "B"*env "b"^2*env "c"*env "d"^2*env "f"*Pk*Pm*S -
            env "B"*env "b"^2*env "d"^3*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) -
            env "B"*env "b"^2*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) -
            env "B"*env "b"^2*env "d"^3*env "f"*Pk*Pm*S^2 +
            env "C"*env "a"^2*env "c"*env "d"^2*env "f"*Pk*Pm*((k : ℤ) : ℂ) +
            env "C"*env "a"^2*env "c"*env "d"^2*env "f"*Pk*Pm +
            env "C"*env "a"^2*env "d"^3*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) +
            env "C"*env "a"^2*env "d"^3*env "f"*Pk*Pm*S +
            env "C"*env "a"*env "b"*env "c"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℂ) +
            env "C"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) +
            2*env "C"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) +
            env "C"*env "a"*env "b"*env "c"*env "d"^2*env "f"*Pk*Pm*S +
            env "C"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) +
            env "C"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) +
            env "C"*env "a"*env "b"*env "d"^3*env "f"*Pk*Pm*S^2) * hP +
            (-2*env "A"*env "a"*env "c"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) -
            2*env "A"*env "a"*env "c"^2*env "f"*Pk*Pm*S -
            2*env "A"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) -
            4*env "A"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) -
            6*env "A"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S^2 -
            2*env "A"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℂ) -
            env "A"*env "a"*env "c"*env "d"*env "f"*Pk*Pm -
            2*env "A"*env "a"*env "d"^2*env "f"*Pk*Pm*S^3*((k : ℤ) : ℂ) -
            2*env "A"*env "a"*env "d"^2*env "f"*Pk*Pm*S^3*((m : ℤ) : ℂ) -
            4*env "A"*env "a"*env "d"^2*env "f"*Pk*Pm*S^3 -
            2*env "A"*env "a"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) -
            env "A"*env "a"*env "d"^2*env "f"*Pk*Pm*S -
            env "A"*env "b"*env "c"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) -
            env "A"*env "b"*env "c"^2*env "f"*Pk*Pm*S^2 -
            env "A"*env "b"*env "c"^2*env "f"*Pk*Pm*((m : ℤ) : ℂ) -
            env "A"*env "b"*env "c"^2*env "f"*Pk*Pm -
            env "A"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^3*((k : ℤ) : ℂ) -
            2*env "A"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^3*((m : ℤ) : ℂ) -
            3*env "A"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^3 -
            env "A"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) -
            4*env "A"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) -
            4*env "A"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S -
            env "A"*env "b"*env "d"^2*env "f"*Pk*Pm*S^4*((k : ℤ) : ℂ) -
            env "A"*env "b"*env "d"^2*env "f"*Pk*Pm*S^4*((m : ℤ) : ℂ) -
            2*env "A"*env "b"*env "d"^2*env "f"*Pk*Pm*S^4 -
            env "A"*env "b"*env "d"^2*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) -
            3*env "A"*env "b"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) -
            3*env "A"*env "b"*env "d"^2*env "f"*Pk*Pm*S^2 -
            2*env "B"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) -
            2*env "B"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) -
            3*env "B"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S -
            2*env "B"*env "a"*env "d"^2*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) -
            2*env "B"*env "a"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) -
            3*env "B"*env "a"*env "d"^2*env "f"*Pk*Pm*S^2 -
            env "B"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) -
            2*env "B"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) -
            2*env "B"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^2 -
            env "B"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℂ) -
            env "B"*env "b"*env "c"*env "d"*env "f"*Pk*Pm -
            env "B"*env "b"*env "d"^2*env "f"*Pk*Pm*S^3*((k : ℤ) : ℂ) -
            2*env "B"*env "b"*env "d"^2*env "f"*Pk*Pm*S^3*((m : ℤ) : ℂ) -
            2*env "B"*env "b"*env "d"^2*env "f"*Pk*Pm*S^3 -
            env "B"*env "b"*env "d"^2*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) -
            env "B"*env "b"*env "d"^2*env "f"*Pk*Pm*S +
            2*env "C"*env "a"*env "c"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) -
            2*env "C"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) +
            2*env "C"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) -
            3*env "C"*env "a"*env "c"*env "d"*env "f"*Pk*Pm*S^2 -
            2*env "C"*env "a"*env "d"^2*env "f"*Pk*Pm*S^3*((k : ℤ) : ℂ) -
            3*env "C"*env "a"*env "d"^2*env "f"*Pk*Pm*S^3 +
            env "C"*env "b"*env "c"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) +
            env "C"*env "b"*env "c"^2*env "f"*Pk*Pm*((m : ℤ) : ℂ) -
            env "C"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^3*((k : ℤ) : ℂ) -
            2*env "C"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S^3 -
            env "C"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) +
            2*env "C"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) -
            env "C"*env "b"*env "c"*env "d"*env "f"*Pk*Pm*S -
            env "C"*env "b"*env "d"^2*env "f"*Pk*Pm*S^4*((k : ℤ) : ℂ) -
            env "C"*env "b"*env "d"^2*env "f"*Pk*Pm*S^4*((m : ℤ) : ℂ) -
            2*env "C"*env "b"*env "d"^2*env "f"*Pk*Pm*S^4 -
            env "C"*env "b"*env "d"^2*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) +
            env "C"*env "b"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) -
            env "C"*env "b"*env "d"^2*env "f"*Pk*Pm*S^2) * hr0 +
            (-env "A"*env "c"^3*env "f"*Pk*Pm*((m : ℤ) : ℂ) - env "A"*env "c"^3*env "f"*Pk*Pm -
            env "A"*env "c"^2*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) -
            2*env "A"*env "c"^2*env "d"*env "f"*Pk*Pm*S +
            3*env "A"*env "c"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) +
            env "A"*env "c"*env "d"^2*env "f"*Pk*Pm*S^2 +
            env "A"*env "d"^3*env "f"*Pk*Pm*S^3*((k : ℤ) : ℂ) +
            2*env "A"*env "d"^3*env "f"*Pk*Pm*S^3*((m : ℤ) : ℂ) +
            2*env "A"*env "d"^3*env "f"*Pk*Pm*S^3 -
            env "B"*env "c"^2*env "d"*env "f"*Pk*Pm*((k : ℤ) : ℂ) +
            env "B"*env "c"^2*env "d"*env "f"*Pk*Pm*((m : ℤ) : ℂ) -
            env "B"*env "c"^2*env "d"*env "f"*Pk*Pm +
            2*env "B"*env "c"*env "d"^2*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) +
            env "B"*env "d"^3*env "f"*Pk*Pm*S^2*((k : ℤ) : ℂ) +
            env "B"*env "d"^3*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) +
            env "B"*env "d"^3*env "f"*Pk*Pm*S^2 + env "C"*env "c"^3*env "f"*Pk*Pm*((m : ℤ) : ℂ) -
            env "C"*env "c"^2*env "d"*env "f"*Pk*Pm*S*((k : ℤ) : ℂ) +
            2*env "C"*env "c"^2*env "d"*env "f"*Pk*Pm*S*((m : ℤ) : ℂ) -
            env "C"*env "c"^2*env "d"*env "f"*Pk*Pm*S +
            env "C"*env "c"*env "d"^2*env "f"*Pk*Pm*S^2*((m : ℤ) : ℂ) +
            env "C"*env "d"^3*env "f"*Pk*Pm*S^3*((k : ℤ) : ℂ) +
            env "C"*env "d"^3*env "f"*Pk*Pm*S^3) * hr1

end OSR.IntegrationRec297
