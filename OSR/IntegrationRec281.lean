import OSR.IntegrationNum1

/-! # Strengthened trigonometric variants: explicit terms with powers plus a residual integral

Proofs over ℝ (`csc` has no complex interpretation) of RUBI rules whose result is an explicit term
`K cot (a + b csc)^E` (or a product of `cot`, `csc` and such powers) plus a residual integral. The
derivative of the explicit term is built from the rule expression; the integrand is recovered with
`sin² + cos² = 1` and the stated parameter relations, separately for `m = 0` and `m ≠ 0`
(`linear_combination` coefficients computed by Gröbner reduction). -/

namespace OSR.IntegrationRec281

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

/-! ## rubi4131r23Nondeg -/

theorem rubi4131r23Nondeg_real : rubi4131r23Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4131r23Nondeg.conditions rubi4131r23Nondeg.body
    rubi4131r23Nondeg.result rubi4131r23Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hn2 : (env "c") ^ 2 + ((-1) * (env "d") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hn2v : (env "c") ^ 2 + -(env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hn4_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc4
  have hn4_1 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc4
  have hn4_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc4
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4131r23Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h
  have hb3 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi4131r23Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi4131r23Nondeg.body →
      (m < 0 → (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4131r23Nondeg, Defined, eval, Interp.real, hkm, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4131r23Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1, iv2R] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4131r23Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        iv2R] at h hn0 hn1 hn2 hn4_0 hn4_1 hn4_2 ⊢
    tauto
  · simp only [rubi4131r23Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "c" +
        (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        ((((env "d" * (env "n" + 1)) *
        ((env "B" * (((env "b" * env "c") + (((-1) * env "a") * env "d"))) ^ 2) +
        ((((-1) * env "A") * env "d") *
        ((((env "a") ^ 2 * env "c") + ((env "b") ^ 2 * env "c")) +
        ((((-2) * env "a") * env "b") * env "d"))))) +
        (((-1) *
        ((((env "B" * env "c") + (((-1) * env "A") * env "d")) *
        ((((env "a") ^ 2 * (env "d") ^ 2) * (env "n" + 2)) +
        ((env "b") ^ 2 * ((env "c") ^ 2 + ((env "d") ^ 2 * (env "n" + 1)))))) +
        ((((2 * env "a") * env "b") * env "d") *
        ((((env "A" * env "c") * env "d") * (env "n" + 2)) +
        (((-1) * env "B") * ((env "c") ^ 2 + ((env "d") ^ 2 * (env "n" + 1)))))))) *
        Real.sin ((env "e" + (env "f" * t))))) +
        (((((((-1) * (env "b") ^ 2) * env "B") * env "d") * (env "n" + 1)) *
        ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))) *
        (Real.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi4131r23Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4131r23Nondeg.result) =
            fun w => ((((((env "B" * env "c") + (((-1) * env "A") * env "d")) *
            (((env "b" * env "c") + (((-1) * env "a") * env "d"))) ^ 2) *
            Real.cos ((env "e" + (env "f" * w)))) *
            ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            ((((env "f" * (env "d") ^ 2) * (env "n" + 1)) *
            ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) +
            ((-1) *
            ((((env "d") ^ 2 * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4131r23Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi4131r23Nondeg.body =
        (((env "a" + (env "b" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 *
        ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m)) *
        (env "A" + (env "B" * Real.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4131r23Nondeg, eval, Interp.real, hkm, iv2R]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((((env "B" * env "c") + (((-1) * env "A") * env "d")) *
        (((env "b" * env "c") +
        (((-1) * env "a") *
        env "d"))) ^ 2))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((((env "f" * (env "d") ^ 2) * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn4_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn4_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^2*env "d"^4 +
          2*env "A"*env "a"*env "b"*env "c"*env "d"^3 - env "A"*env "b"^2*env "c"^2*env "d"^2 +
          env "B"*env "a"^2*env "c"*env "d"^3 - 2*env "B"*env "a"*env "b"*env "c"^2*env "d"^2 +
          env "B"*env "b"^2*env "c"^3*env "d") * hP
    · have hdm : (env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ m =
          ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
        have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
          ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
        have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
          ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
        have := zsplit ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "c" + (env "d" * Real.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Real.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^2*env "c"*env "d"^4*env "f"*P*((m : ℤ) : ℝ) -
          env "A"*env "a"^2*env "c"*env "d"^4*env "f"*P -
          env "A"*env "a"^2*env "d"^5*env "f"*P*S*((m : ℤ) : ℝ) -
          env "A"*env "a"^2*env "d"^5*env "f"*P*S +
          2*env "A"*env "a"*env "b"*env "c"^2*env "d"^3*env "f"*P*((m : ℤ) : ℝ) +
          2*env "A"*env "a"*env "b"*env "c"^2*env "d"^3*env "f"*P +
          2*env "A"*env "a"*env "b"*env "c"*env "d"^4*env "f"*P*S*((m : ℤ) : ℝ) +
          2*env "A"*env "a"*env "b"*env "c"*env "d"^4*env "f"*P*S -
          env "A"*env "b"^2*env "c"^3*env "d"^2*env "f"*P*((m : ℤ) : ℝ) -
          env "A"*env "b"^2*env "c"^3*env "d"^2*env "f"*P -
          env "A"*env "b"^2*env "c"^2*env "d"^3*env "f"*P*S*((m : ℤ) : ℝ) -
          env "A"*env "b"^2*env "c"^2*env "d"^3*env "f"*P*S +
          env "B"*env "a"^2*env "c"^2*env "d"^3*env "f"*P*((m : ℤ) : ℝ) +
          env "B"*env "a"^2*env "c"^2*env "d"^3*env "f"*P +
          env "B"*env "a"^2*env "c"*env "d"^4*env "f"*P*S*((m : ℤ) : ℝ) +
          env "B"*env "a"^2*env "c"*env "d"^4*env "f"*P*S -
          2*env "B"*env "a"*env "b"*env "c"^3*env "d"^2*env "f"*P*((m : ℤ) : ℝ) -
          2*env "B"*env "a"*env "b"*env "c"^3*env "d"^2*env "f"*P -
          2*env "B"*env "a"*env "b"*env "c"^2*env "d"^3*env "f"*P*S*((m : ℤ) : ℝ) -
          2*env "B"*env "a"*env "b"*env "c"^2*env "d"^3*env "f"*P*S +
          env "B"*env "b"^2*env "c"^4*env "d"*env "f"*P*((m : ℤ) : ℝ) +
          env "B"*env "b"^2*env "c"^4*env "d"*env "f"*P +
          env "B"*env "b"^2*env "c"^3*env "d"^2*env "f"*P*S*((m : ℤ) : ℝ) +
          env "B"*env "b"^2*env "c"^3*env "d"^2*env "f"*P*S) * hP

theorem rubi4131r23Nondeg_complex : rubi4131r23Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4131r23Nondeg.conditions rubi4131r23Nondeg.body
    rubi4131r23Nondeg.result rubi4131r23Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "b" * env "c") + (((-1) * env "a") * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hn0v : (env "b" * env "c") + (-env "a" * env "d") ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hn1 : (env "a") ^ 2 + ((-1) * (env "b") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hn1v : (env "a") ^ 2 + -(env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hn2 : (env "c") ^ 2 + ((-1) * (env "d") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hn2v : (env "c") ^ 2 + -(env "d") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hc4 :=
      hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int 0)) (by simp [rubi4131r23Nondeg])
  have hn4_0 : env "f" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc4
  have hn4_1 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc4
  have hn4_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc4
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4131r23Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h
  have hb3 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi4131r23Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi4131r23Nondeg.body →
      (m < 0 → (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w))))) ≠ 0) := by
    intro w h
    simp [rubi4131r23Nondeg, Defined, eval, Interp.complex, hkm, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4131r23Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1, iv2C] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi4131r23Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C,
        iv2C] at h hn0 hn1 hn2 hn4_0 hn4_1 hn4_2 ⊢
    tauto
  · simp only [rubi4131r23Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (((env "c" +
        (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) *
        ((((env "d" * (env "n" + 1)) *
        ((env "B" * (((env "b" * env "c") + (((-1) * env "a") * env "d"))) ^ 2) +
        ((((-1) * env "A") * env "d") *
        ((((env "a") ^ 2 * env "c") + ((env "b") ^ 2 * env "c")) +
        ((((-2) * env "a") * env "b") * env "d"))))) +
        (((-1) *
        ((((env "B" * env "c") + (((-1) * env "A") * env "d")) *
        ((((env "a") ^ 2 * (env "d") ^ 2) * (env "n" + 2)) +
        ((env "b") ^ 2 * ((env "c") ^ 2 + ((env "d") ^ 2 * (env "n" + 1)))))) +
        ((((2 * env "a") * env "b") * env "d") *
        ((((env "A" * env "c") * env "d") * (env "n" + 2)) +
        (((-1) * env "B") * ((env "c") ^ 2 + ((env "d") ^ 2 * (env "n" + 1)))))))) *
        Complex.sin ((env "e" + (env "f" * t))))) +
        (((((((-1) * (env "b") ^ 2) * env "B") * env "d") * (env "n" + 1)) *
        ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))) *
        (Complex.sin ((env "e" + (env "f" * t)))) ^ 2))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, iv2C, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi4131r23Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi4131r23Nondeg.result) =
            fun w => ((((((env "B" * env "c") + (((-1) * env "A") * env "d")) *
            (((env "b" * env "c") + (((-1) * env "a") * env "d"))) ^ 2) *
            Complex.cos ((env "e" + (env "f" * w)))) *
            ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * w)))))) ^ (m + 1)) *
            ((((env "f" * (env "d") ^ 2) * (env "n" + 1)) *
            ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) +
            ((-1) *
            ((((env "d") ^ 2 * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹) *
            Φ "I1" w := by
      funext w
      simp [rubi4131r23Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi4131r23Nondeg.body =
        (((env "a" + (env "b" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 *
        ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m)) *
        (env "A" + (env "B" * Complex.sin ((env "e" + (env "f" * t))))) := by
      simp [rubi4131r23Nondeg, eval, Interp.complex, hkm, iv2C]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((((env "B" * env "c") + (((-1) * env "A") * env "d")) *
        (((env "b" * env "c") +
        (((-1) * env "a") *
        env "d"))) ^ 2))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "e")).add ((hasDerivAt_const t (env "f")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t (((((env "f" * (env "d") ^ 2) * (env "n" + 1)) * ((env "c") ^ 2 + ((-1) * (env "d") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn4_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn4_2
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "e" + env "f" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^2*env "d"^4 +
          2*env "A"*env "a"*env "b"*env "c"*env "d"^3 - env "A"*env "b"^2*env "c"^2*env "d"^2 +
          env "B"*env "a"^2*env "c"*env "d"^3 - 2*env "B"*env "a"*env "b"*env "c"^2*env "d"^2 +
          env "B"*env "b"^2*env "c"^3*env "d") * hP
    · have hdm : (env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t))))) ≠ 0 ∨ 0 ≤ m - 1 :=
        by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ m =
          ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 1 := by
        have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 1) =
          ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 2 := by
        have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m + 2) =
          ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) *
          ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ 3 := by
        have := zsplit ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) (m -
            1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize ((env "c" + (env "d" * Complex.sin ((env "e" + (env "f" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "e" + env "f" * t) = S at hP ⊢
      generalize Complex.cos (env "e" + env "f" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "a"^2*env "c"*env "d"^4*env "f"*P*((m : ℤ) : ℂ) -
          env "A"*env "a"^2*env "c"*env "d"^4*env "f"*P -
          env "A"*env "a"^2*env "d"^5*env "f"*P*S*((m : ℤ) : ℂ) -
          env "A"*env "a"^2*env "d"^5*env "f"*P*S +
          2*env "A"*env "a"*env "b"*env "c"^2*env "d"^3*env "f"*P*((m : ℤ) : ℂ) +
          2*env "A"*env "a"*env "b"*env "c"^2*env "d"^3*env "f"*P +
          2*env "A"*env "a"*env "b"*env "c"*env "d"^4*env "f"*P*S*((m : ℤ) : ℂ) +
          2*env "A"*env "a"*env "b"*env "c"*env "d"^4*env "f"*P*S -
          env "A"*env "b"^2*env "c"^3*env "d"^2*env "f"*P*((m : ℤ) : ℂ) -
          env "A"*env "b"^2*env "c"^3*env "d"^2*env "f"*P -
          env "A"*env "b"^2*env "c"^2*env "d"^3*env "f"*P*S*((m : ℤ) : ℂ) -
          env "A"*env "b"^2*env "c"^2*env "d"^3*env "f"*P*S +
          env "B"*env "a"^2*env "c"^2*env "d"^3*env "f"*P*((m : ℤ) : ℂ) +
          env "B"*env "a"^2*env "c"^2*env "d"^3*env "f"*P +
          env "B"*env "a"^2*env "c"*env "d"^4*env "f"*P*S*((m : ℤ) : ℂ) +
          env "B"*env "a"^2*env "c"*env "d"^4*env "f"*P*S -
          2*env "B"*env "a"*env "b"*env "c"^3*env "d"^2*env "f"*P*((m : ℤ) : ℂ) -
          2*env "B"*env "a"*env "b"*env "c"^3*env "d"^2*env "f"*P -
          2*env "B"*env "a"*env "b"*env "c"^2*env "d"^3*env "f"*P*S*((m : ℤ) : ℂ) -
          2*env "B"*env "a"*env "b"*env "c"^2*env "d"^3*env "f"*P*S +
          env "B"*env "b"^2*env "c"^4*env "d"*env "f"*P*((m : ℤ) : ℂ) +
          env "B"*env "b"^2*env "c"^4*env "d"*env "f"*P +
          env "B"*env "b"^2*env "c"^3*env "d"^2*env "f"*P*S*((m : ℤ) : ℂ) +
          env "B"*env "b"^2*env "c"^3*env "d"^2*env "f"*P*S) * hP

/-! ## rubi415r6Nondeg -/

theorem rubi415r6Nondeg_real : rubi415r6Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi415r6Nondeg.conditions rubi415r6Nondeg.body
    rubi415r6Nondeg.result rubi415r6Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi415r6Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi415r6Nondeg])
  have hn3_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi415r6Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi415r6Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi415r6Nondeg.body →
      (m < 0 → ((env "a" * Real.cos ((env "c" + (env "d" * w)))) +
          (env "b" * Real.sin ((env "c" + (env "d" * w))))) ≠ 0) := by
    intro w h
    simp [rubi415r6Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em2] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi415r6Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        iv2R] at h hn0 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi415r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
        (env "b" * Real.sin ((env "c" + (env "d" * t)))))) ^ (m + 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi415r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi415r6Nondeg.result) =
            fun w => ((((env "b" * Real.cos ((env "c" + (env "d" * w)))) +
            (((-1) * env "a") * Real.sin ((env "c" + (env "d" * w))))) *
            (((env "a" * Real.cos ((env "c" + (env "d" * w)))) +
            (env "b" * Real.sin ((env "c" + (env "d" * w)))))) ^ (m + 1)) *
            (((env "d" * (env "n" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) +
            ((env "n" + 2) * (((env "n" + 1) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi415r6Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi415r6Nondeg.body =
        (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
        (env "b" * Real.sin ((env "c" + (env "d" * t)))))) ^ (m) := by
      simp [rubi415r6Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
        (env "b" * Real.sin ((env "c" + (env "d" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t))))).add ((hasDerivAt_const t (((-1) * env "a"))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) (((hasDerivAt_const t (env "a")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t))))).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "d" * (env "n" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "c" + env "d" * t) = S at hP ⊢
      generalize Real.cos (env "c" + env "d" * t) = C at hP ⊢
      field_simp
      linear_combination (env "a"^2 + env "b"^2) * hP
    · have hdm : ((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
        (env "b" * Real.sin ((env "c" + (env "d" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Real.sin ((env "c" + (env "d" * t)))))) ^ m =
          (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Real.sin ((env "c" + (env "d" * t)))))) ^ (m - 1) *
          (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Real.sin ((env "c" + (env "d" * t)))))) ^ 1 := by
        have := zsplit (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
            (env "b" * Real.sin ((env "c" + (env "d" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Real.sin ((env "c" + (env "d" * t)))))) ^ (m + 1) =
          (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Real.sin ((env "c" + (env "d" * t)))))) ^ (m - 1) *
          (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Real.sin ((env "c" + (env "d" * t)))))) ^ 2 := by
        have := zsplit (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
            (env "b" * Real.sin ((env "c" + (env "d" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Real.sin ((env "c" + (env "d" * t)))))) ^ (m + 2) =
          (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Real.sin ((env "c" + (env "d" * t)))))) ^ (m - 1) *
          (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Real.sin ((env "c" + (env "d" * t)))))) ^ 3 := by
        have := zsplit (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
            (env "b" * Real.sin ((env "c" + (env "d" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1, e2]
      generalize (((env "a" * Real.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Real.sin ((env "c" + (env "d" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "c" + env "d" * t) = S at hP ⊢
      generalize Real.cos (env "c" + env "d" * t) = C at hP ⊢
      field_simp
      linear_combination (C*env "a"^3*env "d"*P*((m : ℤ) : ℝ) + C*env "a"^3*env "d"*P +
          C*env "a"*env "b"^2*env "d"*P*((m : ℤ) : ℝ) + C*env "a"*env "b"^2*env "d"*P +
          env "a"^2*env "b"*env "d"*P*S*((m : ℤ) : ℝ) + env "a"^2*env "b"*env "d"*P*S +
          env "b"^3*env "d"*P*S*((m : ℤ) : ℝ) + env "b"^3*env "d"*P*S) * hP

theorem rubi415r6Nondeg_complex : rubi415r6Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi415r6Nondeg.conditions rubi415r6Nondeg.body
    rubi415r6Nondeg.result rubi415r6Nondeg.integrals
  intro env hc t hF
  have hn0 : (env "a") ^ 2 + (env "b") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi415r6Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi415r6Nondeg])
  have hn3_0 : env "d" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi415r6Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi415r6Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi415r6Nondeg.body →
      (m < 0 → ((env "a" * Complex.cos ((env "c" + (env "d" * w)))) +
          (env "b" * Complex.sin ((env "c" + (env "d" * w))))) ≠ 0) := by
    intro w h
    simp [rubi415r6Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r6Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em2] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi415r6Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C,
        iv2C] at h hn0 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi415r6Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
        (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) ^ (m + 2)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em2, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi415r6Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi415r6Nondeg.result) =
            fun w => ((((env "b" * Complex.cos ((env "c" + (env "d" * w)))) +
            (((-1) * env "a") * Complex.sin ((env "c" + (env "d" * w))))) *
            (((env "a" * Complex.cos ((env "c" + (env "d" * w)))) +
            (env "b" * Complex.sin ((env "c" + (env "d" * w)))))) ^ (m + 1)) *
            (((env "d" * (env "n" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) +
            ((env "n" + 2) * (((env "n" + 1) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi415r6Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi415r6Nondeg.body =
        (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
        (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) ^ (m) := by
      simp [rubi415r6Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
        (env "b" * Complex.sin ((env "c" + (env "d" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t))))).add ((hasDerivAt_const t (((-1) * env "a"))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) (((hasDerivAt_const t (env "a")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t))))).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "c")).add ((hasDerivAt_const t (env "d")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "d" * (env "n" + 1)) * ((env "a") ^ 2 + (env "b") ^ 2)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "c" + env "d" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "c" + env "d" * t) = S at hP ⊢
      generalize Complex.cos (env "c" + env "d" * t) = C at hP ⊢
      field_simp
      linear_combination (env "a"^2 + env "b"^2) * hP
    · have hdm : ((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
        (env "b" * Complex.sin ((env "c" + (env "d" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) ^ m =
          (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) ^ (m - 1) *
          (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) ^ 1 := by
        have := zsplit (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
            (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) ^ (m + 1) =
          (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) ^ (m - 1) *
          (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) ^ 2 := by
        have := zsplit (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
            (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) ^ (m + 2) =
          (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) ^ (m - 1) *
          (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) ^ 3 := by
        have := zsplit (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
            (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1, e2]
      generalize (((env "a" * Complex.cos ((env "c" + (env "d" * t)))) +
          (env "b" * Complex.sin ((env "c" + (env "d" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "c" + env "d" * t) = S at hP ⊢
      generalize Complex.cos (env "c" + env "d" * t) = C at hP ⊢
      field_simp
      linear_combination (C*env "a"^3*env "d"*P*((m : ℤ) : ℂ) + C*env "a"^3*env "d"*P +
          C*env "a"*env "b"^2*env "d"*P*((m : ℤ) : ℂ) + C*env "a"*env "b"^2*env "d"*P +
          env "a"^2*env "b"*env "d"*P*S*((m : ℤ) : ℂ) + env "a"^2*env "b"*env "d"*P*S +
          env "b"^3*env "d"*P*S*((m : ℤ) : ℂ) + env "b"^3*env "d"*P*S) * hP

/-! ## rubi416r14Nondeg -/

theorem rubi416r14Nondeg_real : rubi416r14Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r14Nondeg.conditions rubi416r14Nondeg.body
    rubi416r14Nondeg.result rubi416r14Nondeg.integrals
  intro env hc t hF
  have hn0 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r14Nondeg])
  have hn0v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r14Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int 0)) (by simp [rubi416r14Nondeg])
  have hn3_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r14Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi416r14Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r14Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r14Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r14Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        iv2R] at h hn0 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi416r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" * (env "n" + 1)) +
        ((((-1) * env "b") * (env "n" + 2)) * Real.cos ((env "d" + (env "e" * t))))) +
        ((((-1) * env "c") * (env "n" + 2)) * Real.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi416r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r14Nondeg.result) =
            fun w => ((((((-1) * env "c") * Real.cos ((env "d" + (env "e" * w)))) +
            (env "b" * Real.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m + 1)) *
            (((env "e" * (env "n" + 1)) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) +
            (1 * (((env "n" + 1) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) * Φ "I1" w :=
            by
      funext w
      simp [rubi416r14Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r14Nondeg.body =
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r14Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "c"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "e" * (env "n" + 1)) * (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "b"^2 - env "c"^2) * hP
    · have hdm : ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-C*env "b"^3*env "e"*P*((m : ℤ) : ℝ) - C*env "b"^3*env "e"*P -
          C*env "b"*env "c"^2*env "e"*P*((m : ℤ) : ℝ) - C*env "b"*env "c"^2*env "e"*P -
          env "a"*env "b"^2*env "e"*P*((m : ℤ) : ℝ) - env "a"*env "b"^2*env "e"*P -
          env "a"*env "c"^2*env "e"*P*((m : ℤ) : ℝ) - env "a"*env "c"^2*env "e"*P -
          env "b"^2*env "c"*env "e"*P*S*((m : ℤ) : ℝ) - env "b"^2*env "c"*env "e"*P*S -
          env "c"^3*env "e"*P*S*((m : ℤ) : ℝ) - env "c"^3*env "e"*P*S) * hP

theorem rubi416r14Nondeg_complex : rubi416r14Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi416r14Nondeg.conditions rubi416r14Nondeg.body
    rubi416r14Nondeg.result rubi416r14Nondeg.integrals
  intro env hc t hF
  have hn0 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r14Nondeg])
  have hn0v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r14Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int 0)) (by simp [rubi416r14Nondeg])
  have hn3_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r14Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb1 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi416r14Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r14Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r14Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r14Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r14Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C,
        iv2C] at h hn0 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi416r14Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" * (env "n" + 1)) +
        ((((-1) * env "b") * (env "n" + 2)) * Complex.cos ((env "d" + (env "e" * t))))) +
        ((((-1) * env "c") * (env "n" + 2)) * Complex.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi416r14Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r14Nondeg.result) =
            fun w => ((((((-1) * env "c") * Complex.cos ((env "d" + (env "e" * w)))) +
            (env "b" * Complex.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m + 1)) *
            (((env "e" * (env "n" + 1)) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) +
            (1 * (((env "n" + 1) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) * Φ "I1" w :=
            by
      funext w
      simp [rubi416r14Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r14Nondeg.body =
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r14Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((-1) *
        env "c"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "e" * (env "n" + 1)) * (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "b"^2 - env "c"^2) * hP
    · have hdm : ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-C*env "b"^3*env "e"*P*((m : ℤ) : ℂ) - C*env "b"^3*env "e"*P -
          C*env "b"*env "c"^2*env "e"*P*((m : ℤ) : ℂ) - C*env "b"*env "c"^2*env "e"*P -
          env "a"*env "b"^2*env "e"*P*((m : ℤ) : ℂ) - env "a"*env "b"^2*env "e"*P -
          env "a"*env "c"^2*env "e"*P*((m : ℤ) : ℂ) - env "a"*env "c"^2*env "e"*P -
          env "b"^2*env "c"*env "e"*P*S*((m : ℤ) : ℂ) - env "b"^2*env "c"*env "e"*P*S -
          env "c"^3*env "e"*P*S*((m : ℤ) : ℂ) - env "c"^3*env "e"*P*S) * hP

/-! ## rubi416r27Nondeg -/

theorem rubi416r27Nondeg_real : rubi416r27Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r27Nondeg.conditions rubi416r27Nondeg.body
    rubi416r27Nondeg.result rubi416r27Nondeg.integrals
  intro env hc t hF
  have hr1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r27Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn2 : (((env "b" * env "B") + (env "c" * env "C")) * env "n") +
      ((env "a" * env "A") * (env "n" + 1)) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.int 0)) (by simp [rubi416r27Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi416r27Nondeg])
  have hn3_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r27Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r27Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r27Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r27Nondeg, Defined, eval, recEnv, Interp.real, hkm,
        ivm1R] at h hn2 hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi416r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi416r27Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r27Nondeg.result) =
            fun w => ((((((env "B" * env "c") + (((-1) * env "b") * env "C")) +
            ((((-1) * env "a") * env "C") * Real.cos ((env "d" + (env "e" * w))))) +
            ((env "a" * env "B") * Real.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * (env "n" + 1)))⁻¹) +
            (((((env "b" * env "B") + (env "c" * env "C")) * env "n") +
            ((env "a" * env "A") * (env "n" + 1))) * ((env "a" * (env "n" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi416r27Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r27Nondeg.body =
        ((env "A" + (env "B" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "C" * Real.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r27Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((env "B" * env "c") +
        (((-1) * env "b") * env "C")))).add ((hasDerivAt_const t ((((-1) * env "a") *
        env "C"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t ((env "a" * env "B"))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdz (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2c : (((env "b" * env "B") + (env "c" * env "C")) * ((m : ℤ) : ℝ)) +
        ((env "a" * env "A") * (((m : ℤ) : ℝ) + 1)) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm]; exact hn2
    have hn3_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination
    · have hdm : ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0]
      generalize (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "B"*env "a"*env "b"*env "e"*P*((m : ℤ) : ℝ) -
          env "C"*env "a"*env "c"*env "e"*P*((m : ℤ) : ℝ)) * hP +
          (-C*env "B"*env "e"*P*((m : ℤ) : ℝ) - env "C"*env "e"*P*S*((m : ℤ) : ℝ)) * hr1

theorem rubi416r27Nondeg_complex : rubi416r27Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi416r27Nondeg.conditions rubi416r27Nondeg.body
    rubi416r27Nondeg.result rubi416r27Nondeg.integrals
  intro env hc t hF
  have hr1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r27Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hn2 : (((env "b" * env "B") + (env "c" * env "C")) * env "n") +
      ((env "a" * env "A") * (env "n" + 1)) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.int 0)) (by simp [rubi416r27Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi416r27Nondeg])
  have hn3_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r27Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r27Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r27Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r27Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r27Nondeg, Defined, eval, recEnv, Interp.complex, hkm,
        ivm1C] at h hn2 hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi416r27Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi416r27Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r27Nondeg.result) =
            fun w => ((((((env "B" * env "c") + (((-1) * env "b") * env "C")) +
            ((((-1) * env "a") * env "C") * Complex.cos ((env "d" + (env "e" * w))))) +
            ((env "a" * env "B") * Complex.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * (env "n" + 1)))⁻¹) +
            (((((env "b" * env "B") + (env "c" * env "C")) * env "n") +
            ((env "a" * env "A") * (env "n" + 1))) * ((env "a" * (env "n" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi416r27Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r27Nondeg.body =
        ((env "A" + (env "B" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "C" * Complex.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r27Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t (((env "B" * env "c") +
        (((-1) * env "b") * env "C")))).add ((hasDerivAt_const t ((((-1) * env "a") *
        env "C"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t ((env "a" * env "B"))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdz (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2c : (((env "b" * env "B") + (env "c" * env "C")) * ((m : ℤ) : ℂ)) +
        ((env "a" * env "A") * (((m : ℤ) : ℂ) + 1)) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm]; exact hn2
    have hn3_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination
    · have hdm : ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0]
      generalize (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "B"*env "a"*env "b"*env "e"*P*((m : ℤ) : ℂ) -
          env "C"*env "a"*env "c"*env "e"*P*((m : ℤ) : ℂ)) * hP +
          (-C*env "B"*env "e"*P*((m : ℤ) : ℂ) - env "C"*env "e"*P*S*((m : ℤ) : ℂ)) * hr1

/-! ## rubi416r28Nondeg -/

theorem rubi416r28Nondeg_real : rubi416r28Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r28Nondeg.conditions rubi416r28Nondeg.body
    rubi416r28Nondeg.result rubi416r28Nondeg.integrals
  intro env hc t hF
  have hr1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r28Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn2 : ((env "c" * env "C") * env "n") + ((env "a" * env "A") * (env "n" + 1)) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "C")) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.int 0)) (by simp [rubi416r28Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi416r28Nondeg])
  have hn3_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r28Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r28Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r28Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r28Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r28Nondeg, Defined, eval, recEnv, Interp.real, hkm,
        ivm1R] at h hn2 hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi416r28Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi416r28Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r28Nondeg.result) =
            fun w => ((((-1) *
            ((env "b" * env "C") + ((env "a" * env "C") * Real.cos ((env "d" + (env "e" * w)))))) *
            (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * (env "n" + 1)))⁻¹) +
            ((((env "c" * env "C") * env "n") + ((env "a" * env "A") * (env "n" + 1))) *
            ((env "a" * (env "n" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi416r28Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r28Nondeg.body =
        (env "A" + (env "C" * Real.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r28Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul ((hasDerivAt_const t ((env "b" *
        env "C"))).add ((hasDerivAt_const t ((env "a" *
        env "C"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdz (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2c : ((env "c" * env "C") * ((m : ℤ) : ℝ)) +
        ((env "a" * env "A") * (((m : ℤ) : ℝ) + 1)) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm]; exact hn2
    have hn3_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination
    · have hdm : ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0]
      generalize (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "C"*env "a"*env "c"*env "e"*P*((m : ℤ) : ℝ)) * hP +
          (-env "C"*env "e"*P*S*((m : ℤ) : ℝ)) * hr1

theorem rubi416r28Nondeg_complex : rubi416r28Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi416r28Nondeg.conditions rubi416r28Nondeg.body
    rubi416r28Nondeg.result rubi416r28Nondeg.integrals
  intro env hc t hF
  have hr1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r28Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hn2 : ((env "c" * env "C") * env "n") + ((env "a" * env "A") * (env "n" + 1)) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "C")) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.int 0)) (by simp [rubi416r28Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi416r28Nondeg])
  have hn3_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r28Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r28Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r28Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r28Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r28Nondeg, Defined, eval, recEnv, Interp.complex, hkm,
        ivm1C] at h hn2 hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi416r28Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi416r28Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r28Nondeg.result) =
            fun w => ((((-1) *
            ((env "b" * env "C") +
            ((env "a" * env "C") * Complex.cos ((env "d" + (env "e" * w)))))) *
            (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * (env "n" + 1)))⁻¹) +
            ((((env "c" * env "C") * env "n") + ((env "a" * env "A") * (env "n" + 1))) *
            ((env "a" * (env "n" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi416r28Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r28Nondeg.body =
        (env "A" + (env "C" * Complex.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r28Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul ((hasDerivAt_const t ((env "b" *
        env "C"))).add ((hasDerivAt_const t ((env "a" *
        env "C"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdz (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2c : ((env "c" * env "C") * ((m : ℤ) : ℂ)) +
        ((env "a" * env "A") * (((m : ℤ) : ℂ) + 1)) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm]; exact hn2
    have hn3_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination
    · have hdm : ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0]
      generalize (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "C"*env "a"*env "c"*env "e"*P*((m : ℤ) : ℂ)) * hP +
          (-env "C"*env "e"*P*S*((m : ℤ) : ℂ)) * hr1

/-! ## rubi416r29Nondeg -/

theorem rubi416r29Nondeg_real : rubi416r29Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r29Nondeg.conditions rubi416r29Nondeg.body
    rubi416r29Nondeg.result rubi416r29Nondeg.integrals
  intro env hc t hF
  have hr1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r29Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.real, iv2R] at h
    linear_combination h
  have hn2 : ((env "b" * env "B") * env "n") + ((env "a" * env "A") * (env "n" + 1)) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.int 0)) (by simp [rubi416r29Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi416r29Nondeg])
  have hn3_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r29Nondeg, Defined, eval, Interp.real, hkm] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r29Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r29Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r29Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r29Nondeg, Defined, eval, recEnv, Interp.real, hkm,
        ivm1R] at h hn2 hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi416r29Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi416r29Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r29Nondeg.result) =
            fun w => ((((env "B" * env "c") +
            ((env "a" * env "B") * Real.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * (env "n" + 1)))⁻¹) +
            ((((env "b" * env "B") * env "n") + ((env "a" * env "A") * (env "n" + 1))) *
            ((env "a" * (env "n" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi416r29Nondeg, eval, recEnv, Interp.real, hkm, ivm1R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r29Nondeg.body =
        (env "A" + (env "B" * Real.cos ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r29Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((env "B" *
        env "c"))).add ((hasDerivAt_const t ((env "a" *
        env "B"))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdz (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2c : ((env "b" * env "B") * ((m : ℤ) : ℝ)) +
        ((env "a" * env "A") * (((m : ℤ) : ℝ) + 1)) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm]; exact hn2
    have hn3_2c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination
    · have hdm : ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0]
      generalize (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "B"*env "a"*env "b"*env "e"*P*((m : ℤ) : ℝ)) * hP +
          (-C*env "B"*env "e"*P*((m : ℤ) : ℝ)) * hr1

theorem rubi416r29Nondeg_complex : rubi416r29Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi416r29Nondeg.conditions rubi416r29Nondeg.body
    rubi416r29Nondeg.result rubi416r29Nondeg.integrals
  intro env hc t hF
  have hr1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) - (0) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r29Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, iv2C] at h
    linear_combination h
  have hn2 : ((env "b" * env "B") * env "n") + ((env "a" * env "A") * (env "n" + 1)) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.int 0)) (by simp [rubi416r29Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int 0)) (by simp [rubi416r29Nondeg])
  have hn3_0 : env "a" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_1 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  have hn3_2 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r29Nondeg, Defined, eval, Interp.complex, hkm] at h
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r29Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r29Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r29Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r29Nondeg, Defined, eval, recEnv, Interp.complex, hkm,
        ivm1C] at h hn2 hn3_0 hn3_1 hn3_2 ⊢
    tauto
  · simp only [rubi416r29Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m)) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi416r29Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r29Nondeg.result) =
            fun w => ((((env "B" * env "c") +
            ((env "a" * env "B") * Complex.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m)) *
            (((env "a" * env "e") * (env "n" + 1)))⁻¹) +
            ((((env "b" * env "B") * env "n") + ((env "a" * env "A") * (env "n" + 1))) *
            ((env "a" * (env "n" + 1)))⁻¹) * Φ "I1" w := by
      funext w
      simp [rubi416r29Nondeg, eval, recEnv, Interp.complex, hkm, ivm1C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r29Nondeg.body =
        (env "A" + (env "B" * Complex.cos ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r29Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((env "B" *
        env "c"))).add ((hasDerivAt_const t ((env "a" *
        env "B"))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m) _ (hdz (m) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "a" * env "e") * (env "n" + 1)))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
    have hn2c : ((env "b" * env "B") * ((m : ℤ) : ℂ)) +
        ((env "a" * env "A") * (((m : ℤ) : ℂ) + 1)) ≠ 0 :=
        by rw [← (intValue?_eq _ _).1 hkm]; exact hn2
    have hn3_2c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_2
    rw [(intValue?_eq _ _).1 hkm] at *
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zero_sub, zpow_zero, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination
    · have hdm : ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0]
      generalize (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "B"*env "a"*env "b"*env "e"*P*((m : ℤ) : ℂ)) * hP +
          (-C*env "B"*env "e"*P*((m : ℤ) : ℂ)) * hr1

/-! ## rubi416r41Nondeg -/

theorem rubi416r41Nondeg_real : rubi416r41Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r41Nondeg.conditions rubi416r41Nondeg.body
    rubi416r41Nondeg.result rubi416r41Nondeg.integrals
  intro env hc t hF
  have hn1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r41Nondeg])
  have hn1v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r41Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int 0)) (by simp [rubi416r41Nondeg])
  have hn3_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r41Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi416r41Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r41Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r41Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r41Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r41Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        iv2R] at h hn1 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi416r41Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) *
        ((((env "n" + 1) *
        (((env "a" * env "A") + (((-1) * env "b") * env "B")) + (((-1) * env "c") * env "C"))) +
        (((env "n" + 2) * ((env "a" * env "B") + (((-1) * env "b") * env "A"))) *
        Real.cos ((env "d" + (env "e" * t))))) +
        (((env "n" + 2) * ((env "a" * env "C") + (((-1) * env "c") * env "A"))) *
        Real.sin ((env "d" + (env "e" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi416r41Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r41Nondeg.result) =
            fun w => ((((-1) *
            ((((env "c" * env "B") + (((-1) * env "b") * env "C")) +
            (((-1) * ((env "a" * env "C") + (((-1) * env "c") * env "A"))) *
            Real.cos ((env "d" + (env "e" * w))))) +
            (((env "a" * env "B") + (((-1) * env "b") * env "A")) *
            Real.sin ((env "d" + (env "e" * w)))))) *
            (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m + 1)) *
            (((env "e" * (env "n" + 1)) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) +
            (1 * (((env "n" + 1) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) * Φ "I1" w :=
            by
      funext w
      simp [rubi416r41Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r41Nondeg.body =
        ((env "A" + (env "B" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "C" * Real.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r41Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul (((hasDerivAt_const t (((env "c" * env "B") +
        (((-1) * env "b") * env "C")))).add ((hasDerivAt_const t (((-1) *
        ((env "a" * env "C") +
        (((-1) * env "c") *
        env "A"))))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (((env "a" * env "B") + (((-1) * env "b") * env "A")))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "e" * (env "n" + 1)) * (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "b"^2 - env "A"*env "c"^2 + env "B"*env "a"*env "b" +
          env "C"*env "a"*env "c") * hP
    · have hdm : ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-C*env "A"*env "b"^3*env "e"*P*((m : ℤ) : ℝ) -
          C*env "A"*env "b"^3*env "e"*P - C*env "A"*env "b"*env "c"^2*env "e"*P*((m : ℤ) : ℝ) -
          C*env "A"*env "b"*env "c"^2*env "e"*P +
          C*env "B"*env "a"*env "b"^2*env "e"*P*((m : ℤ) : ℝ) +
          C*env "B"*env "a"*env "b"^2*env "e"*P +
          C*env "C"*env "a"*env "b"*env "c"*env "e"*P*((m : ℤ) : ℝ) +
          C*env "C"*env "a"*env "b"*env "c"*env "e"*P -
          env "A"*env "a"*env "b"^2*env "e"*P*((m : ℤ) : ℝ) - env "A"*env "a"*env "b"^2*env "e"*P -
          env "A"*env "a"*env "c"^2*env "e"*P*((m : ℤ) : ℝ) - env "A"*env "a"*env "c"^2*env "e"*P -
          env "A"*env "b"^2*env "c"*env "e"*P*S*((m : ℤ) : ℝ) -
          env "A"*env "b"^2*env "c"*env "e"*P*S - env "A"*env "c"^3*env "e"*P*S*((m : ℤ) : ℝ) -
          env "A"*env "c"^3*env "e"*P*S + env "B"*env "a"^2*env "b"*env "e"*P*((m : ℤ) : ℝ) +
          env "B"*env "a"^2*env "b"*env "e"*P +
          env "B"*env "a"*env "b"*env "c"*env "e"*P*S*((m : ℤ) : ℝ) +
          env "B"*env "a"*env "b"*env "c"*env "e"*P*S +
          env "C"*env "a"^2*env "c"*env "e"*P*((m : ℤ) : ℝ) + env "C"*env "a"^2*env "c"*env "e"*P +
          env "C"*env "a"*env "c"^2*env "e"*P*S*((m : ℤ) : ℝ) +
          env "C"*env "a"*env "c"^2*env "e"*P*S) * hP

theorem rubi416r41Nondeg_complex : rubi416r41Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi416r41Nondeg.conditions rubi416r41Nondeg.body
    rubi416r41Nondeg.result rubi416r41Nondeg.integrals
  intro env hc t hF
  have hn1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r41Nondeg])
  have hn1v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r41Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int 0)) (by simp [rubi416r41Nondeg])
  have hn3_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r41Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi416r41Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r41Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r41Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r41Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r41Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C,
        iv2C] at h hn1 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi416r41Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) *
        ((((env "n" + 1) *
        (((env "a" * env "A") + (((-1) * env "b") * env "B")) + (((-1) * env "c") * env "C"))) +
        (((env "n" + 2) * ((env "a" * env "B") + (((-1) * env "b") * env "A"))) *
        Complex.cos ((env "d" + (env "e" * t))))) +
        (((env "n" + 2) * ((env "a" * env "C") + (((-1) * env "c") * env "A"))) *
        Complex.sin ((env "d" + (env "e" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi416r41Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r41Nondeg.result) =
            fun w => ((((-1) *
            ((((env "c" * env "B") + (((-1) * env "b") * env "C")) +
            (((-1) * ((env "a" * env "C") + (((-1) * env "c") * env "A"))) *
            Complex.cos ((env "d" + (env "e" * w))))) +
            (((env "a" * env "B") + (((-1) * env "b") * env "A")) *
            Complex.sin ((env "d" + (env "e" * w)))))) *
            (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m + 1)) *
            (((env "e" * (env "n" + 1)) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) +
            (1 * (((env "n" + 1) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) * Φ "I1" w :=
            by
      funext w
      simp [rubi416r41Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r41Nondeg.body =
        ((env "A" + (env "B" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "C" * Complex.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r41Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul (((hasDerivAt_const t (((env "c" * env "B") +
        (((-1) * env "b") * env "C")))).add ((hasDerivAt_const t (((-1) *
        ((env "a" * env "C") +
        (((-1) * env "c") *
        env "A"))))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (((env "a" * env "B") + (((-1) * env "b") * env "A")))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "e" * (env "n" + 1)) * (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "b"^2 - env "A"*env "c"^2 + env "B"*env "a"*env "b" +
          env "C"*env "a"*env "c") * hP
    · have hdm : ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-C*env "A"*env "b"^3*env "e"*P*((m : ℤ) : ℂ) -
          C*env "A"*env "b"^3*env "e"*P - C*env "A"*env "b"*env "c"^2*env "e"*P*((m : ℤ) : ℂ) -
          C*env "A"*env "b"*env "c"^2*env "e"*P +
          C*env "B"*env "a"*env "b"^2*env "e"*P*((m : ℤ) : ℂ) +
          C*env "B"*env "a"*env "b"^2*env "e"*P +
          C*env "C"*env "a"*env "b"*env "c"*env "e"*P*((m : ℤ) : ℂ) +
          C*env "C"*env "a"*env "b"*env "c"*env "e"*P -
          env "A"*env "a"*env "b"^2*env "e"*P*((m : ℤ) : ℂ) - env "A"*env "a"*env "b"^2*env "e"*P -
          env "A"*env "a"*env "c"^2*env "e"*P*((m : ℤ) : ℂ) - env "A"*env "a"*env "c"^2*env "e"*P -
          env "A"*env "b"^2*env "c"*env "e"*P*S*((m : ℤ) : ℂ) -
          env "A"*env "b"^2*env "c"*env "e"*P*S - env "A"*env "c"^3*env "e"*P*S*((m : ℤ) : ℂ) -
          env "A"*env "c"^3*env "e"*P*S + env "B"*env "a"^2*env "b"*env "e"*P*((m : ℤ) : ℂ) +
          env "B"*env "a"^2*env "b"*env "e"*P +
          env "B"*env "a"*env "b"*env "c"*env "e"*P*S*((m : ℤ) : ℂ) +
          env "B"*env "a"*env "b"*env "c"*env "e"*P*S +
          env "C"*env "a"^2*env "c"*env "e"*P*((m : ℤ) : ℂ) + env "C"*env "a"^2*env "c"*env "e"*P +
          env "C"*env "a"*env "c"^2*env "e"*P*S*((m : ℤ) : ℂ) +
          env "C"*env "a"*env "c"^2*env "e"*P*S) * hP

/-! ## rubi416r42Nondeg -/

theorem rubi416r42Nondeg_real : rubi416r42Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r42Nondeg.conditions rubi416r42Nondeg.body
    rubi416r42Nondeg.result rubi416r42Nondeg.integrals
  intro env hc t hF
  have hn1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r42Nondeg])
  have hn1v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r42Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int 0)) (by simp [rubi416r42Nondeg])
  have hn3_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r42Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi416r42Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r42Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r42Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r42Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r42Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        iv2R] at h hn1 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi416r42Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) *
        ((((env "n" + 1) * ((env "a" * env "A") + (((-1) * env "c") * env "C"))) +
        (((((-1) * (env "n" + 2)) * env "b") * env "A") * Real.cos ((env "d" + (env "e" * t))))) +
        (((env "n" + 2) * ((env "a" * env "C") + (((-1) * env "c") * env "A"))) *
        Real.sin ((env "d" + (env "e" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi416r42Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r42Nondeg.result) =
            fun w => (((((env "b" * env "C") +
            (((env "a" * env "C") + (((-1) * env "c") * env "A")) *
            Real.cos ((env "d" + (env "e" * w))))) +
            ((env "b" * env "A") * Real.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m + 1)) *
            (((env "e" * (env "n" + 1)) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) +
            (1 * (((env "n" + 1) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) * Φ "I1" w :=
            by
      funext w
      simp [rubi416r42Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r42Nondeg.body =
        (env "A" + (env "C" * Real.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r42Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t ((env "b" *
        env "C"))).add ((hasDerivAt_const t (((env "a" * env "C") +
        (((-1) * env "c") *
        env "A")))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t ((env "b" * env "A"))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "e" * (env "n" + 1)) * (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "b"^2 - env "A"*env "c"^2 + env "C"*env "a"*env "c") * hP
    · have hdm : ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-C*env "A"*env "b"^3*env "e"*P*((m : ℤ) : ℝ) -
          C*env "A"*env "b"^3*env "e"*P - C*env "A"*env "b"*env "c"^2*env "e"*P*((m : ℤ) : ℝ) -
          C*env "A"*env "b"*env "c"^2*env "e"*P +
          C*env "C"*env "a"*env "b"*env "c"*env "e"*P*((m : ℤ) : ℝ) +
          C*env "C"*env "a"*env "b"*env "c"*env "e"*P -
          env "A"*env "a"*env "b"^2*env "e"*P*((m : ℤ) : ℝ) - env "A"*env "a"*env "b"^2*env "e"*P -
          env "A"*env "a"*env "c"^2*env "e"*P*((m : ℤ) : ℝ) - env "A"*env "a"*env "c"^2*env "e"*P -
          env "A"*env "b"^2*env "c"*env "e"*P*S*((m : ℤ) : ℝ) -
          env "A"*env "b"^2*env "c"*env "e"*P*S - env "A"*env "c"^3*env "e"*P*S*((m : ℤ) : ℝ) -
          env "A"*env "c"^3*env "e"*P*S + env "C"*env "a"^2*env "c"*env "e"*P*((m : ℤ) : ℝ) +
          env "C"*env "a"^2*env "c"*env "e"*P +
          env "C"*env "a"*env "c"^2*env "e"*P*S*((m : ℤ) : ℝ) +
          env "C"*env "a"*env "c"^2*env "e"*P*S) * hP

theorem rubi416r42Nondeg_complex : rubi416r42Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi416r42Nondeg.conditions rubi416r42Nondeg.body
    rubi416r42Nondeg.result rubi416r42Nondeg.integrals
  intro env hc t hF
  have hn1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r42Nondeg])
  have hn1v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r42Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int 0)) (by simp [rubi416r42Nondeg])
  have hn3_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r42Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi416r42Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r42Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r42Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r42Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r42Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C,
        iv2C] at h hn1 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi416r42Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) *
        ((((env "n" + 1) * ((env "a" * env "A") + (((-1) * env "c") * env "C"))) +
        (((((-1) * (env "n" + 2)) * env "b") * env "A") *
        Complex.cos ((env "d" + (env "e" * t))))) +
        (((env "n" + 2) * ((env "a" * env "C") + (((-1) * env "c") * env "A"))) *
        Complex.sin ((env "d" + (env "e" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi416r42Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r42Nondeg.result) =
            fun w => (((((env "b" * env "C") +
            (((env "a" * env "C") + (((-1) * env "c") * env "A")) *
            Complex.cos ((env "d" + (env "e" * w))))) +
            ((env "b" * env "A") * Complex.sin ((env "d" + (env "e" * w))))) *
            (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m + 1)) *
            (((env "e" * (env "n" + 1)) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) +
            (1 * (((env "n" + 1) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) * Φ "I1" w :=
            by
      funext w
      simp [rubi416r42Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r42Nondeg.body =
        (env "A" + (env "C" * Complex.sin ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r42Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine ((((((hasDerivAt_const t ((env "b" *
        env "C"))).add ((hasDerivAt_const t (((env "a" * env "C") +
        (((-1) * env "c") *
        env "A")))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t ((env "b" * env "A"))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "e" * (env "n" + 1)) * (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "b"^2 - env "A"*env "c"^2 + env "C"*env "a"*env "c") * hP
    · have hdm : ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-C*env "A"*env "b"^3*env "e"*P*((m : ℤ) : ℂ) -
          C*env "A"*env "b"^3*env "e"*P - C*env "A"*env "b"*env "c"^2*env "e"*P*((m : ℤ) : ℂ) -
          C*env "A"*env "b"*env "c"^2*env "e"*P +
          C*env "C"*env "a"*env "b"*env "c"*env "e"*P*((m : ℤ) : ℂ) +
          C*env "C"*env "a"*env "b"*env "c"*env "e"*P -
          env "A"*env "a"*env "b"^2*env "e"*P*((m : ℤ) : ℂ) - env "A"*env "a"*env "b"^2*env "e"*P -
          env "A"*env "a"*env "c"^2*env "e"*P*((m : ℤ) : ℂ) - env "A"*env "a"*env "c"^2*env "e"*P -
          env "A"*env "b"^2*env "c"*env "e"*P*S*((m : ℤ) : ℂ) -
          env "A"*env "b"^2*env "c"*env "e"*P*S - env "A"*env "c"^3*env "e"*P*S*((m : ℤ) : ℂ) -
          env "A"*env "c"^3*env "e"*P*S + env "C"*env "a"^2*env "c"*env "e"*P*((m : ℤ) : ℂ) +
          env "C"*env "a"^2*env "c"*env "e"*P +
          env "C"*env "a"*env "c"^2*env "e"*P*S*((m : ℤ) : ℂ) +
          env "C"*env "a"*env "c"^2*env "e"*P*S) * hP

/-! ## rubi416r43Nondeg -/

theorem rubi416r43Nondeg_real : rubi416r43Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi416r43Nondeg.conditions rubi416r43Nondeg.body
    rubi416r43Nondeg.result rubi416r43Nondeg.integrals
  intro env hc t hF
  have hn1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r43Nondeg])
  have hn1v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.real,
        iv2R] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r43Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int 0)) (by simp [rubi416r43Nondeg])
  have hn3_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.real, iv2R, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r43Nondeg, Defined, eval, Interp.real, hkm] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi416r43Nondeg])
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      rw [← (intValue?_eq _ _).1 hkm]
      simp [Cond.Holds, Defined, eval, Interp.real] at h
      linarith
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi416r43Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r43Nondeg, Defined, eval, Interp.real, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r43Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.real, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r43Nondeg, Defined, eval, recEnv, Interp.real, em1, ivm1R,
        iv2R] at h hn1 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi416r43Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) *
        ((((env "n" + 1) * ((env "a" * env "A") + (((-1) * env "b") * env "B"))) +
        (((env "n" + 2) * ((env "a" * env "B") + (((-1) * env "b") * env "A"))) *
        Real.cos ((env "d" + (env "e" * t))))) +
        (((((-1) * (env "n" + 2)) * env "c") * env "A") *
        Real.sin ((env "d" + (env "e" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.real, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi416r43Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r43Nondeg.result) =
            fun w => ((((-1) *
            (((env "c" * env "B") + ((env "c" * env "A") * Real.cos ((env "d" + (env "e" * w))))) +
            (((env "a" * env "B") + (((-1) * env "b") * env "A")) *
            Real.sin ((env "d" + (env "e" * w)))))) *
            (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * w)))))) ^ (m + 1)) *
            (((env "e" * (env "n" + 1)) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) +
            (1 * (((env "n" + 1) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) * Φ "I1" w :=
            by
      funext w
      simp [rubi416r43Nondeg, eval, recEnv, Interp.real, em1, ivm1R, iv2R, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi416r43Nondeg.body =
        (env "A" + (env "B" * Real.cos ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r43Nondeg, eval, Interp.real, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul (((hasDerivAt_const t ((env "c" *
        env "B"))).add ((hasDerivAt_const t ((env "c" *
        env "A"))).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (((env "a" * env "B") + (((-1) * env "b") * env "A")))).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Real.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Real.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "e" * (env "n" + 1)) * (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℝ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "b"^2 - env "A"*env "c"^2 + env "B"*env "a"*env "b") * hP
    · have hdm : ((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Real.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Real.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize (((env "a" + (env "b" * Real.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Real.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Real.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Real.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-C*env "A"*env "b"^3*env "e"*P*((m : ℤ) : ℝ) -
          C*env "A"*env "b"^3*env "e"*P - C*env "A"*env "b"*env "c"^2*env "e"*P*((m : ℤ) : ℝ) -
          C*env "A"*env "b"*env "c"^2*env "e"*P +
          C*env "B"*env "a"*env "b"^2*env "e"*P*((m : ℤ) : ℝ) +
          C*env "B"*env "a"*env "b"^2*env "e"*P -
          env "A"*env "a"*env "b"^2*env "e"*P*((m : ℤ) : ℝ) - env "A"*env "a"*env "b"^2*env "e"*P -
          env "A"*env "a"*env "c"^2*env "e"*P*((m : ℤ) : ℝ) - env "A"*env "a"*env "c"^2*env "e"*P -
          env "A"*env "b"^2*env "c"*env "e"*P*S*((m : ℤ) : ℝ) -
          env "A"*env "b"^2*env "c"*env "e"*P*S - env "A"*env "c"^3*env "e"*P*S*((m : ℤ) : ℝ) -
          env "A"*env "c"^3*env "e"*P*S + env "B"*env "a"^2*env "b"*env "e"*P*((m : ℤ) : ℝ) +
          env "B"*env "a"^2*env "b"*env "e"*P +
          env "B"*env "a"*env "b"*env "c"*env "e"*P*S*((m : ℤ) : ℝ) +
          env "B"*env "a"*env "b"*env "c"*env "e"*P*S) * hP

theorem rubi416r43Nondeg_complex : rubi416r43Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi416r43Nondeg.conditions rubi416r43Nondeg.body
    rubi416r43Nondeg.result rubi416r43Nondeg.integrals
  intro env hc t hF
  have hn1 : ((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2) ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r43Nondeg])
  have hn1v : ((env "a") ^ 2 + -(env "b") ^ 2) + -(env "c") ^ 2 ≠ 0 := by
    simpa [Cond.Holds, Defined, eval, Interp.complex,
        iv2C] using hc (.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)) (by simp [rubi416r43Nondeg])
  have hc3 :=
      hc (.ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int 0)) (by simp [rubi416r43Nondeg])
  have hn3_0 : env "e" ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  have hn3_1 : env "n" + 1 ≠ 0 :=
      by intro h0; simp [Cond.Holds, Defined, eval, Interp.complex, iv2C, h0] at hc3
  rcases hkm : intValue? (env "n") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi416r43Nondeg, Defined, eval, Interp.complex, hkm] at h
  have hb0 : m < -1 := by
    have h := hc (.gt (.int (-1)) (.var "n")) (by simp [rubi416r43Nondeg])
    simp [Cond.Holds, Defined, eval, Interp.complex, (intValue?_eq _ _).1 hkm, Complex.ext_iff] at h
    have h' : ((m : ℤ) : ℝ) < (-1 : ℝ) := by
      exact_mod_cast h
    exact_mod_cast h'
  have em1 : intValue? (env "n" + 1) = some (m + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have em2 : intValue? (env "n" + 2) = some (m + 2) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have emm1 : intValue? (env "n" + -1) = some (m - 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkm]; push_cast; ring)
  have ho1 : m + 1 < 0 → m < 0 := by omega
  have ho2 : m + 2 < 0 → m < 0 := by omega
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi416r43Nondeg.body →
      (m < 0 → ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * w))))) ≠ 0) := by
    intro w h
    simp [rubi416r43Nondeg, Defined, eval, Interp.complex, hkm] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi416r43Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := hD w hw
    simp [Defined, eval, Interp.complex, em1] at h ⊢
    tauto
  · filter_upwards [hF] with w hw
    have h := hD w hw
    simp [rubi416r43Nondeg, Defined, eval, recEnv, Interp.complex, em1, ivm1C,
        iv2C] at h hn1 hn3_0 hn3_1 ⊢
    tauto
  · simp only [rubi416r43Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((((env "a" +
        (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) *
        ((((env "n" + 1) * ((env "a" * env "A") + (((-1) * env "b") * env "B"))) +
        (((env "n" + 2) * ((env "a" * env "B") + (((-1) * env "b") * env "A"))) *
        Complex.cos ((env "d" + (env "e" * t))))) +
        (((((-1) * (env "n" + 2)) * env "c") * env "A") *
        Complex.sin ((env "d" + (env "e" * t)))))) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, em1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi416r43Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi416r43Nondeg.result) =
            fun w => ((((-1) *
            (((env "c" * env "B") +
            ((env "c" * env "A") * Complex.cos ((env "d" + (env "e" * w))))) +
            (((env "a" * env "B") + (((-1) * env "b") * env "A")) *
            Complex.sin ((env "d" + (env "e" * w)))))) *
            (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * w))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * w)))))) ^ (m + 1)) *
            (((env "e" * (env "n" + 1)) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) +
            (1 * (((env "n" + 1) *
            (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹) * Φ "I1" w :=
            by
      funext w
      simp [rubi416r43Nondeg, eval, recEnv, Interp.complex, em1, ivm1C, iv2C, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi416r43Nondeg.body =
        (env "A" + (env "B" * Complex.cos ((env "d" + (env "e" * t))))) *
        (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m) := by
      simp [rubi416r43Nondeg, eval, Interp.complex, hkm]
    rw [hfun, hEF]
    have hB0 := hD t hF.self_of_nhds
    have hdz : ∀ E : ℤ, (E < 0 → m < 0) →
        ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ E := by
      intro E hEm
      by_cases hE : 0 ≤ E
      · exact Or.inr hE
      · exact Or.inl (hB0 (hEm (by omega)))
    refine (((((hasDerivAt_const t ((-1))).mul (((hasDerivAt_const t ((env "c" *
        env "B"))).add ((hasDerivAt_const t ((env "c" *
        env "A"))).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (((env "a" * env "B") + (((-1) * env "b") * env "A")))).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t))))))).mul (HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ (hdz (m + 1) (by omega))) (((hasDerivAt_const t (env "a")).add ((hasDerivAt_const t (env "b")).mul ((Complex.hasDerivAt_cos _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))).add ((hasDerivAt_const t (env "c")).mul ((Complex.hasDerivAt_sin _).comp t ((hasDerivAt_const t (env "d")).add ((hasDerivAt_const t (env "e")).mul (hasDerivAt_id' t)))))))).mul (hasDerivAt_const t ((((env "e" * (env "n" + 1)) * (((env "a") ^ 2 + ((-1) * (env "b") ^ 2)) + ((-1) * (env "c") ^ 2))))⁻¹))).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.add_apply, Pi.mul_apply,

      add_sub_cancel_right]
    have hn3_1c : ((m : ℤ) : ℂ) + 1 ≠ 0 := by rw [← (intValue?_eq _ _).1 hkm]; exact hn3_1
    rw [(intValue?_eq _ _).1 hkm] at *
    push_cast
    have hP := Complex.sin_sq_add_cos_sq (env "d" + env "e" * t)
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      simp only [zero_add, zpow_zero, zpow_one, Int.cast_zero, zero_mul, mul_zero,
          add_zero,
        zero_add]
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-env "A"*env "b"^2 - env "A"*env "c"^2 + env "B"*env "a"*env "b") * hP
    · have hdm : ((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
        (env "c" * Complex.sin ((env "d" + (env "e" * t))))) ≠ 0 ∨ 0 ≤ m - 1 := by
        by_cases hm : m < 0
        · exact Or.inl (hB0 hm)
        · exact Or.inr (by omega)
      have e0 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ m =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 1 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 1 hdm
        rwa [show m - 1 + ((1 : ℕ) : ℤ) = m by push_cast; ring] at this
      have e1 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 1) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 2 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 2 hdm
        rwa [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring] at this
      have e2 : (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m + 2) =
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) *
          (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ 3 := by
        have := zsplit (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
            (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) (m - 1) 3 hdm
        rwa [show m - 1 + ((3 : ℕ) : ℤ) = m + 2 by push_cast; ring] at this
      simp only [e0, e1]
      generalize (((env "a" + (env "b" * Complex.cos ((env "d" + (env "e" * t))))) +
          (env "c" * Complex.sin ((env "d" + (env "e" * t)))))) ^ (m - 1) = P
      generalize Complex.sin (env "d" + env "e" * t) = S at hP ⊢
      generalize Complex.cos (env "d" + env "e" * t) = C at hP ⊢
      field_simp
      linear_combination (-C*env "A"*env "b"^3*env "e"*P*((m : ℤ) : ℂ) -
          C*env "A"*env "b"^3*env "e"*P - C*env "A"*env "b"*env "c"^2*env "e"*P*((m : ℤ) : ℂ) -
          C*env "A"*env "b"*env "c"^2*env "e"*P +
          C*env "B"*env "a"*env "b"^2*env "e"*P*((m : ℤ) : ℂ) +
          C*env "B"*env "a"*env "b"^2*env "e"*P -
          env "A"*env "a"*env "b"^2*env "e"*P*((m : ℤ) : ℂ) - env "A"*env "a"*env "b"^2*env "e"*P -
          env "A"*env "a"*env "c"^2*env "e"*P*((m : ℤ) : ℂ) - env "A"*env "a"*env "c"^2*env "e"*P -
          env "A"*env "b"^2*env "c"*env "e"*P*S*((m : ℤ) : ℂ) -
          env "A"*env "b"^2*env "c"*env "e"*P*S - env "A"*env "c"^3*env "e"*P*S*((m : ℤ) : ℂ) -
          env "A"*env "c"^3*env "e"*P*S + env "B"*env "a"^2*env "b"*env "e"*P*((m : ℤ) : ℂ) +
          env "B"*env "a"^2*env "b"*env "e"*P +
          env "B"*env "a"*env "b"*env "c"*env "e"*P*S*((m : ℤ) : ℂ) +
          env "B"*env "a"*env "b"*env "c"*env "e"*P*S) * hP

end OSR.IntegrationRec281
