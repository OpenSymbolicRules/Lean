import OSR.IntegrationNum1
import OSR.IntegrationRec131

/-! # Strengthened inverse hyperbolic tangent rules with `x` factors

Proofs over ℝ of strengthened variants of `OSR.IntegrationNum1`. Both `artanh (c x)` and
`artanh (1/(c x))` have derivative `c / (1 - c^2 x^2)` where they are defined
(`hasDerivAt_artanh_mul`, `hasDerivAt_artanh_inv`), so each rule and its reciprocal-argument
companion share one proof shape. The inverse hyperbolic tangent has no complex
interpretation in the fragment, so the complex statement is vacuous and stays unproved. -/

namespace OSR.IntegrationRec215

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-- `artanh (c x)` has derivative `c / (1 - c^2 x^2)` on `|c x| < 1`. -/
theorem hasDerivAt_artanh_mul {c t : ℝ} (h1 : -1 < c * t) (h2 : c * t < 1) :
    HasDerivAt (fun w => Real.artanh (c * w)) (c * (1 - c ^ 2 * t ^ 2)⁻¹) t := by
  have h := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t
    ((hasDerivAt_id' t).const_mul c)
  refine h.congr_deriv ?_
  rw [mul_pow]; ring

/-- `artanh (1/(c x))` has derivative `c / (1 - c^2 x^2)` on `|c x| > 1`. -/
theorem hasDerivAt_artanh_inv {c t : ℝ} (hct : c * t ≠ 0) (h1 : -1 < (c * t)⁻¹)
    (h2 : (c * t)⁻¹ < 1) :
    HasDerivAt (fun w => Real.artanh (c * w)⁻¹) (c * (1 - c ^ 2 * t ^ 2)⁻¹) t := by
  have h := (OSR.IntegrationRec131.hasDerivAt_artanh h1 h2).comp t
    (((hasDerivAt_id' t).const_mul c).inv hct)
  refine h.congr_deriv ?_
  have hy2 : ((c * t)⁻¹) ^ 2 < 1 := by nlinarith
  have hm : (c * t) ^ 2 * ((c * t)⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hct, one_pow]
  have hgt : 1 < (c * t) ^ 2 := by nlinarith [sq_nonneg ((c * t)⁻¹)]
  have hD2 : 1 - (c * t) ^ 2 ≠ 0 := by linarith
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hct
  have ht0 : t ≠ 0 := right_ne_zero_of_mul hct
  have hD2' : 1 - c ^ 2 * t ^ 2 ≠ 0 := by rwa [mul_pow] at hD2
  have h3 : 1 - ((c * t)⁻¹) ^ 2 = -(1 - (c * t) ^ 2) / (c * t) ^ 2 := by
    field_simp
    ring
  rw [h3, ← mul_pow]
  field_simp

/-- On `|c x| < 1` or `|c x| > 1`, `1 - c^2 x^2 ≠ 0`. -/
theorem one_sub_sq_mul_ne {c t : ℝ} (h1 : -1 < c * t) (h2 : c * t < 1) :
    1 - c ^ 2 * t ^ 2 ≠ 0 := by
  rw [← mul_pow]; exact (sub_pos.mpr (by nlinarith)).ne'

theorem one_sub_sq_inv_ne {c t : ℝ} (hct : c * t ≠ 0) (h1 : -1 < (c * t)⁻¹)
    (h2 : (c * t)⁻¹ < 1) : 1 - c ^ 2 * t ^ 2 ≠ 0 := by
  have hy2 : ((c * t)⁻¹) ^ 2 < 1 := by nlinarith
  have hm : (c * t) ^ 2 * ((c * t)⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hct, one_pow]
  have hgt : 1 < (c * t) ^ 2 := by nlinarith [sq_nonneg ((c * t)⁻¹)]
  rw [← mul_pow]; linarith

private theorem hasDerivAt_quad0 (a b t : ℝ) :
    HasDerivAt (fun w => a + b * w ^ 2) (2 * b * t) t := by
  have h := ((hasDerivAt_pow 2 t).const_mul b).const_add a
  refine h.congr_deriv ?_
  simp; ring

private theorem zpow_succ_of (A : ℝ) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 7.3.1 #69 (and 7.3.4 #49): `∫ x (a + b artanh(c x))^p / (d + e x^2) dx` -/

theorem rubi731r69Nondeg_real : rubi731r69Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r69Nondeg.conditions rubi731r69Nondeg.body
    rubi731r69Nondeg.result rubi731r69Nondeg.integrals
  intro env hc t hF
  have hW : env "b" * env "e" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.app2 .add (.var "p")
      (.int 1))) (.int 0)) (by simp [rubi731r69Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r69Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r69Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨hb, he⟩, hp1⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  have hcz : env "c" ≠ 0 := by rintro h; apply he; rw [he', h]; ring
  have hd : env "d" ≠ 0 := by rintro h; apply he; rw [he', h]; ring
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r69Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have e1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r69Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r69Nondeg, Defined, eval, Interp.real, hkp, ivm1R, iv2R] at h
    have hk0 : ¬ k < 0 := by omega
    tauto
  have hlin : ∀ w, -1 < env "c" * w → env "c" * w < 1 → 1 + -(env "c" * w) ≠ 0 := by
    intro w h1 h2; linarith
  obtain ⟨hD0, hc1, hc2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r69Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hl := hlin w hb.2.1 hb.2.2
    simp [Defined, eval, Interp.real, hkp, ivm1R, hb.2.1, hb.2.2]
    exact ⟨fun h => absurd h (by omega), hl⟩
  · filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [rubi731r69Nondeg, Defined, eval, recEnv, Interp.real, e1, ivm1R, hcz, hd, hb,
      he, hp1, hB.2.1, hB.2.2]
    all_goals first | done | (intro h; exfalso; omega)
  · simp only [rubi731r69Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.artanh (env "c" * t)) ^ k *
        (1 - env "c" * t)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkp, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring_nf
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r69Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r69Nondeg.result) =
        fun w => (env "a" + env "b" * Real.artanh (env "c" * w)) ^ (k + 1) *
            (env "b" * env "e" * (env "p" + 1))⁻¹ + (env "c" * env "d")⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r69Nondeg, eval, recEnv, Interp.real, e1, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r69Nondeg.body =
        t * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k *
          (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi731r69Nondeg, eval, Interp.real, hkp, ivm1R, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_mul hc1 hc2).const_mul (env "b")).const_add (env "a")
    have hP := (hasDerivAt_zpow (k + 1) _ (Or.inr (by omega))).comp t hA
    refine ((hP.mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    rw [hk1]
    have hD := one_sub_sq_mul_ne hc1 hc2
    have hl := hlin t hc1 hc2
    have hl' : 1 - env "c" * t ≠ 0 := by intro h; apply hl; linear_combination h
    have hl2 : 1 + env "c" * t ≠ 0 := by intro h; linarith
    have hfac : 1 - env "c" ^ 2 * t ^ 2 = (1 - env "c" * t) * (1 + env "c" * t) := by ring
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k = P
    have hden : env "d" + env "e" * t ^ 2 = env "d" * ((1 - env "c" * t) * (1 + env "c" * t)) := by
      rw [he']; ring
    rw [hden, he', hfac]
    field_simp
    ring

/-! ## RUBI 7.3.1 #73 (and 7.3.4 #53): `∫ (a + b artanh(c x))^p / (x (d + e x^2)) dx` -/

theorem rubi731r73Nondeg_real : rubi731r73Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r73Nondeg.conditions rubi731r73Nondeg.body
    rubi731r73Nondeg.result rubi731r73Nondeg.integrals
  intro env hc t hF
  have hW : env "b" * env "d" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "p")
      (.int 1))) (.int 0)) (by simp [rubi731r73Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r73Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r73Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨hb, hd⟩, hp1⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r73Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have e1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r73Nondeg.body →
      (¬ w = 0 ∧ ¬ env "d" + env "e" * w ^ 2 = 0) ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r73Nondeg, Defined, eval, Interp.real, hkp, ivm1R, iv2R] at h
    have hk0 : ¬ k < 0 := by omega
    tauto
  have hlin : ∀ w, -1 < env "c" * w → env "c" * w < 1 → 1 + env "c" * w ≠ 0 := by
    intro w h1 h2; linarith
  obtain ⟨⟨ht0, hD0⟩, hc1, hc2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r73Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hl := hlin w hb.2.1 hb.2.2
    simp [Defined, eval, Interp.real, hkp, ivm1R, hb.1.1, hl, hb.2.1, hb.2.2]
    all_goals first | done | (intro h; exfalso; omega)
  · filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [rubi731r73Nondeg, Defined, eval, recEnv, Interp.real, e1, ivm1R, hd, hb, hp1,
      hB.2.1, hB.2.2]
    all_goals first | done | (intro h; exfalso; omega)
  · simp only [rubi731r73Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.artanh (env "c" * t)) ^ k *
        (t * (1 + env "c" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkp, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r73Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r73Nondeg.result) =
        fun w => (env "a" + env "b" * Real.artanh (env "c" * w)) ^ (k + 1) *
            (env "b" * env "d" * (env "p" + 1))⁻¹ + (env "d")⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r73Nondeg, eval, recEnv, Interp.real, e1, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r73Nondeg.body =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k *
          (t * (env "d" + env "e" * t ^ 2))⁻¹ := by
      simp [rubi731r73Nondeg, eval, Interp.real, hkp, ivm1R, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_mul hc1 hc2).const_mul (env "b")).const_add (env "a")
    have hP := (hasDerivAt_zpow (k + 1) _ (Or.inr (by omega))).comp t hA
    refine ((hP.mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    rw [hk1]
    have hD := one_sub_sq_mul_ne hc1 hc2
    have hl := hlin t hc1 hc2
    have hl2 : 1 - env "c" * t ≠ 0 := by intro h; linarith
    have hfac : 1 - env "c" ^ 2 * t ^ 2 = (1 - env "c" * t) * (1 + env "c" * t) := by ring
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k = P
    have hden : env "d" + env "e" * t ^ 2 = env "d" * ((1 - env "c" * t) * (1 + env "c" * t)) := by
      rw [he']; ring
    rw [hden, hfac]
    field_simp
    ring

/-! ## RUBI 7.3.1 #79 (and 7.3.4 #59): `∫ x (d + e x^2)^q (a + b artanh(c x))^p dx` -/

theorem rubi731r79Nondeg_real : rubi731r79Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r79Nondeg.conditions rubi731r79Nondeg.body
    rubi731r79Nondeg.result rubi731r79Nondeg.integrals
  intro env hc t hF
  have hW : 2 * env "e" * (env "q" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "q")
      (.int 1))) (.int 0)) (by simp [rubi731r79Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r79Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r79Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨-, he⟩, hq1⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  have hcz : env "c" ≠ 0 := by rintro h; apply he; rw [he', h]; ring
  have hd : env "d" ≠ 0 := by rintro h; apply he; rw [he', h]; ring
  rcases hkq : intValue? (env "q") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r79Nondeg, Defined, eval, Interp.real, hkq] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r79Nondeg, Defined, eval, Interp.real, hkq, hkp] at h
  have hq : env "q" = (j : ℝ) := (intValue?_eq _ _).1 hkq
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have e1 : intValue? (env "q" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have ep : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r79Nondeg.body →
      (j < 0 → env "d" + env "e" * w ^ 2 ≠ 0) ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r79Nondeg, Defined, eval, Interp.real, hkq, hkp, iv2R] at h
    tauto
  obtain ⟨hj0, hc1, hc2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r79Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [Defined, eval, Interp.real, hkq, ep, iv2R, hb.2.1, hb.2.2]
    exact ⟨hb.1, fun h => absurd h (by omega)⟩
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi731r79Nondeg, Defined, eval, recEnv, Interp.real, e1, hkp, ivm1R, iv2R, he, hcz,
      hq1, hb.2.1, hb.2.2]
    exact ⟨fun h => hb.1 (by omega), fun h => absurd h (by omega)⟩
  · simp only [rubi731r79Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ 2) ^ j *
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkq, ep, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r79Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r79Nondeg.result) =
        fun w => (env "d" + env "e" * w ^ 2) ^ (j + 1) *
            (env "a" + env "b" * Real.artanh (env "c" * w)) ^ k * (2 * env "e" * (env "q" + 1))⁻¹ +
          env "b" * env "p" * (2 * env "c" * (env "q" + 1))⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r79Nondeg, eval, recEnv, Interp.real, e1, hkp, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r79Nondeg.body =
        t * (env "d" + env "e" * t ^ 2) ^ j *
          (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k := by
      simp [rubi731r79Nondeg, eval, Interp.real, hkq, hkp, iv2R]
    rw [hfun, hEF]
    have hz : env "d" + env "e" * t ^ 2 ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases h : j < 0
      · exact Or.inl (hj0 h)
      · exact Or.inr (by omega)
    have hz0 : env "d" + env "e" * t ^ 2 ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (hj0 h)
      · exact Or.inr (by omega)
    have hA := ((hasDerivAt_artanh_mul hc1 hc2).const_mul (env "b")).const_add (env "a")
    have hPq := (hasDerivAt_zpow (j + 1) _ hz).comp t (hasDerivAt_quad0 (env "d") (env "e") t)
    have hPp := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t hA
    refine (((hPq.mul hPp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hz0]
    have hAk : (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k =
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) *
          (env "a" + env "b" * Real.artanh (env "c" * t)) := by
      have := zpow_succ_of (env "a" + env "b" * Real.artanh (env "c" * t)) (k - 1)
        (Or.inr (by omega))
      rwa [sub_add_cancel] at this
    rw [hAk]
    have hj1 : ((j + 1 : ℤ) : ℝ) = env "q" + 1 := by rw [hq]; push_cast; ring
    rw [hj1, ← hp]
    have hD := one_sub_sq_mul_ne hc1 hc2
    generalize (env "d" + env "e" * t ^ 2) ^ j = Q
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) = P
    generalize Real.artanh (env "c" * t) = T
    have hden : env "d" + env "e" * t ^ 2 = env "d" * (1 - env "c" ^ 2 * t ^ 2) := by
      rw [he']; ring
    rw [hden, he']
    field_simp
    ring

theorem rubi734r49Nondeg_real : rubi734r49Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r49Nondeg.conditions rubi734r49Nondeg.body
    rubi734r49Nondeg.result rubi734r49Nondeg.integrals
  exact rubi731r69Nondeg_real

theorem rubi734r53Nondeg_real : rubi734r53Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r53Nondeg.conditions rubi734r53Nondeg.body
    rubi734r53Nondeg.result rubi734r53Nondeg.integrals
  exact rubi731r73Nondeg_real

theorem rubi734r59Nondeg_real : rubi734r59Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r59Nondeg.conditions rubi734r59Nondeg.body
    rubi734r59Nondeg.result rubi734r59Nondeg.integrals
  exact rubi731r79Nondeg_real

end OSR.IntegrationRec215
