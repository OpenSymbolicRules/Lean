import OSR.IntegrationNum1
import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rules with a reciprocal argument

Proofs over ℝ of the `artanh (1/(c x))` companions of the rules of `OSR.IntegrationRec215`,
with the derivative `OSR.IntegrationRec215.hasDerivAt_artanh_inv`. The complex statement is
vacuous (no complex interpretation of `transc1#arctanh`) and stays unproved. Each 7.3.1 rule
has a 7.3.4 twin with the same statement, which reuses its proof. -/

namespace OSR.IntegrationRec216

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem inv_bounds_ne {y : ℝ} (h1 : -1 < y⁻¹) (h2 : y⁻¹ < 1) : y ≠ 1 ∧ y ≠ -1 :=
  ⟨fun h => by rw [h, inv_one] at h2; exact lt_irrefl _ h2,
   fun h => by rw [h] at h1; norm_num at h1⟩

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

theorem rubi731r70Nondeg_real : rubi731r70Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r70Nondeg.conditions rubi731r70Nondeg.body
    rubi731r70Nondeg.result rubi731r70Nondeg.integrals
  intro env hc t hF
  have hW : env "b" * env "e" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.app2 .add (.var "p")
      (.int 1))) (.int 0)) (by simp [rubi731r70Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r70Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r70Nondeg])
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
    simp [rubi731r70Nondeg, Defined, eval, Interp.real, hkp, ivm1R] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have e1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r70Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 ∧ (¬ env "c" = 0 ∧ ¬ w = 0) ∧ (-1 < w⁻¹ * (env "c")⁻¹ ∧ w⁻¹ * (env "c")⁻¹ < 1) := by
    intro w h
    simp [rubi731r70Nondeg, Defined, eval, Interp.real, hkp, ivm1R, iv2R] at h
    have hk0 : ¬ k < 0 := by omega
    tauto
  have hlin : ∀ w, ¬ env "c" = 0 ∧ ¬ w = 0 → -1 < w⁻¹ * (env "c")⁻¹ → w⁻¹ * (env "c")⁻¹ < 1 →
      1 + -(env "c" * w) ≠ 0 := by
    intro w hcw h1 h2 h
    have hb := inv_bounds_ne (y := env "c" * w) (by rwa [mul_inv_rev]) (by rwa [mul_inv_rev])
    exact hb.1 (by linarith)
  obtain ⟨hD0, ⟨-, ht0⟩, hc1, hc2⟩ := hBody t hF.self_of_nhds
  have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht0
  have h1 : -1 < (env "c" * t)⁻¹ := by rw [mul_inv_rev]; exact hc1
  have h2 : (env "c" * t)⁻¹ < 1 := by rw [mul_inv_rev]; exact hc2
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r70Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hl := hlin w hb.2.1 hb.2.2.1 hb.2.2.2
    simp [Defined, eval, Interp.real, hkp, ivm1R, hb.2.1.1, hb.2.1.2, hb.2.2.1, hb.2.2.2]
    exact ⟨fun h => absurd h (by omega), hl⟩
  · filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [rubi731r70Nondeg, Defined, eval, recEnv, Interp.real, e1, ivm1R, hcz, hd, hb,
      he, hp1, hB.2.1.2, hB.2.2.1, hB.2.2.2]
    all_goals first | done | (intro h; exfalso; omega)
  · simp only [rubi731r70Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ k *
        (1 - env "c" * t)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkp, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring_nf
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r70Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r70Nondeg.result) =
        fun w => (env "a" + env "b" * Real.artanh (env "c" * w)⁻¹) ^ (k + 1) *
            (env "b" * env "e" * (env "p" + 1))⁻¹ + (env "c" * env "d")⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r70Nondeg, eval, recEnv, Interp.real, e1, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r70Nondeg.body =
        t * (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ k *
          (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi731r70Nondeg, eval, Interp.real, hkp, ivm1R, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_inv hct h1 h2).const_mul (env "b")).const_add (env "a")
    have hP := (hasDerivAt_zpow (k + 1) _ (Or.inr (by omega))).comp t hA
    refine ((hP.mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    rw [hk1]
    have hD := one_sub_sq_inv_ne hct h1 h2
    have hl := hlin t ⟨hcz, ht0⟩ hc1 hc2
    have hl' : 1 - env "c" * t ≠ 0 := by intro h; apply hl; linear_combination h
    have hl2 : 1 + env "c" * t ≠ 0 := fun h => (inv_bounds_ne h1 h2).2 (by linarith)
    have hfac : 1 - env "c" ^ 2 * t ^ 2 = (1 - env "c" * t) * (1 + env "c" * t) := by ring
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ k = P
    have hden : env "d" + env "e" * t ^ 2 = env "d" * ((1 - env "c" * t) * (1 + env "c" * t)) := by
      rw [he']; ring
    rw [hden, he', hfac]
    field_simp
    ring

theorem rubi731r74Nondeg_real : rubi731r74Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r74Nondeg.conditions rubi731r74Nondeg.body
    rubi731r74Nondeg.result rubi731r74Nondeg.integrals
  intro env hc t hF
  have hW : env "b" * env "d" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "p")
      (.int 1))) (.int 0)) (by simp [rubi731r74Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r74Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r74Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW' := hW
  simp only [mul_ne_zero_iff] at hW'
  obtain ⟨⟨hb, hd⟩, hp1⟩ := hW'
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r74Nondeg, Defined, eval, Interp.real, hkp, ivm1R] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have e1 : intValue? (env "p" + 1) = some (k + 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r74Nondeg.body →
      (¬ w = 0 ∧ ¬ env "d" + env "e" * w ^ 2 = 0) ∧ (¬ env "c" = 0 ∧ ¬ w = 0) ∧ (-1 < w⁻¹ * (env "c")⁻¹ ∧ w⁻¹ * (env "c")⁻¹ < 1) := by
    intro w h
    simp [rubi731r74Nondeg, Defined, eval, Interp.real, hkp, ivm1R, iv2R] at h
    have hk0 : ¬ k < 0 := by omega
    tauto
  have hlin : ∀ w, ¬ env "c" = 0 ∧ ¬ w = 0 → -1 < w⁻¹ * (env "c")⁻¹ → w⁻¹ * (env "c")⁻¹ < 1 →
      1 + env "c" * w ≠ 0 := by
    intro w hcw h1 h2 h
    have hb := inv_bounds_ne (y := env "c" * w) (by rwa [mul_inv_rev]) (by rwa [mul_inv_rev])
    exact hb.2 (by linarith)
  obtain ⟨⟨ht0, hD0⟩, ⟨hcz, -⟩, hc1, hc2⟩ := hBody t hF.self_of_nhds
  have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht0
  have h1 : -1 < (env "c" * t)⁻¹ := by rw [mul_inv_rev]; exact hc1
  have h2 : (env "c" * t)⁻¹ < 1 := by rw [mul_inv_rev]; exact hc2
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r74Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hl := hlin w hb.2.1 hb.2.2.1 hb.2.2.2
    simp [Defined, eval, Interp.real, hkp, ivm1R, hb.1.1, hl, hb.2.1.1, hb.2.2.1, hb.2.2.2]
    all_goals first | done | (intro h; exfalso; omega)
  · filter_upwards [hF] with w hw
    have hB := hBody w hw
    simp [rubi731r74Nondeg, Defined, eval, recEnv, Interp.real, e1, ivm1R, hd, hb, hp1,
      hB.2.1.1, hB.2.1.2, hB.2.2.1, hB.2.2.2]
    all_goals first | done | (intro h; exfalso; omega)
  · simp only [rubi731r74Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ k *
        (t * (1 + env "c" * t))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkp, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r74Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r74Nondeg.result) =
        fun w => (env "a" + env "b" * Real.artanh (env "c" * w)⁻¹) ^ (k + 1) *
            (env "b" * env "d" * (env "p" + 1))⁻¹ + (env "d")⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r74Nondeg, eval, recEnv, Interp.real, e1, ivm1R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r74Nondeg.body =
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ k *
          (t * (env "d" + env "e" * t ^ 2))⁻¹ := by
      simp [rubi731r74Nondeg, eval, Interp.real, hkp, ivm1R, iv2R]
    rw [hfun, hEF]
    have hA := ((hasDerivAt_artanh_inv hct h1 h2).const_mul (env "b")).const_add (env "a")
    have hP := (hasDerivAt_zpow (k + 1) _ (Or.inr (by omega))).comp t hA
    refine ((hP.mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [add_sub_cancel_right]
    have hk1 : ((k + 1 : ℤ) : ℝ) = env "p" + 1 := by rw [hp]; push_cast; ring
    rw [hk1]
    have hD := one_sub_sq_inv_ne hct h1 h2
    have hl := hlin t ⟨hcz, ht0⟩ hc1 hc2
    have hl2 : 1 - env "c" * t ≠ 0 := fun h => (inv_bounds_ne h1 h2).1 (by linarith)
    have hfac : 1 - env "c" ^ 2 * t ^ 2 = (1 - env "c" * t) * (1 + env "c" * t) := by ring
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ k = P
    have hden : env "d" + env "e" * t ^ 2 = env "d" * ((1 - env "c" * t) * (1 + env "c" * t)) := by
      rw [he']; ring
    rw [hden, hfac]
    field_simp
    ring

theorem rubi731r80Nondeg_real : rubi731r80Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r80Nondeg.conditions rubi731r80Nondeg.body
    rubi731r80Nondeg.result rubi731r80Nondeg.integrals
  intro env hc t hF
  have hW : 2 * env "e" * (env "q" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "q")
      (.int 1))) (.int 0)) (by simp [rubi731r80Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r80Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r80Nondeg])
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
    simp [rubi731r80Nondeg, Defined, eval, Interp.real, hkq, ivm1R] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r80Nondeg, Defined, eval, Interp.real, hkq, hkp, ivm1R] at h
  have hq : env "q" = (j : ℝ) := (intValue?_eq _ _).1 hkq
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have e1 : intValue? (env "q" + 1) = some (j + 1) :=
    (intValue?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have ep : intValue? (env "p" + -1) = some (k - 1) :=
    (intValue?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r80Nondeg.body →
      (j < 0 → env "d" + env "e" * w ^ 2 ≠ 0) ∧ (¬ env "c" = 0 ∧ ¬ w = 0) ∧ (-1 < w⁻¹ * (env "c")⁻¹ ∧ w⁻¹ * (env "c")⁻¹ < 1) := by
    intro w h
    simp [rubi731r80Nondeg, Defined, eval, Interp.real, hkq, hkp, iv2R, ivm1R] at h
    tauto
  obtain ⟨hj0, ⟨-, ht0⟩, hc1, hc2⟩ := hBody t hF.self_of_nhds
  have hct : env "c" * t ≠ 0 := mul_ne_zero hcz ht0
  have h1 : -1 < (env "c" * t)⁻¹ := by rw [mul_inv_rev]; exact hc1
  have h2 : (env "c" * t)⁻¹ < 1 := by rw [mul_inv_rev]; exact hc2
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r80Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [Defined, eval, Interp.real, hkq, ep, iv2R, hb.2.1.1, hb.2.1.2, hb.2.2.1, hb.2.2.2, ivm1R]
    exact ⟨hb.1, fun h => absurd h (by omega)⟩
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi731r80Nondeg, Defined, eval, recEnv, Interp.real, e1, hkp, ivm1R, iv2R, he, hcz,
      hq1, hb.2.1.2, hb.2.2.1, hb.2.2.2]
    exact ⟨fun h => hb.1 (by omega), fun h => absurd h (by omega)⟩
  · simp only [rubi731r80Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ 2) ^ j *
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (k - 1)) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkq, ep, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r80Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r80Nondeg.result) =
        fun w => (env "d" + env "e" * w ^ 2) ^ (j + 1) *
            (env "a" + env "b" * Real.artanh (env "c" * w)⁻¹) ^ k * (2 * env "e" * (env "q" + 1))⁻¹ +
          env "b" * env "p" * (2 * env "c" * (env "q" + 1))⁻¹ * Φ "I1" w := by
      funext w; simp [rubi731r80Nondeg, eval, recEnv, Interp.real, e1, hkp, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r80Nondeg.body =
        t * (env "d" + env "e" * t ^ 2) ^ j *
          (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ k := by
      simp [rubi731r80Nondeg, eval, Interp.real, hkq, hkp, iv2R, ivm1R]
    rw [hfun, hEF]
    have hz : env "d" + env "e" * t ^ 2 ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases h : j < 0
      · exact Or.inl (hj0 h)
      · exact Or.inr (by omega)
    have hz0 : env "d" + env "e" * t ^ 2 ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (hj0 h)
      · exact Or.inr (by omega)
    have hA := ((hasDerivAt_artanh_inv hct h1 h2).const_mul (env "b")).const_add (env "a")
    have hPq := (hasDerivAt_zpow (j + 1) _ hz).comp t (hasDerivAt_quad0 (env "d") (env "e") t)
    have hPp := (hasDerivAt_zpow k _ (Or.inr hk.le)).comp t hA
    refine (((hPq.mul hPp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_apply, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hz0]
    have hAk : (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ k =
        (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (k - 1) *
          (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) := by
      have := zpow_succ_of (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) (k - 1)
        (Or.inr (by omega))
      rwa [sub_add_cancel] at this
    rw [hAk]
    have hj1 : ((j + 1 : ℤ) : ℝ) = env "q" + 1 := by rw [hq]; push_cast; ring
    rw [hj1, ← hp]
    have hD := one_sub_sq_inv_ne hct h1 h2
    generalize (env "d" + env "e" * t ^ 2) ^ j = Q
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)⁻¹) ^ (k - 1) = P
    generalize Real.artanh (env "c" * t)⁻¹ = T
    have hden : env "d" + env "e" * t ^ 2 = env "d" * (1 - env "c" ^ 2 * t ^ 2) := by
      rw [he']; ring
    rw [hden, he']
    field_simp
    ring

theorem rubi734r50Nondeg_real : rubi734r50Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r50Nondeg.conditions rubi734r50Nondeg.body
    rubi734r50Nondeg.result rubi734r50Nondeg.integrals
  exact rubi731r70Nondeg_real

theorem rubi734r54Nondeg_real : rubi734r54Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r54Nondeg.conditions rubi734r54Nondeg.body
    rubi734r54Nondeg.result rubi734r54Nondeg.integrals
  exact rubi731r74Nondeg_real

theorem rubi734r60Nondeg_real : rubi734r60Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r60Nondeg.conditions rubi734r60Nondeg.body
    rubi734r60Nondeg.result rubi734r60Nondeg.integrals
  exact rubi731r80Nondeg_real

end OSR.IntegrationRec216
