import OSR.IntegrationNum1

/-! # Strengthened algebraic variants: trinomials split by a binomial factor

Proofs of RUBI 1.2.3.3 #11, #51 and 1.2.3.4 #18 over ℝ and ℂ: with `n₂ = 2 n` and
`c d² - b d e + a e² = 0`, `a + b xⁿ + c x^(2 n) = (d + e xⁿ) (a / d + c xⁿ / e)`, so
`(d + e xⁿ)^q (a + b xⁿ + c x^(2 n))^p` equals `(d + e xⁿ)^(p + q) (a / d + c xⁿ / e)^p`. -/

namespace OSR.IntegrationRec267

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem ivm1C : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2C : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem zmerge {K : Type} [Field K] (X : K) (j k : ℤ) (h : X ≠ 0 ∨ (0 ≤ j ∧ 0 ≤ k)) :
    X ^ j * X ^ k = X ^ (j + k) := by
  rcases h with h | ⟨hj, hk⟩
  · rw [zpow_add₀ h]
  · lift j to ℕ using hj
    lift k to ℕ using hk
    rw [show ((j : ℤ) + k) = ((j + k : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      zpow_natCast, pow_add]

/-! ## rubi1234r18Nondeg -/

theorem rubi1234r18Nondeg_real : rubi1234r18Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1234r18Nondeg.conditions rubi1234r18Nondeg.body
    rubi1234r18Nondeg.result rubi1234r18Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1234r18Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1234r18Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1234r18Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  have hn2e : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1234r18Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1234r18Nondeg, Defined, eval, Interp.real, hkkm] at h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1234r18Nondeg, Defined, eval, Interp.real, hkkm, hkkn] at h
  rcases hkkn2 : intValue? (env "n2") with _ | kn2
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1234r18Nondeg, Defined, eval, Interp.real, hkkm, hkkn, hkkn2] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1234r18Nondeg, Defined, eval, Interp.real, hkkm, hkkn, hkkn2, hkkp] at h
  rcases hkkq : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1234r18Nondeg, Defined, eval, Interp.real, hkkm, hkkn, hkkn2, hkkp, hkkq] at h
  have eqp : intValue? (env "q" + env "p") = some (kq + kp) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkq,
        (intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1234r18Nondeg.body →
      (km < 0 → env "f" * w ≠ 0) ∧ (kn < 0 → w ≠ 0) ∧ (kn2 < 0 → w ≠ 0) ∧
          (kq < 0 → env "d" + env "e" * w ^ kn ≠ 0) ∧ (kp < 0 → env "a" + env "c" * w ^ kn2 ≠ 0) :=
          by
    intro w h
    simp [rubi1234r18Nondeg, Defined, eval, Interp.real, hkkm, hkkn, hkkn2, hkkp, hkkq] at h ⊢
    tauto
  have hn2 : kn2 = kn * 2 := by
    have h := hn2e
    rw [(intValue?_eq _ _).1 hkkn2, (intValue?_eq _ _).1 hkkn] at h
    have h' : ((kn2 : ℤ) : ℝ) = ((kn * 2 : ℤ) : ℝ) := by push_cast; rw [h]; ring
    exact_mod_cast h'
  have hX2 : ∀ w : ℝ, w ^ kn2 = (w ^ kn) ^ 2 := by
    intro w
    rw [hn2, zpow_mul]
    norm_num
  have hfac : ∀ w, env "a" + env "c" * w ^ kn2 = (env "d" + env "e" * w ^ kn) *
      (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ kn) := by
    intro w
    rw [hX2 w]
    generalize w ^ kn = Y
    field_simp
    first
    | linear_combination Y * hrel
    | linear_combination (-Y) * hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1234r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hf0, hw0, hw2, hL, hQ⟩ := hD w hw
    have hQLM : env "a" + env "c" * w ^ kn2 ≠ 0 → env "d" + env "e" * w ^ kn ≠ 0 ∧ env "a" *
        (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ kn ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : kq + kp < 0 → env "d" + env "e" * w ^ kn ≠ 0 := fun h => by
      by_cases hm : kq < 0
      · exact hL hm
      · exact (hQLM (hQ (by omega))).1
    have f1' : kp + kq < 0 → env "d" + env "e" * w ^ kn ≠ 0 := fun h => f1 (by omega)
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.real, hkkm, hkkn, hkkp, eqp, ivm1R] at hf0 hw0 hw2 hL hQ f1 f1' f2 ⊢
    clear hfac hX2 hD hF hc hw hQLM
    repeat' constructor
    all_goals assumption
  · filter_upwards with w
    simp [rubi1234r18Nondeg, Defined, recEnv]
  · simp only [rubi1234r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ km * (env "d" + env "e" * t ^ kn) ^ (kq + kp) *
        (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ kn) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkkm, hkkn, hkkp, eqp, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1234r18Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1234r18Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1234r18Nondeg, eval, recEnv]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1234r18Nondeg.body =
        (env "f" * t) ^ km * (env "d" + env "e" * t ^ kn) ^ kq *
        (env "a" + env "c" * t ^ kn2) ^ kp := by
      simp [rubi1234r18Nondeg, eval, Interp.real, hkkm, hkkn, hkkn2, hkkp, hkkq]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨-, -, -, hL, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "c" * t ^ kn2 ≠ 0 → env "d" + env "e" * t ^ kn ≠ 0 ∧ env "a" *
        (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ kn ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "d" + env "e" * t ^ kn) ^ kq * (env "d" + env "e" * t ^ kn) ^ kp =
        (env "d" + env "e" * t ^ kn) ^ (kq + kp) := by
      rw [show kq + kp = kq + kp by ring]
      apply zmerge
      by_cases hL0 : env "d" + env "e" * t ^ kn = 0
      · right
        constructor
        · by_contra hm; exact hL (by omega) hL0
        · by_contra hp; exact (hQLM (hQ (by omega))).1 hL0
      · exact Or.inl hL0
    rw [hfac t, mul_zpow (env "d" + env "e" * t ^ kn), ← hmerge]
    ring

theorem rubi1234r18Nondeg_complex : rubi1234r18Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1234r18Nondeg.conditions rubi1234r18Nondeg.body
    rubi1234r18Nondeg.result rubi1234r18Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1234r18Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1234r18Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1234r18Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  have hn2e : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1234r18Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1234r18Nondeg, Defined, eval, Interp.complex, hkkm] at h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1234r18Nondeg, Defined, eval, Interp.complex, hkkm, hkkn] at h
  rcases hkkn2 : intValue? (env "n2") with _ | kn2
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1234r18Nondeg, Defined, eval, Interp.complex, hkkm, hkkn, hkkn2] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1234r18Nondeg, Defined, eval, Interp.complex, hkkm, hkkn, hkkn2, hkkp] at h
  rcases hkkq : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1234r18Nondeg, Defined, eval, Interp.complex, hkkm, hkkn, hkkn2, hkkp, hkkq] at h
  have eqp : intValue? (env "q" + env "p") = some (kq + kp) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkq,
        (intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1234r18Nondeg.body →
      (km < 0 → env "f" * w ≠ 0) ∧ (kn < 0 → w ≠ 0) ∧ (kn2 < 0 → w ≠ 0) ∧
          (kq < 0 → env "d" + env "e" * w ^ kn ≠ 0) ∧ (kp < 0 → env "a" + env "c" * w ^ kn2 ≠ 0) :=
          by
    intro w h
    simp [rubi1234r18Nondeg, Defined, eval, Interp.complex, hkkm, hkkn, hkkn2, hkkp, hkkq] at h ⊢
    tauto
  have hn2 : kn2 = kn * 2 := by
    have h := hn2e
    rw [(intValue?_eq _ _).1 hkkn2, (intValue?_eq _ _).1 hkkn] at h
    have h' : ((kn2 : ℤ) : ℂ) = ((kn * 2 : ℤ) : ℂ) := by push_cast; rw [h]; ring
    exact_mod_cast h'
  have hX2 : ∀ w : ℂ, w ^ kn2 = (w ^ kn) ^ 2 := by
    intro w
    rw [hn2, zpow_mul]
    norm_num
  have hfac : ∀ w, env "a" + env "c" * w ^ kn2 = (env "d" + env "e" * w ^ kn) *
      (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ kn) := by
    intro w
    rw [hX2 w]
    generalize w ^ kn = Y
    field_simp
    first
    | linear_combination Y * hrel
    | linear_combination (-Y) * hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1234r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hf0, hw0, hw2, hL, hQ⟩ := hD w hw
    have hQLM : env "a" + env "c" * w ^ kn2 ≠ 0 → env "d" + env "e" * w ^ kn ≠ 0 ∧ env "a" *
        (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ kn ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : kq + kp < 0 → env "d" + env "e" * w ^ kn ≠ 0 := fun h => by
      by_cases hm : kq < 0
      · exact hL hm
      · exact (hQLM (hQ (by omega))).1
    have f1' : kp + kq < 0 → env "d" + env "e" * w ^ kn ≠ 0 := fun h => f1 (by omega)
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.complex, hkkm, hkkn, hkkp, eqp,
        ivm1C] at hf0 hw0 hw2 hL hQ f1 f1' f2 ⊢
    clear hfac hX2 hD hF hc hw hQLM
    repeat' constructor
    all_goals assumption
  · filter_upwards with w
    simp [rubi1234r18Nondeg, Defined, recEnv]
  · simp only [rubi1234r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ km * (env "d" + env "e" * t ^ kn) ^ (kq + kp) *
        (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ kn) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkkm, hkkn, hkkp, eqp, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1234r18Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1234r18Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1234r18Nondeg, eval, recEnv]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1234r18Nondeg.body =
        (env "f" * t) ^ km * (env "d" + env "e" * t ^ kn) ^ kq *
        (env "a" + env "c" * t ^ kn2) ^ kp := by
      simp [rubi1234r18Nondeg, eval, Interp.complex, hkkm, hkkn, hkkn2, hkkp, hkkq]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨-, -, -, hL, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "c" * t ^ kn2 ≠ 0 → env "d" + env "e" * t ^ kn ≠ 0 ∧ env "a" *
        (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ kn ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "d" + env "e" * t ^ kn) ^ kq * (env "d" + env "e" * t ^ kn) ^ kp =
        (env "d" + env "e" * t ^ kn) ^ (kq + kp) := by
      rw [show kq + kp = kq + kp by ring]
      apply zmerge
      by_cases hL0 : env "d" + env "e" * t ^ kn = 0
      · right
        constructor
        · by_contra hm; exact hL (by omega) hL0
        · by_contra hp; exact (hQLM (hQ (by omega))).1 hL0
      · exact Or.inl hL0
    rw [hfac t, mul_zpow (env "d" + env "e" * t ^ kn), ← hmerge]
    ring

/-! ## rubi1233r51Nondeg -/

theorem rubi1233r51Nondeg_real : rubi1233r51Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1233r51Nondeg.conditions rubi1233r51Nondeg.body
    rubi1233r51Nondeg.result rubi1233r51Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1233r51Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1233r51Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1233r51Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  have hn2e : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1233r51Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r51Nondeg, Defined, eval, Interp.real, hkkn] at h
  rcases hkkn2 : intValue? (env "n2") with _ | kn2
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r51Nondeg, Defined, eval, Interp.real, hkkn, hkkn2] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r51Nondeg, Defined, eval, Interp.real, hkkn, hkkn2, hkkp] at h
  rcases hkkq : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r51Nondeg, Defined, eval, Interp.real, hkkn, hkkn2, hkkp, hkkq] at h
  rcases hkkr : intValue? (env "r") with _ | kr
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r51Nondeg, Defined, eval, Interp.real, hkkn, hkkn2, hkkp, hkkq, hkkr] at h
  have epq : intValue? (env "p" + env "q") = some (kp + kq) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkq,
        (intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1233r51Nondeg.body →
      (kn < 0 → w ≠ 0) ∧ (kn2 < 0 → w ≠ 0) ∧ (kq < 0 → env "d" + env "e" * w ^ kn ≠ 0) ∧
          (kr < 0 → env "f" + env "g" * w ^ kn ≠ 0) ∧ (kp < 0 → env "a" + env "c" * w ^ kn2 ≠ 0) :=
          by
    intro w h
    simp [rubi1233r51Nondeg, Defined, eval, Interp.real, hkkn, hkkn2, hkkp, hkkq, hkkr] at h ⊢
    tauto
  have hn2 : kn2 = kn * 2 := by
    have h := hn2e
    rw [(intValue?_eq _ _).1 hkkn2, (intValue?_eq _ _).1 hkkn] at h
    have h' : ((kn2 : ℤ) : ℝ) = ((kn * 2 : ℤ) : ℝ) := by push_cast; rw [h]; ring
    exact_mod_cast h'
  have hX2 : ∀ w : ℝ, w ^ kn2 = (w ^ kn) ^ 2 := by
    intro w
    rw [hn2, zpow_mul]
    norm_num
  have hfac : ∀ w, env "a" + env "c" * w ^ kn2 = (env "d" + env "e" * w ^ kn) *
      (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ kn) := by
    intro w
    rw [hX2 w]
    generalize w ^ kn = Y
    field_simp
    first
    | linear_combination Y * hrel
    | linear_combination (-Y) * hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1233r51Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hw0, hw2, hL, hG, hQ⟩ := hD w hw
    have hQLM : env "a" + env "c" * w ^ kn2 ≠ 0 → env "d" + env "e" * w ^ kn ≠ 0 ∧ env "a" *
        (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ kn ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : kq + kp < 0 → env "d" + env "e" * w ^ kn ≠ 0 := fun h => by
      by_cases hm : kq < 0
      · exact hL hm
      · exact (hQLM (hQ (by omega))).1
    have f1' : kp + kq < 0 → env "d" + env "e" * w ^ kn ≠ 0 := fun h => f1 (by omega)
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.real, hkkn, hkkp, hkkr, epq, ivm1R] at hw0 hw2 hL hG hQ f1 f1' f2 ⊢
    clear hfac hX2 hD hF hc hw hQLM
    repeat' constructor
    all_goals assumption
  · filter_upwards with w
    simp [rubi1233r51Nondeg, Defined, recEnv]
  · simp only [rubi1233r51Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ kn) ^ (kp + kq) *
        (env "f" + env "g" * t ^ kn) ^ kr *
        (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ kn) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkkn, hkkp, hkkr, epq, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1233r51Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1233r51Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1233r51Nondeg, eval, recEnv]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1233r51Nondeg.body =
        (env "d" + env "e" * t ^ kn) ^ kq * (env "f" + env "g" * t ^ kn) ^ kr *
        (env "a" + env "c" * t ^ kn2) ^ kp := by
      simp [rubi1233r51Nondeg, eval, Interp.real, hkkn, hkkn2, hkkp, hkkq, hkkr]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨-, -, hL, -, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "c" * t ^ kn2 ≠ 0 → env "d" + env "e" * t ^ kn ≠ 0 ∧ env "a" *
        (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ kn ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "d" + env "e" * t ^ kn) ^ kq * (env "d" + env "e" * t ^ kn) ^ kp =
        (env "d" + env "e" * t ^ kn) ^ (kp + kq) := by
      rw [show kp + kq = kq + kp by ring]
      apply zmerge
      by_cases hL0 : env "d" + env "e" * t ^ kn = 0
      · right
        constructor
        · by_contra hm; exact hL (by omega) hL0
        · by_contra hp; exact (hQLM (hQ (by omega))).1 hL0
      · exact Or.inl hL0
    rw [hfac t, mul_zpow (env "d" + env "e" * t ^ kn), ← hmerge]
    ring

theorem rubi1233r51Nondeg_complex : rubi1233r51Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1233r51Nondeg.conditions rubi1233r51Nondeg.body
    rubi1233r51Nondeg.result rubi1233r51Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1233r51Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1233r51Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1233r51Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  have hn2e : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1233r51Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r51Nondeg, Defined, eval, Interp.complex, hkkn] at h
  rcases hkkn2 : intValue? (env "n2") with _ | kn2
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r51Nondeg, Defined, eval, Interp.complex, hkkn, hkkn2] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r51Nondeg, Defined, eval, Interp.complex, hkkn, hkkn2, hkkp] at h
  rcases hkkq : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r51Nondeg, Defined, eval, Interp.complex, hkkn, hkkn2, hkkp, hkkq] at h
  rcases hkkr : intValue? (env "r") with _ | kr
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r51Nondeg, Defined, eval, Interp.complex, hkkn, hkkn2, hkkp, hkkq, hkkr] at h
  have epq : intValue? (env "p" + env "q") = some (kp + kq) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkq,
        (intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1233r51Nondeg.body →
      (kn < 0 → w ≠ 0) ∧ (kn2 < 0 → w ≠ 0) ∧ (kq < 0 → env "d" + env "e" * w ^ kn ≠ 0) ∧
          (kr < 0 → env "f" + env "g" * w ^ kn ≠ 0) ∧ (kp < 0 → env "a" + env "c" * w ^ kn2 ≠ 0) :=
          by
    intro w h
    simp [rubi1233r51Nondeg, Defined, eval, Interp.complex, hkkn, hkkn2, hkkp, hkkq, hkkr] at h ⊢
    tauto
  have hn2 : kn2 = kn * 2 := by
    have h := hn2e
    rw [(intValue?_eq _ _).1 hkkn2, (intValue?_eq _ _).1 hkkn] at h
    have h' : ((kn2 : ℤ) : ℂ) = ((kn * 2 : ℤ) : ℂ) := by push_cast; rw [h]; ring
    exact_mod_cast h'
  have hX2 : ∀ w : ℂ, w ^ kn2 = (w ^ kn) ^ 2 := by
    intro w
    rw [hn2, zpow_mul]
    norm_num
  have hfac : ∀ w, env "a" + env "c" * w ^ kn2 = (env "d" + env "e" * w ^ kn) *
      (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ kn) := by
    intro w
    rw [hX2 w]
    generalize w ^ kn = Y
    field_simp
    first
    | linear_combination Y * hrel
    | linear_combination (-Y) * hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1233r51Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hw0, hw2, hL, hG, hQ⟩ := hD w hw
    have hQLM : env "a" + env "c" * w ^ kn2 ≠ 0 → env "d" + env "e" * w ^ kn ≠ 0 ∧ env "a" *
        (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ kn ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : kq + kp < 0 → env "d" + env "e" * w ^ kn ≠ 0 := fun h => by
      by_cases hm : kq < 0
      · exact hL hm
      · exact (hQLM (hQ (by omega))).1
    have f1' : kp + kq < 0 → env "d" + env "e" * w ^ kn ≠ 0 := fun h => f1 (by omega)
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.complex, hkkn, hkkp, hkkr, epq,
        ivm1C] at hw0 hw2 hL hG hQ f1 f1' f2 ⊢
    clear hfac hX2 hD hF hc hw hQLM
    repeat' constructor
    all_goals assumption
  · filter_upwards with w
    simp [rubi1233r51Nondeg, Defined, recEnv]
  · simp only [rubi1233r51Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ kn) ^ (kp + kq) *
        (env "f" + env "g" * t ^ kn) ^ kr *
        (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ kn) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkkn, hkkp, hkkr, epq, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1233r51Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1233r51Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1233r51Nondeg, eval, recEnv]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1233r51Nondeg.body =
        (env "d" + env "e" * t ^ kn) ^ kq * (env "f" + env "g" * t ^ kn) ^ kr *
        (env "a" + env "c" * t ^ kn2) ^ kp := by
      simp [rubi1233r51Nondeg, eval, Interp.complex, hkkn, hkkn2, hkkp, hkkq, hkkr]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨-, -, hL, -, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "c" * t ^ kn2 ≠ 0 → env "d" + env "e" * t ^ kn ≠ 0 ∧ env "a" *
        (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ kn ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "d" + env "e" * t ^ kn) ^ kq * (env "d" + env "e" * t ^ kn) ^ kp =
        (env "d" + env "e" * t ^ kn) ^ (kp + kq) := by
      rw [show kp + kq = kq + kp by ring]
      apply zmerge
      by_cases hL0 : env "d" + env "e" * t ^ kn = 0
      · right
        constructor
        · by_contra hm; exact hL (by omega) hL0
        · by_contra hp; exact (hQLM (hQ (by omega))).1 hL0
      · exact Or.inl hL0
    rw [hfac t, mul_zpow (env "d" + env "e" * t ^ kn), ← hmerge]
    ring

/-! ## rubi1233r11Nondeg -/

theorem rubi1233r11Nondeg_real : rubi1233r11Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1233r11Nondeg.conditions rubi1233r11Nondeg.body
    rubi1233r11Nondeg.result rubi1233r11Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1233r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1233r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "d" ^ 2 - env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1233r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, sub_eq_add_neg] using h
  have hn2e : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1233r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r11Nondeg, Defined, eval, Interp.real, hkkn] at h
  rcases hkkn2 : intValue? (env "n2") with _ | kn2
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r11Nondeg, Defined, eval, Interp.real, hkkn, hkkn2] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r11Nondeg, Defined, eval, Interp.real, hkkn, hkkn2, hkkp] at h
  rcases hkkq : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r11Nondeg, Defined, eval, Interp.real, hkkn, hkkn2, hkkp, hkkq] at h
  have epq : intValue? (env "p" + env "q") = some (kp + kq) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkq,
        (intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1233r11Nondeg.body →
      (kn < 0 → w ≠ 0) ∧ (kn2 < 0 → w ≠ 0) ∧ (kq < 0 → env "d" + env "e" * w ^ kn ≠ 0) ∧
          (kp < 0 → env "a" + env "b" * w ^ kn + env "c" * w ^ kn2 ≠ 0) := by
    intro w h
    simp [rubi1233r11Nondeg, Defined, eval, Interp.real, hkkn, hkkn2, hkkp, hkkq] at h ⊢
    tauto
  have hn2 : kn2 = kn * 2 := by
    have h := hn2e
    rw [(intValue?_eq _ _).1 hkkn2, (intValue?_eq _ _).1 hkkn] at h
    have h' : ((kn2 : ℤ) : ℝ) = ((kn * 2 : ℤ) : ℝ) := by push_cast; rw [h]; ring
    exact_mod_cast h'
  have hX2 : ∀ w : ℝ, w ^ kn2 = (w ^ kn) ^ 2 := by
    intro w
    rw [hn2, zpow_mul]
    norm_num
  have hfac : ∀ w, env "a" + env "b" * w ^ kn + env "c" * w ^ kn2 = (env "d" + env "e" * w ^ kn) *
      (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ kn) := by
    intro w
    rw [hX2 w]
    generalize w ^ kn = Y
    field_simp
    first
    | linear_combination Y * hrel
    | linear_combination (-Y) * hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1233r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hw0, hw2, hL, hQ⟩ := hD w hw
    have hQLM : env "a" + env "b" * w ^ kn + env "c" * w ^ kn2 ≠ 0 → env "d" + env "e" *
        w ^ kn ≠ 0 ∧ env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ kn ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : kq + kp < 0 → env "d" + env "e" * w ^ kn ≠ 0 := fun h => by
      by_cases hm : kq < 0
      · exact hL hm
      · exact (hQLM (hQ (by omega))).1
    have f1' : kp + kq < 0 → env "d" + env "e" * w ^ kn ≠ 0 := fun h => f1 (by omega)
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.real, hkkn, hkkp, epq, ivm1R] at hw0 hw2 hL hQ f1 f1' f2 ⊢
    clear hfac hX2 hD hF hc hw hQLM
    repeat' constructor
    all_goals assumption
  · filter_upwards with w
    simp [rubi1233r11Nondeg, Defined, recEnv]
  · simp only [rubi1233r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ kn) ^ (kp + kq) *
        (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ kn) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkkn, hkkp, epq, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1233r11Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1233r11Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1233r11Nondeg, eval, recEnv]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1233r11Nondeg.body =
        (env "d" + env "e" * t ^ kn) ^ kq *
        (env "a" + env "b" * t ^ kn + env "c" * t ^ kn2) ^ kp := by
      simp [rubi1233r11Nondeg, eval, Interp.real, hkkn, hkkn2, hkkp, hkkq]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨-, -, hL, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "b" * t ^ kn + env "c" * t ^ kn2 ≠ 0 → env "d" + env "e" *
        t ^ kn ≠ 0 ∧ env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ kn ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "d" + env "e" * t ^ kn) ^ kq * (env "d" + env "e" * t ^ kn) ^ kp =
        (env "d" + env "e" * t ^ kn) ^ (kp + kq) := by
      rw [show kp + kq = kq + kp by ring]
      apply zmerge
      by_cases hL0 : env "d" + env "e" * t ^ kn = 0
      · right
        constructor
        · by_contra hm; exact hL (by omega) hL0
        · by_contra hp; exact (hQLM (hQ (by omega))).1 hL0
      · exact Or.inl hL0
    rw [hfac t, mul_zpow (env "d" + env "e" * t ^ kn), ← hmerge]
    ring

theorem rubi1233r11Nondeg_complex : rubi1233r11Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1233r11Nondeg.conditions rubi1233r11Nondeg.body
    rubi1233r11Nondeg.result rubi1233r11Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1233r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1233r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "d" ^ 2 - env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1233r11Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C, sub_eq_add_neg] using h
  have hn2e : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1233r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r11Nondeg, Defined, eval, Interp.complex, hkkn] at h
  rcases hkkn2 : intValue? (env "n2") with _ | kn2
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r11Nondeg, Defined, eval, Interp.complex, hkkn, hkkn2] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r11Nondeg, Defined, eval, Interp.complex, hkkn, hkkn2, hkkp] at h
  rcases hkkq : intValue? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r11Nondeg, Defined, eval, Interp.complex, hkkn, hkkn2, hkkp, hkkq] at h
  have epq : intValue? (env "p" + env "q") = some (kp + kq) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkq,
        (intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1233r11Nondeg.body →
      (kn < 0 → w ≠ 0) ∧ (kn2 < 0 → w ≠ 0) ∧ (kq < 0 → env "d" + env "e" * w ^ kn ≠ 0) ∧
          (kp < 0 → env "a" + env "b" * w ^ kn + env "c" * w ^ kn2 ≠ 0) := by
    intro w h
    simp [rubi1233r11Nondeg, Defined, eval, Interp.complex, hkkn, hkkn2, hkkp, hkkq] at h ⊢
    tauto
  have hn2 : kn2 = kn * 2 := by
    have h := hn2e
    rw [(intValue?_eq _ _).1 hkkn2, (intValue?_eq _ _).1 hkkn] at h
    have h' : ((kn2 : ℤ) : ℂ) = ((kn * 2 : ℤ) : ℂ) := by push_cast; rw [h]; ring
    exact_mod_cast h'
  have hX2 : ∀ w : ℂ, w ^ kn2 = (w ^ kn) ^ 2 := by
    intro w
    rw [hn2, zpow_mul]
    norm_num
  have hfac : ∀ w, env "a" + env "b" * w ^ kn + env "c" * w ^ kn2 = (env "d" + env "e" * w ^ kn) *
      (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ kn) := by
    intro w
    rw [hX2 w]
    generalize w ^ kn = Y
    field_simp
    first
    | linear_combination Y * hrel
    | linear_combination (-Y) * hrel
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1233r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hw0, hw2, hL, hQ⟩ := hD w hw
    have hQLM : env "a" + env "b" * w ^ kn + env "c" * w ^ kn2 ≠ 0 → env "d" + env "e" *
        w ^ kn ≠ 0 ∧ env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ kn ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : kq + kp < 0 → env "d" + env "e" * w ^ kn ≠ 0 := fun h => by
      by_cases hm : kq < 0
      · exact hL hm
      · exact (hQLM (hQ (by omega))).1
    have f1' : kp + kq < 0 → env "d" + env "e" * w ^ kn ≠ 0 := fun h => f1 (by omega)
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.complex, hkkn, hkkp, epq, ivm1C] at hw0 hw2 hL hQ f1 f1' f2 ⊢
    clear hfac hX2 hD hF hc hw hQLM
    repeat' constructor
    all_goals assumption
  · filter_upwards with w
    simp [rubi1233r11Nondeg, Defined, recEnv]
  · simp only [rubi1233r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ kn) ^ (kp + kq) *
        (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ kn) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkkn, hkkp, epq, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1233r11Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1233r11Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1233r11Nondeg, eval, recEnv]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1233r11Nondeg.body =
        (env "d" + env "e" * t ^ kn) ^ kq *
        (env "a" + env "b" * t ^ kn + env "c" * t ^ kn2) ^ kp := by
      simp [rubi1233r11Nondeg, eval, Interp.complex, hkkn, hkkn2, hkkp, hkkq]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨-, -, hL, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "b" * t ^ kn + env "c" * t ^ kn2 ≠ 0 → env "d" + env "e" *
        t ^ kn ≠ 0 ∧ env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t ^ kn ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "d" + env "e" * t ^ kn) ^ kq * (env "d" + env "e" * t ^ kn) ^ kp =
        (env "d" + env "e" * t ^ kn) ^ (kp + kq) := by
      rw [show kp + kq = kq + kp by ring]
      apply zmerge
      by_cases hL0 : env "d" + env "e" * t ^ kn = 0
      · right
        constructor
        · by_contra hm; exact hL (by omega) hL0
        · by_contra hp; exact (hQLM (hQ (by omega))).1 hL0
      · exact Or.inl hL0
    rw [hfac t, mul_zpow (env "d" + env "e" * t ^ kn), ← hmerge]
    ring

end OSR.IntegrationRec267
