import OSR.IntegrationNum1

/-! # Strengthened algebraic variants: quadratic factors split by a linear factor

Proofs of RUBI 1.2.1.2 #2, 1.2.1.3 #21, #37 and 1.2.1.4 #4 over ℝ and ℂ: when `c d² + a e² = 0`,
`a + c x² = (d + e x) (a / d + c x / e)`, so `(d + e x)^m (a + c x²)^p` equals
`(d + e x)^(m + p) (a / d + c x / e)^p` (the powers merge when `d + e x ≠ 0` or both exponents are
nonnegative, and `d + e x = 0` forces `a + c x² = 0`). -/

namespace OSR.IntegrationRec266

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

/-! ## rubi1212r2Nondeg -/

theorem rubi1212r2Nondeg_real : rubi1212r2Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1212r2Nondeg.conditions rubi1212r2Nondeg.body
    rubi1212r2Nondeg.result rubi1212r2Nondeg.integrals
  intro env hc t hF
  have h0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1212r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1212r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2)))
      (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hfac : ∀ w, env "a" + env "c" * w ^ 2 = (env "d" + env "e" * w) *
      (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w) := by
    intro w
    field_simp
    first
    | linear_combination w * hrel
    | linear_combination (-w) * hrel
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r2Nondeg, Defined, eval, Interp.real, hkkm, iv2R] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r2Nondeg, Defined, eval, Interp.real, hkkm, hkkp, iv2R] at h
  have emp : intValue? (env "m" + env "p") = some (km + kp) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm,
        (intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1212r2Nondeg.body →
      (km < 0 → env "d" + env "e" * w ≠ 0) ∧ (kp < 0 → env "a" + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1212r2Nondeg, Defined, eval, Interp.real, hkkm, hkkp, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hL, hQ⟩ := hD w hw
    have hQLM : env "a" + env "c" * w ^ 2 ≠ 0 → env "d" + env "e" * w ≠ 0 ∧ env "a" * (env "d")⁻¹ +
        env "c" * (env "e")⁻¹ * w ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : km + kp < 0 → env "d" + env "e" * w ≠ 0 := fun h => by
      by_cases hm : km < 0
      · exact hL hm
      · exact (hQLM (hQ (by omega))).1
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.real, hkkp, emp, ivm1R]
    tauto
  · filter_upwards with w
    simp [rubi1212r2Nondeg, Defined, recEnv]
  · simp only [rubi1212r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (km + kp) *
        (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkkp, emp, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1212r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1212r2Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1212r2Nondeg, eval, recEnv]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1212r2Nondeg.body =
        (env "d" + env "e" * t) ^ km * (env "a" + env "c" * t ^ 2) ^ kp := by
      simp [rubi1212r2Nondeg, eval, Interp.real, hkkm, hkkp, iv2R]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨hL, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "c" * t ^ 2 ≠ 0 → env "d" + env "e" * t ≠ 0 ∧ env "a" * (env "d")⁻¹ +
        env "c" * (env "e")⁻¹ * t ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "d" + env "e" * t) ^ km * (env "d" + env "e" * t) ^ kp =
        (env "d" + env "e" * t) ^ (km + kp) := by
      apply zmerge
      by_cases hL0 : env "d" + env "e" * t = 0
      · right
        constructor
        · by_contra hm; exact hL (by omega) hL0
        · by_contra hp; exact (hQLM (hQ (by omega))).1 hL0
      · exact Or.inl hL0
    rw [hfac t, mul_zpow, ← hmerge]
    ring
theorem rubi1212r2Nondeg_complex : rubi1212r2Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1212r2Nondeg.conditions rubi1212r2Nondeg.body
    rubi1212r2Nondeg.result rubi1212r2Nondeg.integrals
  intro env hc t hF
  have h0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1212r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1212r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2)))
      (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r2Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hfac : ∀ w, env "a" + env "c" * w ^ 2 = (env "d" + env "e" * w) *
      (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w) := by
    intro w
    field_simp
    first
    | linear_combination w * hrel
    | linear_combination (-w) * hrel
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r2Nondeg, Defined, eval, Interp.complex, hkkm, iv2C] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r2Nondeg, Defined, eval, Interp.complex, hkkm, hkkp, iv2C] at h
  have emp : intValue? (env "m" + env "p") = some (km + kp) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm,
        (intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1212r2Nondeg.body →
      (km < 0 → env "d" + env "e" * w ≠ 0) ∧ (kp < 0 → env "a" + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1212r2Nondeg, Defined, eval, Interp.complex, hkkm, hkkp, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r2Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hL, hQ⟩ := hD w hw
    have hQLM : env "a" + env "c" * w ^ 2 ≠ 0 → env "d" + env "e" * w ≠ 0 ∧ env "a" * (env "d")⁻¹ +
        env "c" * (env "e")⁻¹ * w ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : km + kp < 0 → env "d" + env "e" * w ≠ 0 := fun h => by
      by_cases hm : km < 0
      · exact hL hm
      · exact (hQLM (hQ (by omega))).1
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.complex, hkkp, emp, ivm1C]
    tauto
  · filter_upwards with w
    simp [rubi1212r2Nondeg, Defined, recEnv]
  · simp only [rubi1212r2Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (km + kp) *
        (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkkp, emp, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1212r2Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1212r2Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1212r2Nondeg, eval, recEnv]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1212r2Nondeg.body =
        (env "d" + env "e" * t) ^ km * (env "a" + env "c" * t ^ 2) ^ kp := by
      simp [rubi1212r2Nondeg, eval, Interp.complex, hkkm, hkkp, iv2C]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨hL, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "c" * t ^ 2 ≠ 0 → env "d" + env "e" * t ≠ 0 ∧ env "a" * (env "d")⁻¹ +
        env "c" * (env "e")⁻¹ * t ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "d" + env "e" * t) ^ km * (env "d" + env "e" * t) ^ kp =
        (env "d" + env "e" * t) ^ (km + kp) := by
      apply zmerge
      by_cases hL0 : env "d" + env "e" * t = 0
      · right
        constructor
        · by_contra hm; exact hL (by omega) hL0
        · by_contra hp; exact (hQLM (hQ (by omega))).1 hL0
      · exact Or.inl hL0
    rw [hfac t, mul_zpow, ← hmerge]
    ring
/-! ## rubi1213r21Nondeg -/

theorem rubi1213r21Nondeg_real : rubi1213r21Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1213r21Nondeg.conditions rubi1213r21Nondeg.body
    rubi1213r21Nondeg.result rubi1213r21Nondeg.integrals
  intro env hc t hF
  have h0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1213r21Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1213r21Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2)))
      (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r21Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hfac : ∀ w, env "a" + env "c" * w ^ 2 = (env "d" + env "e" * w) *
      (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w) := by
    intro w
    field_simp
    first
    | linear_combination w * hrel
    | linear_combination (-w) * hrel
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r21Nondeg, Defined, eval, Interp.real, hkkm, iv2R] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r21Nondeg, Defined, eval, Interp.real, hkkm, hkkp, iv2R] at h
  have emp : intValue? (env "m" + env "p") = some (km + kp) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm,
        (intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1213r21Nondeg.body →
      (km < 0 → env "d" + env "e" * w ≠ 0) ∧ (kp < 0 → env "a" + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1213r21Nondeg, Defined, eval, Interp.real, hkkm, hkkp, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r21Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hL, hQ⟩ := hD w hw
    have hQLM : env "a" + env "c" * w ^ 2 ≠ 0 → env "d" + env "e" * w ≠ 0 ∧ env "a" * (env "d")⁻¹ +
        env "c" * (env "e")⁻¹ * w ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : km + kp < 0 → env "d" + env "e" * w ≠ 0 := fun h => by
      by_cases hm : km < 0
      · exact hL hm
      · exact (hQLM (hQ (by omega))).1
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.real, hkkp, emp, ivm1R]
    tauto
  · filter_upwards with w
    simp [rubi1213r21Nondeg, Defined, recEnv]
  · simp only [rubi1213r21Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (km + kp) * (env "f" + env "g" * t) *
        (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkkp, emp, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1213r21Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r21Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1213r21Nondeg, eval, recEnv]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1213r21Nondeg.body =
        (env "d" + env "e" * t) ^ km * (env "f" + env "g" * t) *
        (env "a" + env "c" * t ^ 2) ^ kp := by
      simp [rubi1213r21Nondeg, eval, Interp.real, hkkm, hkkp, iv2R]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨hL, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "c" * t ^ 2 ≠ 0 → env "d" + env "e" * t ≠ 0 ∧ env "a" * (env "d")⁻¹ +
        env "c" * (env "e")⁻¹ * t ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "d" + env "e" * t) ^ km * (env "d" + env "e" * t) ^ kp =
        (env "d" + env "e" * t) ^ (km + kp) := by
      apply zmerge
      by_cases hL0 : env "d" + env "e" * t = 0
      · right
        constructor
        · by_contra hm; exact hL (by omega) hL0
        · by_contra hp; exact (hQLM (hQ (by omega))).1 hL0
      · exact Or.inl hL0
    rw [hfac t, mul_zpow, ← hmerge]
    ring
theorem rubi1213r21Nondeg_complex : rubi1213r21Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1213r21Nondeg.conditions rubi1213r21Nondeg.body
    rubi1213r21Nondeg.result rubi1213r21Nondeg.integrals
  intro env hc t hF
  have h0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1213r21Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1213r21Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2)))
      (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r21Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hfac : ∀ w, env "a" + env "c" * w ^ 2 = (env "d" + env "e" * w) *
      (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w) := by
    intro w
    field_simp
    first
    | linear_combination w * hrel
    | linear_combination (-w) * hrel
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r21Nondeg, Defined, eval, Interp.complex, hkkm, iv2C] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r21Nondeg, Defined, eval, Interp.complex, hkkm, hkkp, iv2C] at h
  have emp : intValue? (env "m" + env "p") = some (km + kp) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm,
        (intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1213r21Nondeg.body →
      (km < 0 → env "d" + env "e" * w ≠ 0) ∧ (kp < 0 → env "a" + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1213r21Nondeg, Defined, eval, Interp.complex, hkkm, hkkp, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r21Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hL, hQ⟩ := hD w hw
    have hQLM : env "a" + env "c" * w ^ 2 ≠ 0 → env "d" + env "e" * w ≠ 0 ∧ env "a" * (env "d")⁻¹ +
        env "c" * (env "e")⁻¹ * w ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : km + kp < 0 → env "d" + env "e" * w ≠ 0 := fun h => by
      by_cases hm : km < 0
      · exact hL hm
      · exact (hQLM (hQ (by omega))).1
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.complex, hkkp, emp, ivm1C]
    tauto
  · filter_upwards with w
    simp [rubi1213r21Nondeg, Defined, recEnv]
  · simp only [rubi1213r21Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (km + kp) * (env "f" + env "g" * t) *
        (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkkp, emp, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1213r21Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r21Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1213r21Nondeg, eval, recEnv]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1213r21Nondeg.body =
        (env "d" + env "e" * t) ^ km * (env "f" + env "g" * t) *
        (env "a" + env "c" * t ^ 2) ^ kp := by
      simp [rubi1213r21Nondeg, eval, Interp.complex, hkkm, hkkp, iv2C]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨hL, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "c" * t ^ 2 ≠ 0 → env "d" + env "e" * t ≠ 0 ∧ env "a" * (env "d")⁻¹ +
        env "c" * (env "e")⁻¹ * t ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "d" + env "e" * t) ^ km * (env "d" + env "e" * t) ^ kp =
        (env "d" + env "e" * t) ^ (km + kp) := by
      apply zmerge
      by_cases hL0 : env "d" + env "e" * t = 0
      · right
        constructor
        · by_contra hm; exact hL (by omega) hL0
        · by_contra hp; exact (hQLM (hQ (by omega))).1 hL0
      · exact Or.inl hL0
    rw [hfac t, mul_zpow, ← hmerge]
    ring
/-! ## rubi1214r4Nondeg -/

theorem rubi1214r4Nondeg_real : rubi1214r4Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1214r4Nondeg.conditions rubi1214r4Nondeg.body
    rubi1214r4Nondeg.result rubi1214r4Nondeg.integrals
  intro env hc t hF
  have h0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1214r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1214r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2)))
      (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1214r4Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hfac : ∀ w, env "a" + env "c" * w ^ 2 = (env "d" + env "e" * w) *
      (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w) := by
    intro w
    field_simp
    first
    | linear_combination w * hrel
    | linear_combination (-w) * hrel
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1214r4Nondeg, Defined, eval, Interp.real, hkkm, iv2R] at h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1214r4Nondeg, Defined, eval, Interp.real, hkkm, hkkn, iv2R] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1214r4Nondeg, Defined, eval, Interp.real, hkkm, hkkn, hkkp, iv2R] at h
  have emp : intValue? (env "m" + env "p") = some (km + kp) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm,
        (intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1214r4Nondeg.body →
      (km < 0 → env "d" + env "e" * w ≠ 0) ∧ (kn < 0 → env "f" + env "g" * w ≠ 0) ∧
          (kp < 0 → env "a" + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1214r4Nondeg, Defined, eval, Interp.real, hkkm, hkkn, hkkp, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1214r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hL, hG, hQ⟩ := hD w hw
    have hQLM : env "a" + env "c" * w ^ 2 ≠ 0 → env "d" + env "e" * w ≠ 0 ∧ env "a" * (env "d")⁻¹ +
        env "c" * (env "e")⁻¹ * w ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : km + kp < 0 → env "d" + env "e" * w ≠ 0 := fun h => by
      by_cases hm : km < 0
      · exact hL hm
      · exact (hQLM (hQ (by omega))).1
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.real, hkkn, hkkp, emp, ivm1R]
    tauto
  · filter_upwards with w
    simp [rubi1214r4Nondeg, Defined, recEnv]
  · simp only [rubi1214r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (km + kp) *
        (env "f" + env "g" * t) ^ kn *
        (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkkn, hkkp, emp, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1214r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1214r4Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1214r4Nondeg, eval, recEnv]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1214r4Nondeg.body =
        (env "d" + env "e" * t) ^ km * (env "f" + env "g" * t) ^ kn *
        (env "a" + env "c" * t ^ 2) ^ kp := by
      simp [rubi1214r4Nondeg, eval, Interp.real, hkkm, hkkn, hkkp, iv2R]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨hL, hG, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "c" * t ^ 2 ≠ 0 → env "d" + env "e" * t ≠ 0 ∧ env "a" * (env "d")⁻¹ +
        env "c" * (env "e")⁻¹ * t ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "d" + env "e" * t) ^ km * (env "d" + env "e" * t) ^ kp =
        (env "d" + env "e" * t) ^ (km + kp) := by
      apply zmerge
      by_cases hL0 : env "d" + env "e" * t = 0
      · right
        constructor
        · by_contra hm; exact hL (by omega) hL0
        · by_contra hp; exact (hQLM (hQ (by omega))).1 hL0
      · exact Or.inl hL0
    rw [hfac t, mul_zpow, ← hmerge]
    ring
theorem rubi1214r4Nondeg_complex : rubi1214r4Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1214r4Nondeg.conditions rubi1214r4Nondeg.body
    rubi1214r4Nondeg.result rubi1214r4Nondeg.integrals
  intro env hc t hF
  have h0 : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1214r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1214r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2)))
      (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1214r4Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hfac : ∀ w, env "a" + env "c" * w ^ 2 = (env "d" + env "e" * w) *
      (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w) := by
    intro w
    field_simp
    first
    | linear_combination w * hrel
    | linear_combination (-w) * hrel
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1214r4Nondeg, Defined, eval, Interp.complex, hkkm, iv2C] at h
  rcases hkkn : intValue? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1214r4Nondeg, Defined, eval, Interp.complex, hkkm, hkkn, iv2C] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1214r4Nondeg, Defined, eval, Interp.complex, hkkm, hkkn, hkkp, iv2C] at h
  have emp : intValue? (env "m" + env "p") = some (km + kp) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkm,
        (intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1214r4Nondeg.body →
      (km < 0 → env "d" + env "e" * w ≠ 0) ∧ (kn < 0 → env "f" + env "g" * w ≠ 0) ∧
          (kp < 0 → env "a" + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1214r4Nondeg, Defined, eval, Interp.complex, hkkm, hkkn, hkkp, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1214r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hL, hG, hQ⟩ := hD w hw
    have hQLM : env "a" + env "c" * w ^ 2 ≠ 0 → env "d" + env "e" * w ≠ 0 ∧ env "a" * (env "d")⁻¹ +
        env "c" * (env "e")⁻¹ * w ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : km + kp < 0 → env "d" + env "e" * w ≠ 0 := fun h => by
      by_cases hm : km < 0
      · exact hL hm
      · exact (hQLM (hQ (by omega))).1
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.complex, hkkn, hkkp, emp, ivm1C]
    tauto
  · filter_upwards with w
    simp [rubi1214r4Nondeg, Defined, recEnv]
  · simp only [rubi1214r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (km + kp) *
        (env "f" + env "g" * t) ^ kn *
        (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * t) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkkn, hkkp, emp, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1214r4Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1214r4Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1214r4Nondeg, eval, recEnv]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1214r4Nondeg.body =
        (env "d" + env "e" * t) ^ km * (env "f" + env "g" * t) ^ kn *
        (env "a" + env "c" * t ^ 2) ^ kp := by
      simp [rubi1214r4Nondeg, eval, Interp.complex, hkkm, hkkn, hkkp, iv2C]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨hL, hG, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "c" * t ^ 2 ≠ 0 → env "d" + env "e" * t ≠ 0 ∧ env "a" * (env "d")⁻¹ +
        env "c" * (env "e")⁻¹ * t ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "d" + env "e" * t) ^ km * (env "d" + env "e" * t) ^ kp =
        (env "d" + env "e" * t) ^ (km + kp) := by
      apply zmerge
      by_cases hL0 : env "d" + env "e" * t = 0
      · right
        constructor
        · by_contra hm; exact hL (by omega) hL0
        · by_contra hp; exact (hQLM (hQ (by omega))).1 hL0
      · exact Or.inl hL0
    rw [hfac t, mul_zpow, ← hmerge]
    ring
/-! ## rubi1213r37Nondeg -/

theorem rubi1213r37Nondeg_real : rubi1213r37Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1213r37Nondeg.conditions rubi1213r37Nondeg.body
    rubi1213r37Nondeg.result rubi1213r37Nondeg.integrals
  intro env hc t hF
  have h0 : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi1213r37Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "g" ≠ 0 := by
    have h := hc (.ne (.var "g") (.int 0)) (by simp [rubi1213r37Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "f" ^ 2 + env "a" * env "g" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "f") (.int 2)))
      (.app2 .mul (.var "a") (.pow (.var "g") (.int 2)))) (.int 0)) (by simp [rubi1213r37Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hfac : ∀ w, env "a" + env "c" * w ^ 2 = (env "f" + env "g" * w) *
      (env "a" * (env "f")⁻¹ + env "c" * (env "g")⁻¹ * w) := by
    intro w
    field_simp
    first
    | linear_combination w * hrel
    | linear_combination (-w) * hrel
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r37Nondeg, Defined, eval, Interp.real, hkkm, iv2R] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r37Nondeg, Defined, eval, Interp.real, hkkm, hkkp, iv2R] at h
  have ep1 : intValue? (env "p" + 1) = some (kp + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi1213r37Nondeg.body →
      (km < 0 → env "d" + env "e" * w ≠ 0) ∧ (kp < 0 → env "a" + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1213r37Nondeg, Defined, eval, Interp.real, hkkm, hkkp, iv2R] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r37Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hL, hQ⟩ := hD w hw
    have hQLM : env "a" + env "c" * w ^ 2 ≠ 0 → env "f" + env "g" * w ≠ 0 ∧ env "a" * (env "f")⁻¹ +
        env "c" * (env "g")⁻¹ * w ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : kp + 1 < 0 → env "f" + env "g" * w ≠ 0 := fun h => (hQLM (hQ (by omega))).1
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.real, hkkm, hkkp, ep1, ivm1R]
    tauto
  · filter_upwards with w
    simp [rubi1213r37Nondeg, Defined, recEnv]
  · simp only [rubi1213r37Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ km *
        (env "f" + env "g" * t) ^ (kp + 1) *
        (env "a" * (env "f")⁻¹ + env "c" * (env "g")⁻¹ * t) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hkkm, hkkp, ep1, ivm1R]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi1213r37Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r37Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1213r37Nondeg, eval, recEnv]
    have hEF : eval Interp.real (Function.update env "x" t) rubi1213r37Nondeg.body =
        (env "d" + env "e" * t) ^ km * (env "f" + env "g" * t) *
        (env "a" + env "c" * t ^ 2) ^ kp := by
      simp [rubi1213r37Nondeg, eval, Interp.real, hkkm, hkkp, iv2R]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨hL, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "c" * t ^ 2 ≠ 0 → env "f" + env "g" * t ≠ 0 ∧ env "a" * (env "f")⁻¹ +
        env "c" * (env "g")⁻¹ * t ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "f" + env "g" * t) * (env "f" + env "g" * t) ^ kp =
        (env "f" + env "g" * t) ^ (kp + 1) := by
      have := zmerge (env "f" + env "g" * t) 1 kp (by
        by_cases hG0 : env "f" + env "g" * t = 0
        · right
          refine ⟨by norm_num, ?_⟩
          by_contra hp; exact (hQLM (hQ (by omega))).1 hG0
        · exact Or.inl hG0)
      rwa [zpow_one, show (1 : ℤ) + kp = kp + 1 by ring] at this
    rw [hfac t, mul_zpow, ← hmerge]
    ring
theorem rubi1213r37Nondeg_complex : rubi1213r37Nondeg.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi1213r37Nondeg.conditions rubi1213r37Nondeg.body
    rubi1213r37Nondeg.result rubi1213r37Nondeg.integrals
  intro env hc t hF
  have h0 : env "f" ≠ 0 := by
    have h := hc (.ne (.var "f") (.int 0)) (by simp [rubi1213r37Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "g" ≠ 0 := by
    have h := hc (.ne (.var "g") (.int 0)) (by simp [rubi1213r37Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hrel : env "c" * env "f" ^ 2 + env "a" * env "g" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "f") (.int 2)))
      (.app2 .mul (.var "a") (.pow (.var "g") (.int 2)))) (.int 0)) (by simp [rubi1213r37Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.complex, iv2C] using h
  have hfac : ∀ w, env "a" + env "c" * w ^ 2 = (env "f" + env "g" * w) *
      (env "a" * (env "f")⁻¹ + env "c" * (env "g")⁻¹ * w) := by
    intro w
    field_simp
    first
    | linear_combination w * hrel
    | linear_combination (-w) * hrel
  rcases hkkm : intValue? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r37Nondeg, Defined, eval, Interp.complex, hkkm, iv2C] at h
  rcases hkkp : intValue? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r37Nondeg, Defined, eval, Interp.complex, hkkm, hkkp, iv2C] at h
  have ep1 : intValue? (env "p" + 1) = some (kp + 1) :=
    (intValue?_eq _ _).2 (by rw [(intValue?_eq _ _).1 hkkp]; push_cast; ring)
  have hD : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi1213r37Nondeg.body →
      (km < 0 → env "d" + env "e" * w ≠ 0) ∧ (kp < 0 → env "a" + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1213r37Nondeg, Defined, eval, Interp.complex, hkkm, hkkp, iv2C] at h ⊢
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r37Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hL, hQ⟩ := hD w hw
    have hQLM : env "a" + env "c" * w ^ 2 ≠ 0 → env "f" + env "g" * w ≠ 0 ∧ env "a" * (env "f")⁻¹ +
        env "c" * (env "g")⁻¹ * w ≠ 0 := fun h => by
      rw [hfac w] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have f1 : kp + 1 < 0 → env "f" + env "g" * w ≠ 0 := fun h => (hQLM (hQ (by omega))).1
    have f2 := fun h => (hQLM (hQ h)).2
    simp [Defined, eval, Interp.complex, hkkm, hkkp, ep1, ivm1C]
    tauto
  · filter_upwards with w
    simp [rubi1213r37Nondeg, Defined, recEnv]
  · simp only [rubi1213r37Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ km *
        (env "f" + env "g" * t) ^ (kp + 1) *
        (env "a" * (env "f")⁻¹ + env "c" * (env "g")⁻¹ * t) ^ kp) t := by
      convert hΦ using 1
      simp [eval, Interp.complex, hkkm, hkkp, ep1, ivm1C]
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi1213r37Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi1213r37Nondeg.result) = fun w => Φ "I1" w := by
      funext w
      simp [rubi1213r37Nondeg, eval, recEnv]
    have hEF : eval Interp.complex (Function.update env "x" t) rubi1213r37Nondeg.body =
        (env "d" + env "e" * t) ^ km * (env "f" + env "g" * t) *
        (env "a" + env "c" * t ^ 2) ^ kp := by
      simp [rubi1213r37Nondeg, eval, Interp.complex, hkkm, hkkp, iv2C]
    rw [hfun, hEF]
    refine hΦ'.congr_deriv ?_
    obtain ⟨hL, hQ⟩ := hD t hF.self_of_nhds
    have hQLM : env "a" + env "c" * t ^ 2 ≠ 0 → env "f" + env "g" * t ≠ 0 ∧ env "a" * (env "f")⁻¹ +
        env "c" * (env "g")⁻¹ * t ≠ 0 := fun h => by
      rw [hfac t] at h
      exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
    have hmerge : (env "f" + env "g" * t) * (env "f" + env "g" * t) ^ kp =
        (env "f" + env "g" * t) ^ (kp + 1) := by
      have := zmerge (env "f" + env "g" * t) 1 kp (by
        by_cases hG0 : env "f" + env "g" * t = 0
        · right
          refine ⟨by norm_num, ?_⟩
          by_contra hp; exact (hQLM (hQ (by omega))).1 hG0
        · exact Or.inl hG0)
      rwa [zpow_one, show (1 : ℤ) + kp = kp + 1 by ring] at this
    rw [hfac t, mul_zpow, ← hmerge]
    ring
end OSR.IntegrationRec266
