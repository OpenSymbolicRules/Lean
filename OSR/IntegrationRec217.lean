import OSR.IntegrationNum1

/-! # Strengthened inverse hyperbolic tangent rules split into residual integrals

Proofs over ℝ of strengthened variants of `OSR.IntegrationNum1` whose result is a
constant-coefficient combination of two residual integrals: the identity
`x^2 = (d + e x^2 - d)/e` moves a power of `x` between the residual integrands. The
inverse hyperbolic tangent factor is carried unchanged. It has no complex interpretation
in the fragment, so the complex statement is vacuous and stays unproved. Each 7.3.1 rule
has a 7.3.4 twin with the same statement, which reuses its proof. -/

namespace OSR.IntegrationRec217

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

private theorem zpow_add_two_of (A : ℝ) (j : ℤ) (h : 0 ≤ j) : A ^ (j + 2) = A ^ j * A ^ 2 := by
  lift j to ℕ using h
  rw [show ((j : ℤ) + 2) = ((j + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
    pow_add]

/-! ## RUBI 7.3.1 #65 (and 7.3.4 #45): `m > 1` -/

theorem rubi731r65Nondeg_real : rubi731r65Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r65Nondeg.conditions rubi731r65Nondeg.body
    rubi731r65Nondeg.result rubi731r65Nondeg.integrals
  intro env hc t hF
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi731r65Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hmgt : 1 < env "m" := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi731r65Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpgt : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r65Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r65Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r65Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hj : 2 ≤ j := by
    have : (1 : ℝ) < j := hm ▸ hmgt
    exact_mod_cast (show (1 : ℤ) < j by exact_mod_cast this)
  have hk : 0 < k := by
    have : (0 : ℝ) < k := hp ▸ hpgt
    exact_mod_cast this
  have em : intValue? (env "m" + -2) = some (j - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have em' : intValue? (env "m" - 2) = some (j - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have em'' : intValue? (-2 + env "m") = some (j - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hj0 : ¬ j < 0 := by omega
  have hj2 : ¬ j < 2 := by omega
  have hj2' : ¬ j - 2 < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r65Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi731r65Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R] at h
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r65Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [rubi731r65Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R] at hw
      simp [Defined, eval, Interp.real, hkp, em, hj2', hk0]
      tauto
    · filter_upwards [hF] with w hw
      simp [rubi731r65Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R] at hw
      simp [Defined, eval, Interp.real, hkp, em, ivm1R, iv2R, hj2', hk0]
      tauto
  · filter_upwards with w
    simp [rubi731r65Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, he]
  · simp only [rubi731r65Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hD0 := hD t hF.self_of_nhds
    set A := eval Interp.real (Function.update env "x" t)
      (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh
        (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) with hA
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (j - 2) * A) t := by
      convert hΦ1 using 1
      simp [hA, eval, Interp.real, em, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (j - 2) * A *
        (env "d" + env "e" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [hA, eval, Interp.real, em, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r65Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r65Nondeg.result) =
        fun w => env "f" ^ 2 * (env "e")⁻¹ * Φ "I1" w +
          -env "d" * env "f" ^ 2 * (env "e")⁻¹ * Φ "I2" w := by
      funext w; simp [rubi731r65Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r65Nondeg.body =
        (env "f" * t) ^ j * A * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi731r65Nondeg, hA, eval, Interp.real, hkm, ivm1R, iv2R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hjj : (env "f" * t) ^ j = (env "f" * t) ^ (j - 2) * (env "f" * t) ^ 2 := by
      have := zpow_add_two_of (env "f" * t) (j - 2) (by omega)
      rwa [sub_add_cancel] at this
    rw [hjj]
    generalize (env "f" * t) ^ (j - 2) = P
    field_simp
    ring

theorem rubi734r45Nondeg_real : rubi734r45Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r45Nondeg.conditions rubi734r45Nondeg.body
    rubi734r45Nondeg.result rubi734r45Nondeg.integrals
  exact rubi731r65Nondeg_real

/-! ## RUBI 7.3.1 #67 (and 7.3.4 #47): `m < -1` -/

theorem rubi731r67Nondeg_real : rubi731r67Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r67Nondeg.conditions rubi731r67Nondeg.body
    rubi731r67Nondeg.result rubi731r67Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi731r67Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hmlt : env "m" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi731r67Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpgt : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r67Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r67Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r67Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hj : j < -1 := by
    have : (j : ℝ) < -1 := hm ▸ hmlt
    exact_mod_cast this
  have hk : 0 < k := by
    have : (0 : ℝ) < k := hp ▸ hpgt
    exact_mod_cast this
  have em : intValue? (env "m" + 2) = some (j + 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hjn : j < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r67Nondeg.body →
      env "f" * w ≠ 0 ∧ env "d" + env "e" * w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi731r67Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R, hjn] at h
    refine ⟨mul_ne_zero ?_ ?_, ?_⟩ <;> tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r67Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [rubi731r67Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R] at hw
      simp [Defined, eval, Interp.real, hkm, hkp, hk0]
      tauto
    · filter_upwards [hF] with w hw
      simp [rubi731r67Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R] at hw
      simp [Defined, eval, Interp.real, hkp, em, ivm1R, iv2R, hk0]
      tauto
  · have hf0 : env "f" ≠ 0 := left_ne_zero_of_mul (hBody t hF.self_of_nhds).1
    filter_upwards with w
    simp [rubi731r67Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hd, hf0]
  · simp only [rubi731r67Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨hft, hD0⟩ := hBody t hF.self_of_nhds
    have hf0 : env "f" ≠ 0 := left_ne_zero_of_mul hft
    have ht0 : t ≠ 0 := right_ne_zero_of_mul hft
    set A := eval Interp.real (Function.update env "x" t)
      (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh
        (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) with hA
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ j * A) t := by
      convert hΦ1 using 1
      simp [hA, eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (j + 2) * A *
        (env "d" + env "e" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [hA, eval, Interp.real, em, ivm1R, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r67Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r67Nondeg.result) =
        fun w => (env "d")⁻¹ * Φ "I1" w +
          -env "e" * (env "d" * env "f" ^ 2)⁻¹ * Φ "I2" w := by
      funext w; simp [rubi731r67Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r67Nondeg.body =
        (env "f" * t) ^ j * A * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi731r67Nondeg, hA, eval, Interp.real, hkm, ivm1R, iv2R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    rw [zpow_add₀ hft]
    generalize (env "f" * t) ^ j = P
    field_simp
    ring

theorem rubi734r47Nondeg_real : rubi734r47Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r47Nondeg.conditions rubi734r47Nondeg.body
    rubi734r47Nondeg.result rubi734r47Nondeg.integrals
  exact rubi731r67Nondeg_real

/-! ## The reciprocal-argument companion `rubi731r66Nondeg` -/

theorem rubi731r66Nondeg_real : rubi731r66Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r66Nondeg.conditions rubi731r66Nondeg.body
    rubi731r66Nondeg.result rubi731r66Nondeg.integrals
  intro env hc t hF
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi731r66Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hmgt : 1 < env "m" := by
    have h := hc (.gt (.var "m") (.int 1)) (by simp [rubi731r66Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpgt : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r66Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r66Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r66Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hj : 2 ≤ j := by
    have : (1 : ℝ) < j := hm ▸ hmgt
    exact_mod_cast (show (1 : ℤ) < j by exact_mod_cast this)
  have hk : 0 < k := by
    have : (0 : ℝ) < k := hp ▸ hpgt
    exact_mod_cast this
  have em : intValue? (env "m" + -2) = some (j - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have em' : intValue? (env "m" - 2) = some (j - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have em'' : intValue? (-2 + env "m") = some (j - 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hj0 : ¬ j < 0 := by omega
  have hj2 : ¬ j < 2 := by omega
  have hj2' : ¬ j - 2 < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r66Nondeg.body →
      env "d" + env "e" * w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi731r66Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R] at h
    tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r66Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [rubi731r66Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R] at hw
      simp [Defined, eval, Interp.real, hkp, em, ivm1R, hj2', hk0]
      tauto
    · filter_upwards [hF] with w hw
      simp [rubi731r66Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R] at hw
      simp [Defined, eval, Interp.real, hkp, em, ivm1R, iv2R, hj2', hk0]
      tauto
  · filter_upwards with w
    simp [rubi731r66Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, he]
  · simp only [rubi731r66Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hD0 := hD t hF.self_of_nhds
    set A := eval Interp.real (Function.update env "x" t)
      (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh
        (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))))) (.var "p")) with hA
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (j - 2) * A) t := by
      convert hΦ1 using 1
      simp [hA, eval, Interp.real, em, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (j - 2) * A *
        (env "d" + env "e" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [hA, eval, Interp.real, em, ivm1R, iv2R, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r66Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r66Nondeg.result) =
        fun w => env "f" ^ 2 * (env "e")⁻¹ * Φ "I1" w +
          -env "d" * env "f" ^ 2 * (env "e")⁻¹ * Φ "I2" w := by
      funext w; simp [rubi731r66Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r66Nondeg.body =
        (env "f" * t) ^ j * A * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi731r66Nondeg, hA, eval, Interp.real, hkm, ivm1R, iv2R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have hjj : (env "f" * t) ^ j = (env "f" * t) ^ (j - 2) * (env "f" * t) ^ 2 := by
      have := zpow_add_two_of (env "f" * t) (j - 2) (by omega)
      rwa [sub_add_cancel] at this
    rw [hjj]
    generalize (env "f" * t) ^ (j - 2) = P
    field_simp
    ring

theorem rubi734r46Nondeg_real : rubi734r46Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r46Nondeg.conditions rubi734r46Nondeg.body
    rubi734r46Nondeg.result rubi734r46Nondeg.integrals
  exact rubi731r66Nondeg_real

/-! ## The reciprocal-argument companion `rubi731r68Nondeg` -/

theorem rubi731r68Nondeg_real : rubi731r68Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r68Nondeg.conditions rubi731r68Nondeg.body
    rubi731r68Nondeg.result rubi731r68Nondeg.integrals
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi731r68Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hmlt : env "m" < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi731r68Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpgt : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r68Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r68Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r68Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hj : j < -1 := by
    have : (j : ℝ) < -1 := hm ▸ hmlt
    exact_mod_cast this
  have hk : 0 < k := by
    have : (0 : ℝ) < k := hp ▸ hpgt
    exact_mod_cast this
  have em : intValue? (env "m" + 2) = some (j + 2) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hjn : j < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r68Nondeg.body →
      env "f" * w ≠ 0 ∧ env "d" + env "e" * w ^ 2 ≠ 0 := by
    intro w h
    simp [rubi731r68Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R, hjn] at h
    refine ⟨mul_ne_zero ?_ ?_, ?_⟩ <;> tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r68Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [rubi731r68Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R] at hw
      simp [Defined, eval, Interp.real, hkm, hkp, ivm1R, hk0]
      tauto
    · filter_upwards [hF] with w hw
      simp [rubi731r68Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, iv2R] at hw
      simp [Defined, eval, Interp.real, hkp, em, ivm1R, iv2R, hk0]
      tauto
  · have hf0 : env "f" ≠ 0 := left_ne_zero_of_mul (hBody t hF.self_of_nhds).1
    filter_upwards with w
    simp [rubi731r68Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, iv2R, hd, hf0]
  · simp only [rubi731r68Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨hft, hD0⟩ := hBody t hF.self_of_nhds
    have hf0 : env "f" ≠ 0 := left_ne_zero_of_mul hft
    have ht0 : t ≠ 0 := right_ne_zero_of_mul hft
    set A := eval Interp.real (Function.update env "x" t)
      (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh
        (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))))) (.var "p")) with hA
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ j * A) t := by
      convert hΦ1 using 1
      simp [hA, eval, Interp.real, hkm, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (j + 2) * A *
        (env "d" + env "e" * t ^ 2)⁻¹) t := by
      convert hΦ2 using 1
      simp [hA, eval, Interp.real, em, ivm1R, iv2R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r68Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r68Nondeg.result) =
        fun w => (env "d")⁻¹ * Φ "I1" w +
          -env "e" * (env "d" * env "f" ^ 2)⁻¹ * Φ "I2" w := by
      funext w; simp [rubi731r68Nondeg, eval, recEnv, Interp.real, ivm1R, iv2R]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r68Nondeg.body =
        (env "f" * t) ^ j * A * (env "d" + env "e" * t ^ 2)⁻¹ := by
      simp [rubi731r68Nondeg, hA, eval, Interp.real, hkm, ivm1R, iv2R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    rw [zpow_add₀ hft]
    generalize (env "f" * t) ^ j = P
    field_simp
    ring

theorem rubi734r48Nondeg_real : rubi734r48Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r48Nondeg.conditions rubi734r48Nondeg.body
    rubi734r48Nondeg.result rubi734r48Nondeg.integrals
  exact rubi731r68Nondeg_real

end OSR.IntegrationRec217
