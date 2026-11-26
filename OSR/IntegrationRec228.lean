import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rule: splitting a linear denominator

Proof over ℝ of RUBI 7.3.1 #21 (and its 7.3.4 #1 twin), which splits
`(f x)^m (a + b artanh(c x))^p / (d + e x)` into
`f/e ∫ (f x)^(m-1) (a + b artanh(c x))^p - d f/e ∫ (f x)^(m-1) (a + b artanh(c x))^p / (d + e x)`.
The step is the algebraic identity `(f x)^m = (f x)^(m-1) (f x)`, valid since the integer `m` is
positive. The condition `c^2 d^2 = e^2` is not needed. The complex statement is vacuous (no complex
interpretation of `transc1#arctanh`) and stays unproved. -/

namespace OSR.IntegrationRec228

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem zpow_add_nat_of (A : ℝ) (j : ℤ) (n : ℕ) (h : 0 ≤ j) :
    A ^ (j + n) = A ^ j * A ^ n := by
  lift j to ℕ using h
  rw [show ((j : ℤ) + n) = ((j + n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
    pow_add]

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 7.3.1 #21 (and 7.3.4 #1) -/

theorem rubi731r21Nondeg_real : rubi731r21Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r21Nondeg.conditions rubi731r21Nondeg.body
    rubi731r21Nondeg.result rubi731r21Nondeg.integrals
  intro env hc t hF
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi731r21Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r21Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hmpos : 0 < env "m" := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi731r21Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hkm : intValue? (env "m") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r21Nondeg, Defined, eval, Interp.real, hkm] at h
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r21Nondeg, Defined, eval, Interp.real, hkm, hkp] at h
  have hm : env "m" = (j : ℝ) := (intValue?_eq _ _).1 hkm
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hj : 0 < j := by rw [hm] at hmpos; exact_mod_cast hmpos
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hj0 : ¬ j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have hj1' : ¬ j < 1 := by omega
  have hk0 : ¬ k < 0 := by omega
  have em1 : intValue? (env "m" + -1) = some (j - 1) :=
    (intValue?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r21Nondeg.body →
      env "d" + env "e" * w ≠ 0 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r21Nondeg, Defined, eval, Interp.real, hkm, hkp, ivm1R, hj0, hk0] at h
    tauto
  obtain ⟨hL0, hc1, hc2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r21Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have hB := hBody w hw
      simp [Defined, eval, Interp.real, em1, hkp, hj1, hk0, hB.2.1, hB.2.2]
    · filter_upwards [hF] with w hw
      have hB := hBody w hw
      simp [Defined, eval, Interp.real, em1, hkp, ivm1R, hj1, hk0, hB.1, hB.2.1, hB.2.2]
  · filter_upwards [hF] with w hw
    simp [rubi731r21Nondeg, Defined, eval, recEnv, Interp.real, ivm1R, he]
  · simp only [rubi731r21Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (j - 1) *
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k) t := by
      convert hΦ1 using 1
      simp [eval, Interp.real, em1, hkp, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (j - 1) *
        (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k * (env "d" + env "e" * t)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, Interp.real, em1, hkp, ivm1R, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r21Nondeg.integrals.map (·.1)) Φ
        "x" w) rubi731r21Nondeg.result) =
        fun w => env "f" * (env "e")⁻¹ * Φ "I1" w +
          -env "d" * env "f" * (env "e")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi731r21Nondeg, eval, recEnv, Interp.real, ivm1R,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r21Nondeg.body =
        (env "f" * t) ^ j * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k *
          (env "d" + env "e" * t)⁻¹ := by
      simp [rubi731r21Nondeg, eval, Interp.real, hkm, hkp, ivm1R]
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    have h1 : (env "f" * t) ^ j = (env "f" * t) ^ (j - 1) * (env "f" * t) := by
      have := zpow_add_nat_of (env "f" * t) (j - 1) 1 (by omega)
      rwa [show j - 1 + ((1 : ℕ) : ℤ) = j by push_cast; ring, pow_one] at this
    rw [h1]
    generalize (env "f" * t) ^ (j - 1) = P
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k = R
    field_simp
    ring

theorem rubi734r1Nondeg_real : rubi734r1Nondeg.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r1Nondeg.conditions rubi734r1Nondeg.body
    rubi734r1Nondeg.result rubi734r1Nondeg.integrals
  exact rubi731r21Nondeg_real

end OSR.IntegrationRec228
