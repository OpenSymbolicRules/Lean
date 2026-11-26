import OSR.IntegrationRec215

/-! # Strengthened inverse hyperbolic tangent rule: substitution `u = artanh(c x)`

Proof over ℝ of RUBI 7.3.1 #39 (and its 7.3.4 #19 twin), which substitutes `u = artanh(c x)` in
`∫ (a + b artanh(c x))^p / sqrt(d + e x^2) dx` when `c^2 d + e = 0` and `d > 0`, giving
`1/(c sqrt d) ∫ (a + b u)^p sech u du`: here `sech(artanh(c x)) = sqrt(1 - c^2 x^2)` and
`sqrt(d + e x^2) = sqrt d sqrt(1 - c^2 x^2)`. The complex statement is vacuous (`arith1#root`
and `transc1#arctanh` have no complex interpretation) and stays unproved. -/

namespace OSR.IntegrationRec233

open OSR OSR.Calculus OSR.IntegrationNum1 OSR.IntegrationRec215 Filter Topology

private theorem ivm1R : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
private theorem iv2R : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)

/-! ## RUBI 7.3.1 #39 (and 7.3.4 #19) -/

theorem rubi731r39Nondeg_real : rubi731r39Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi731r39Nondeg.conditions
    rubi731r39Nondeg.body rubi731r39Nondeg.result rubi731r39Nondeg.integrals
    rubi731r39Nondeg.substs
  intro env hc t hF
  have hrel : env "c" ^ 2 * env "d" + env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e"))
      (.int 0)) (by simp [rubi731r39Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R] using h
  have hdpos : 0 < env "d" := by
    have h := hc (.gt (.var "d") (.int 0)) (by simp [rubi731r39Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hpos : 0 < env "p" := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r39Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  have hW : env "c" * Real.sqrt (env "d") ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "c") (.app2 .root (.var "d") (.int 2))) (.int 0))
      (by simp [rubi731r39Nondeg])
    simpa [Cond.Holds, Defined, eval, Interp.real, iv2R, hdpos.le] using h
  have he' : env "e" = -(env "c" ^ 2 * env "d") := by linear_combination hrel
  rcases hkp : intValue? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi731r39Nondeg, Defined, eval, Interp.real, hkp] at h
  have hp : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hkp
  have hk : 0 < k := by rw [hp] at hpos; exact_mod_cast hpos
  have hk0 : ¬ k < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r39Nondeg.body →
      -1 < env "c" * w ∧ env "c" * w < 1 := by
    intro w h
    simp [rubi731r39Nondeg, Defined, eval, Interp.real, hkp, hk0, ivm1R, iv2R] at h
    tauto
  obtain ⟨h1, h2⟩ := hD t hF.self_of_nhds
  have hsub : substAt Interp.real env rubi731r39Nondeg.substs "x" "I1" t =
      Real.artanh (env "c" * t) := by
    simp [rubi731r39Nondeg, substAt, eval, Interp.real]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [rubi731r39Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    constructor
    · filter_upwards [hF] with w hw
      intro g hg
      simp only [rubi731r39Nondeg, List.lookup_cons, beq_self_eq_true,
        Option.some.injEq] at hg
      subst g
      have hw' := hD w hw
      simp [Defined, eval, Interp.real, hw'.1, hw'.2]
    · filter_upwards with u
      simp [Defined, eval, Interp.real, hkp, hk0]
  · intro Φ hΦ
    refine ⟨?_, ?_⟩
    · filter_upwards with w
      simp [rubi731r39Nondeg, Defined, eval, Interp.real, substEnv, ivm1R, iv2R, hdpos.le, hW]
    · simp only [rubi731r39Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
      have hΦ' : HasDerivAt (Φ "I1")
          ((env "a" + env "b" * Real.artanh (env "c" * t)) ^ k *
            Fn.sech (Real.artanh (env "c" * t))) (Real.artanh (env "c" * t)) := by
        convert hΦ using 1 <;> simp [substAt, eval, Interp.real, hkp]
      have h := (hΦ'.comp t (hasDerivAt_artanh_mul h1 h2)).const_mul
        (env "c" * Real.sqrt (env "d"))⁻¹
      have hfun : (fun w => eval Interp.real
          (substEnv Interp.real env (rubi731r39Nondeg.integrals.map (·.1))
            rubi731r39Nondeg.substs Φ "x" w) rubi731r39Nondeg.result) =
          fun w => (env "c" * Real.sqrt (env "d"))⁻¹ * Φ "I1" (Real.artanh (env "c" * w)) := by
        funext w
        simp [rubi731r39Nondeg, substEnv, substAt, eval, Interp.real, ivm1R]
      rw [hfun]
      apply h.congr_deriv
      have hEF : eval Interp.real (Function.update env "x" t) rubi731r39Nondeg.body =
          (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k *
            (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
        simp [rubi731r39Nondeg, eval, Interp.real, hkp, ivm1R, iv2R]
      rw [hEF]
      have hmem : env "c" * t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨h1, h2⟩
      have hY : 0 < 1 - (env "c" * t) ^ 2 := by
        have : (env "c" * t) ^ 2 < 1 := by
          rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
        linarith
      have hsech : Fn.sech (Real.artanh (env "c" * t)) = Real.sqrt (1 - (env "c" * t) ^ 2) := by
        rw [Fn.sech, Real.cosh_artanh hmem]
        field_simp
      have hsq : Real.sqrt (env "d" + env "e" * t ^ 2) =
          Real.sqrt (env "d") * Real.sqrt (1 - (env "c" * t) ^ 2) := by
        rw [← Real.sqrt_mul hdpos.le, he']
        congr 1
        ring
      rw [hsech, hsq]
      have hs0 : Real.sqrt (1 - (env "c" * t) ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hY).ne'
      have hs2 : Real.sqrt (1 - (env "c" * t) ^ 2) ^ 2 = 1 - (env "c" * t) ^ 2 :=
        Real.sq_sqrt hY.le
      have hcz : env "c" ≠ 0 := left_ne_zero_of_mul hW
      have hsd : Real.sqrt (env "d") ≠ 0 := right_ne_zero_of_mul hW
      have hD' : 1 - env "c" ^ 2 * t ^ 2 ≠ 0 := by rw [← mul_pow]; exact hY.ne'
      generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k = R
      generalize Real.sqrt (1 - (env "c" * t) ^ 2) = s at hs0 hs2 ⊢
      rw [mul_pow] at hs2
      field_simp
      rw [hs2]

theorem rubi734r19Nondeg_real : rubi734r19Nondeg.Holds .real := by
  show AntiderivSubstHolds Interp.real "x" rubi734r19Nondeg.conditions
    rubi734r19Nondeg.body rubi734r19Nondeg.result rubi734r19Nondeg.integrals
    rubi734r19Nondeg.substs
  exact rubi731r39Nondeg_real

end OSR.IntegrationRec233
