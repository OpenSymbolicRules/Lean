import OSR.IntegrationNum1

/-!
# Integration (RUBI): strengthened recursive rule 1.1.3.4 #16

The nonzero denominator also makes the scale `e` nonzero. The result
combines a direct antiderivative with an arbitrary residual antiderivative.
-/

namespace OSR.IntegrationRec203

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

section
variable {K : Type} [NontriviallyNormedField K]

private theorem int_neg_one (I : Interp K) : I.toInt? (-1 : K) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem zsucc (a : K) (k : ℤ) (h : a ≠ 0 ∨ 0 ≤ k) : a ^ (k + 1) = a ^ k * a := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, zpow_natCast, pow_succ]

/-- RUBI 1.1.3.4 #16 with nonzero denominator. -/
theorem rubi1134r16Nondeg_holds (I : Interp K) :
    AntiderivRecHolds I "x" rubi1134r16Nondeg.conditions rubi1134r16Nondeg.body
      rubi1134r16Nondeg.result rubi1134r16Nondeg.integrals := by
  intro env hc t hF
  have hd : env "a" * env "e" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e"))
      (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1134r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    intro h
    apply hd
    rw [h]
    ring
  have hexp : env "m" + env "n" * (env "p" + 1) + 1 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m")
      (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)) (.int 0))
      (by simp [rubi1134r16Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r16Nondeg, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r16Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r16Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (m : K) := (I.toInt?_eq _ _).1 hkm
  have hn : env "n" = (n : K) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (p : K) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (m + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkmn : I.toInt? (env "m" + env "n") = some (m + n) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hn]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (p + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hen : env "e" ^ n ≠ 0 := zpow_ne_zero _ he
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1134r16Nondeg.body →
      (m < 0 → w ≠ 0) ∧ (n < 0 → w ≠ 0) ∧
      (p < 0 → env "a" + env "b" * w ^ n ≠ 0) := by
    intro w h
    simp [rubi1134r16Nondeg, Defined, eval, hkm, hkn, hkp] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1134r16Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hm0, hn0, hp0⟩ := hD w hw
    simp [Defined, eval, hkmn, hkn, hkp, he]
    exact ⟨fun h => by by_cases hn : n < 0 <;> first | exact hn0 hn | exact hm0 (by omega),
      hn0, hp0⟩
  · filter_upwards [hF] with w hw
    obtain ⟨hm0, hn0, hp0⟩ := hD w hw
    simp [rubi1134r16Nondeg, Defined, eval, recEnv, hkm1, hkn, hkp1, int_neg_one, hd, he, hen]
    exact ⟨fun h => hm0 (by omega), hn0, fun h => hp0 (by omega)⟩
  · simp only [rubi1134r16Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hE : ∀ w, eval I (recEnv env (rubi1134r16Nondeg.integrals.map (·.1)) Φ "x" w)
        rubi1134r16Nondeg.result =
      env "c" * (env "e" * w) ^ (m + 1) * (env "a" + env "b" * w ^ n) ^ (p + 1) *
        (env "a" * env "e" * (env "m" + 1))⁻¹ + env "d" * (env "e" ^ n)⁻¹ * Φ "I1" w := by
      intro w
      simp [rubi1134r16Nondeg, eval, recEnv, hkm1, hkn, hkp1, int_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1134r16Nondeg.body =
      (env "e" * t) ^ m * (env "a" + env "b" * t ^ n) ^ p *
        (env "c" + env "d" * t ^ n) := by
      simp [rubi1134r16Nondeg, eval, hkm, hkn, hkp]
    rw [hEF, show (fun w => eval I (recEnv env (rubi1134r16Nondeg.integrals.map (·.1)) Φ "x" w)
      rubi1134r16Nondeg.result) = fun w =>
      env "c" * (env "e" * w) ^ (m + 1) * (env "a" + env "b" * w ^ n) ^ (p + 1) *
        (env "a" * env "e" * (env "m" + 1))⁻¹ + env "d" * (env "e" ^ n)⁻¹ * Φ "I1" w from funext hE]
    have hI : HasDerivAt (Φ "I1")
      ((env "e" * t) ^ (m + n) * (env "a" + env "b" * t ^ n) ^ p) t := by
      simpa [rubi1134r16Nondeg, eval, hkmn, hkn, hkp] using hΦ
    have he0 : env "e" * t ≠ 0 ∨ 0 ≤ m := by
      by_cases h : m < 0
      · exact Or.inl (mul_ne_zero he (ht.1 h))
      · exact Or.inr (by omega)
    have hx : t ≠ 0 ∨ 0 ≤ n := by
      by_cases h : n < 0
      · exact Or.inl (ht.2.1 h)
      · exact Or.inr (by omega)
    have hu : env "a" + env "b" * t ^ n ≠ 0 ∨ 0 ≤ p := by
      by_cases h : p < 0
      · exact Or.inl (ht.2.2 h)
      · exact Or.inr (by omega)
    have he1 : env "e" * t ≠ 0 ∨ 0 ≤ m + 1 := he0.imp_right (by omega)
    have hu1 : env "a" + env "b" * t ^ n ≠ 0 ∨ 0 ≤ p + 1 := hu.imp_right (by omega)
    have hkey : (n : K) * t ^ (n - 1) * t = (n : K) * t ^ n := by
      rcases em (n = 0) with hn0 | hn0
      · subst hn0; simp
      · have h' : t ≠ 0 ∨ 0 ≤ n - 1 := by
          by_cases hn' : n < 0
          · exact Or.inl (ht.2.1 hn')
          · exact Or.inr (by omega)
        rw [show t ^ n = t ^ (n - 1) * t by rw [← zsucc _ _ h', sub_add_cancel]]
        ring
    have hscale : (env "e" * t) ^ (m + n) * (env "e" ^ n)⁻¹ =
        (env "e" * t) ^ m * t ^ n := by
      rw [mul_zpow, mul_zpow, zpow_add₀ he]
      by_cases ht0 : t = 0
      · have hm0 : 0 ≤ m := by by_contra h; exact ht.1 (by omega) ht0
        have hn0 : 0 ≤ n := by by_contra h; exact ht.2.1 (by omega) ht0
        lift m to ℕ using hm0
        lift n to ℕ using hn0
        rw [← Int.natCast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]
        field_simp
        simp only [zpow_natCast]
      · rw [zpow_add₀ ht0]
        field_simp
    have hI' : HasDerivAt (fun w => env "d" * (env "e" ^ n)⁻¹ * Φ "I1" w)
        (env "d" * ((env "e" * t) ^ m * t ^ n) * (env "a" + env "b" * t ^ n) ^ p) t := by
      convert hI.const_mul (env "d" * (env "e" ^ n)⁻¹) using 1
      rw [← hscale]
      ring
    have hU := ((hasDerivAt_zpow n t hx).const_mul (env "b")).const_add (env "a")
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ he1)
      ((hasDerivAt_id' t).const_mul (env "e"))).const_mul (env "c")).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (p + 1) _ hu1) hU)).mul_const _).add
      hI').congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zsucc _ _ he0, zsucc _ _ hu]
    generalize (env "e" * t) ^ m = E
    generalize (env "a" + env "b" * t ^ n) ^ p = U
    generalize t ^ (n - 1) = R at hkey ⊢
    generalize t ^ n = T at hkey ⊢
    rw [hm, hn, hp] at hexp
    rw [hm] at hd ⊢
    push_cast at hd hexp ⊢
    rw [← eq_sub_iff_add_eq]
    rw [mul_inv_eq_iff_eq_mul₀ hd]
    linear_combination
      (env "c" * E * U * env "e" * env "b" * (p + 1)) * hkey +
      (env "c" * E * U * env "e" * env "b" * T) * hexp

theorem rubi1134r16Nondeg_real : rubi1134r16Nondeg.Holds .real :=
  rubi1134r16Nondeg_holds Interp.real

theorem rubi1134r16Nondeg_complex : rubi1134r16Nondeg.Holds .complex :=
  rubi1134r16Nondeg_holds Interp.complex

end
end OSR.IntegrationRec203
