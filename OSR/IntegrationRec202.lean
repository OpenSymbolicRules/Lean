import OSR.IntegrationNum1

/-!
# Integration (RUBI): strengthened rule 1.1.3.4 #15

The binomial product identity establishes the rule over both supported
domains, including the derivative and definedness obligations.
-/

namespace OSR.IntegrationRec202

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-- Polynomial identity obtained by differentiating the candidate result. -/
theorem rubi1134r15_coefficient {K : Type} [CommRing K]
    (a1 a2 b1 b2 c d m k p x : K)
    (hcross : a2 * b1 + a1 * b2 = 0)
    (hcoef : a1 * a2 * d * (m + 1) -
      b1 * b2 * c * (m + 2 * k * (p + 1) + 1) = 0) :
    c * ((m + 1) * (a1 + b1 * x) * (a2 + b2 * x) +
      (p + 1) * k * x * (b1 * (a2 + b2 * x) + b2 * (a1 + b1 * x))) =
      a1 * a2 * (m + 1) * (c + d * x ^ 2) := by
  linear_combination (c * x * (m + 1 + k * (p + 1))) * hcross - x ^ 2 * hcoef

section
variable {K : Type} [NontriviallyNormedField K] [CharZero K]

omit [CharZero K] in
private theorem int_neg_one (I : Interp K) : I.toInt? (-1 : K) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

omit [CharZero K] in
private theorem int_two (I : Interp K) : I.toInt? (2 : K) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

omit [CharZero K] in
private theorem zsucc (a : K) (k : ℤ) (h : a ≠ 0 ∨ 0 ≤ k) : a ^ (k + 1) = a ^ k * a := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, zpow_natCast, pow_succ]

omit [CharZero K] in
private theorem zdouble (a : K) (k : ℤ) (h : a ≠ 0 ∨ 0 ≤ k) :
    a ^ (2 * k) = a ^ k * a ^ k := by
  rw [show 2 * k = k + k by omega]
  rcases h with h | h
  · exact zpow_add₀ h _ _
  · lift k to ℕ using h
    norm_cast
    exact pow_add a k k

/-- RUBI 1.1.3.4 #15 with its denominator required to be nonzero. -/
theorem rubi1134r15Nondeg_holds (I : Interp K) :
    AntiderivHoldsUnder I "x" rubi1134r15Nondeg.conditions rubi1134r15Nondeg.body
      rubi1134r15Nondeg.result := by
  intro env hc t hF
  have hd : env "a1" * env "a2" * env "e" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "a1") (.var "a2"))
      (.var "e")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1134r15Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hcross : env "a2" * env "b1" + env "a1" * env "b2" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1"))
      (.app2 .mul (.var "a1") (.var "b2"))) (.int 0)) (by simp [rubi1134r15Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hcoef : env "a1" * env "a2" * env "d" * (env "m" + 1) +
      -1 * env "b1" * env "b2" * env "c" * (env "m" + env "n" * (env "p" + 1) + 1) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a1") (.var "a2"))
      (.var "d")) (.app2 .add (.var "m") (.int 1)))
      (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b1")) (.var "b2"))
        (.var "c")) (.app2 .add (.app2 .add (.var "m")
        (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)))) (.int 0))
      (by simp [rubi1134r15Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hhalf : env "non2" = env "n" * (2 : K)⁻¹ := by
    have h := hc (.eq (.var "non2") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1)))))
      (by simp [rubi1134r15Nondeg])
    have h' : (2 : K) ≠ 0 ∧ env "non2" = env "n" * (2 : K)⁻¹ := by
      simpa [Cond.Holds, Defined, eval, int_two, int_neg_one] using h
    exact h'.2
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r15Nondeg, Defined, eval, hkm] at h
  rcases hkr : I.toInt? (env "non2") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r15Nondeg, Defined, eval, hkr] at h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r15Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r15Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (m : K) := (I.toInt?_eq _ _).1 hkm
  have hr : env "non2" = (k : K) := (I.toInt?_eq _ _).1 hkr
  have hn : env "n" = (n : K) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (p : K) := (I.toInt?_eq _ _).1 hkp
  have hj : n = 2 * k := by
    have hcast : (n : K) = 2 * (k : K) := by
      rw [hr, hn] at hhalf
      calc
        (n : K) = 2 * ((n : K) * 2⁻¹) := by field_simp
        _ = 2 * (k : K) := by rw [← hhalf]
    exact_mod_cast hcast
  have hExp : I.toInt? (env "n" * (2 : K)⁻¹) = some k :=
    (I.toInt?_eq _ _).2 (by rw [hn, hj]; push_cast; field_simp)
  have hkm1 : I.toInt? (env "m" + 1) = some (m + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (p + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1134r15Nondeg.body →
      (m < 0 → env "e" ≠ 0 ∧ w ≠ 0) ∧ (k < 0 → w ≠ 0) ∧
      (p < 0 → env "a1" + env "b1" * w ^ k ≠ 0) ∧
      (p < 0 → env "a2" + env "b2" * w ^ k ≠ 0) := by
    intro w h
    simp [rubi1134r15Nondeg, Defined, eval, hkm, hkr, hkn, hkp] at h
    tauto
  have hDG : ∀ w, Defined I (Function.update env "x" w) rubi1134r15Nondeg.body →
      Defined I (Function.update env "x" w) rubi1134r15Nondeg.result := by
    intro w h
    obtain ⟨he, hx, hu, hv⟩ := hD w h
    have htwo : (2 : K) ≠ 0 := by norm_num
    simp [rubi1134r15Nondeg, Defined, eval, hkm1, hExp, hkp1, int_neg_one, hd, htwo]
    exact ⟨⟨fun h => he (by omega), hx, fun h => hu (by omega)⟩,
      hx, fun h => hv (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w hw
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1134r15Nondeg.result =
      env "c" * (env "e" * w) ^ (m + 1) * (env "a1" + env "b1" * w ^ k) ^ (p + 1) *
        (env "a2" + env "b2" * w ^ k) ^ (p + 1) *
        (env "a1" * env "a2" * env "e" * (env "m" + 1))⁻¹ := by
      intro w
      simp [rubi1134r15Nondeg, eval, hkm1, hExp, hkp1, int_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1134r15Nondeg.body =
      (env "e" * t) ^ m * (env "a1" + env "b1" * t ^ k) ^ p *
        (env "a2" + env "b2" * t ^ k) ^ p * (env "c" + env "d" * t ^ (2 * k)) := by
      simp [rubi1134r15Nondeg, eval, hkm, hkr, hkn, hkp, hj]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1134r15Nondeg.result) =
      fun w => env "c" * (env "e" * w) ^ (m + 1) * (env "a1" + env "b1" * w ^ k) ^ (p + 1) *
        (env "a2" + env "b2" * w ^ k) ^ (p + 1) *
        (env "a1" * env "a2" * env "e" * (env "m" + 1))⁻¹ from funext hE]
    have he : env "e" * t ≠ 0 ∨ 0 ≤ m := by
      by_cases h : m < 0
      · exact Or.inl (mul_ne_zero (ht.1 h).1 (ht.1 h).2)
      · exact Or.inr (by omega)
    have hx : t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht.2.1 h)
      · exact Or.inr (by omega)
    have hu : env "a1" + env "b1" * t ^ k ≠ 0 ∨ 0 ≤ p := by
      by_cases h : p < 0
      · exact Or.inl (ht.2.2.1 h)
      · exact Or.inr (by omega)
    have hv : env "a2" + env "b2" * t ^ k ≠ 0 ∨ 0 ≤ p := by
      by_cases h : p < 0
      · exact Or.inl (ht.2.2.2 h)
      · exact Or.inr (by omega)
    have he1 : env "e" * t ≠ 0 ∨ 0 ≤ m + 1 := he.imp_right (by omega)
    have hu1 : env "a1" + env "b1" * t ^ k ≠ 0 ∨ 0 ≤ p + 1 := hu.imp_right (by omega)
    have hv1 : env "a2" + env "b2" * t ^ k ≠ 0 ∨ 0 ≤ p + 1 := hv.imp_right (by omega)
    have hkey : (k : K) * t ^ (k - 1) * t = (k : K) * t ^ k := by
      rcases em (k = 0) with hk | hk
      · subst hk; simp
      · have h' : t ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hk' : k < 0
          · exact Or.inl (ht.2.1 hk')
          · exact Or.inr (by omega)
        rw [show t ^ k = t ^ (k - 1) * t by rw [← zsucc _ _ h', sub_add_cancel]]
        ring
    have hU := ((hasDerivAt_zpow k t hx).const_mul (env "b1")).const_add (env "a1")
    have hV := ((hasDerivAt_zpow k t hx).const_mul (env "b2")).const_add (env "a2")
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (m + 1) _ he1)
      ((hasDerivAt_id' t).const_mul (env "e"))).const_mul (env "c")).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (p + 1) _ hu1) hU)).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (p + 1) _ hv1) hV)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [zsucc _ _ he, zsucc _ _ hu, zsucc _ _ hv, zdouble _ _ hx]
    generalize (env "e" * t) ^ m = E
    generalize (env "a1" + env "b1" * t ^ k) ^ p = U
    generalize (env "a2" + env "b2" * t ^ k) ^ p = V
    generalize t ^ (k - 1) = R at hkey ⊢
    generalize t ^ k = T at hkey ⊢
    rw [hm, hn, hp, hj] at hcoef
    rw [hm] at hd ⊢
    push_cast at hcoef hd ⊢
    rw [mul_inv_eq_iff_eq_mul₀ hd]
    linear_combination
      (env "c" * (p + 1) * E * U * V * env "e" * env "b1" * (env "a2" + env "b2" * T)) * hkey +
      (env "c" * (p + 1) * E * U * V * env "e" * (env "a1" + env "b1" * T) * env "b2") * hkey +
      (env "c" * E * U * V * env "e" * T * ((m + 1) + (p + 1) * k)) * hcross -
      (E * U * V * env "e" * T * T) * hcoef

theorem rubi1134r15Nondeg_real : rubi1134r15Nondeg.Holds .real :=
  rubi1134r15Nondeg_holds Interp.real

theorem rubi1134r15Nondeg_complex : rubi1134r15Nondeg.Holds .complex :=
  rubi1134r15Nondeg_holds Interp.complex

end

end OSR.IntegrationRec202
