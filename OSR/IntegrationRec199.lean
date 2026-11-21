import OSR.IntegrationNum1

/-!
# Integration (RUBI): binomial product identity

An algebraic step towards the strengthened RUBI 1.1.3.2 #4 rule.
-/

namespace OSR.IntegrationRec199

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-- The cross term vanishes under the converted equality condition. -/
theorem binomial_product_derivative_factor {K : Type} [CommRing K]
    (a1 a2 b1 b2 t : K) (h : a2 * b1 + a1 * b2 = 0) :
    b1 * (a2 + b2 * t) + b2 * (a1 + b1 * t) = 2 * b1 * b2 * t := by
  linear_combination h

section
variable {K : Type} [NontriviallyNormedField K] [CharZero K]

omit [CharZero K] in
private theorem int_neg_one (I : Interp K) : I.toInt? (-1 : K) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

/-- RUBI 1.1.3.2 #4 with nonzero denominator. -/
theorem rubi1132r4Nondeg_holds (I : Interp K) :
    AntiderivHoldsUnder I "x" rubi1132r4Nondeg.conditions rubi1132r4Nondeg.body
      rubi1132r4Nondeg.result := by
  intro env hc t hF
  have hd : 2 * env "b1" * env "b2" * env "n" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2)
      (.var "b1")) (.var "b2")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0))
      (by simp [rubi1132r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hcross : env "a2" * env "b1" + env "a1" * env "b2" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1"))
      (.app2 .mul (.var "a1") (.var "b2"))) (.int 0)) (by simp [rubi1132r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hmn : env "m" = 2 * env "n" - 1 := by
    have h := hc (.eq (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n"))
      (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi1132r4Nondeg])
    simpa [Cond.Holds, Defined, eval, sub_eq_add_neg] using h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1132r4Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1132r4Nondeg, Defined, eval, hkp] at h
  have hn : env "n" = (n : K) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (p : K) := (I.toInt?_eq _ _).1 hkp
  have hkm : I.toInt? (env "m") = some (2 * n - 1) :=
    (I.toInt?_eq _ _).2 (by rw [hmn, hn]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (p + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1132r4Nondeg.body →
      (2 * n - 1 < 0 → w ≠ 0) ∧ (n < 0 → w ≠ 0) ∧
      (p < 0 → env "a1" + env "b1" * w ^ n ≠ 0) ∧
      (p < 0 → env "a2" + env "b2" * w ^ n ≠ 0) := by
    intro w h
    simp [rubi1132r4Nondeg, Defined, eval, hkm, hkn, hkp] at h
    exact ⟨fun hm => h.1.1 (by omega), h.1.2.1, h.1.2.2, h.2.2⟩
  have hDG : ∀ w, Defined I (Function.update env "x" w) rubi1132r4Nondeg.body →
      Defined I (Function.update env "x" w) rubi1132r4Nondeg.result := by
    intro w hw
    obtain ⟨hm, hx, hu, hv⟩ := hD w hw
    simp [rubi1132r4Nondeg, Defined, eval, hkn, hkp1, int_neg_one, hd]
    exact ⟨⟨hx, fun h => hu (by omega)⟩, ⟨hx, fun h => hv (by omega)⟩⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w hw
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1132r4Nondeg.result =
        (env "a1" + env "b1" * w ^ n) ^ (p + 1) *
        (env "a2" + env "b2" * w ^ n) ^ (p + 1) *
        (2 * env "b1" * env "b2" * env "n" * (env "p" + 1))⁻¹ := by
      intro w
      simp [rubi1132r4Nondeg, eval, hkn, hkp1, int_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1132r4Nondeg.body =
        t ^ (2 * n - 1) * (env "a1" + env "b1" * t ^ n) ^ p *
        (env "a2" + env "b2" * t ^ n) ^ p := by
      simp [rubi1132r4Nondeg, eval, hkm, hkn, hkp]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1132r4Nondeg.result) =
      fun w => (env "a1" + env "b1" * w ^ n) ^ (p + 1) *
        (env "a2" + env "b2" * w ^ n) ^ (p + 1) *
        (2 * env "b1" * env "b2" * env "n" * (env "p" + 1))⁻¹ from funext hE]
    have hx : t ≠ 0 ∨ 0 ≤ n := by
      by_cases h : n < 0
      · exact Or.inl (ht.2.1 h)
      · exact Or.inr (by omega)
    have hu : env "a1" + env "b1" * t ^ n ≠ 0 ∨ 0 ≤ p + 1 := by
      by_cases h : p < 0
      · exact Or.inl (ht.2.2.1 h)
      · exact Or.inr (by omega)
    have hv : env "a2" + env "b2" * t ^ n ≠ 0 ∨ 0 ≤ p + 1 := by
      by_cases h : p < 0
      · exact Or.inl (ht.2.2.2 h)
      · exact Or.inr (by omega)
    have hu0 : env "a1" + env "b1" * t ^ n ≠ 0 ∨ 0 ≤ p := by
      by_cases h : p < 0
      · exact Or.inl (ht.2.2.1 h)
      · exact Or.inr (by omega)
    have hv0 : env "a2" + env "b2" * t ^ n ≠ 0 ∨ 0 ≤ p := by
      by_cases h : p < 0
      · exact Or.inl (ht.2.2.2 h)
      · exact Or.inr (by omega)
    have hU := ((hasDerivAt_zpow n t hx).const_mul (env "b1")).const_add (env "a1")
    have hV := ((hasDerivAt_zpow n t hx).const_mul (env "b2")).const_add (env "a2")
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (p + 1) _ hu) hU).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (p + 1) _ hv) hV)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def]
    have zsucc (A : K) (j : ℤ) (h : A ≠ 0 ∨ 0 ≤ j) : A ^ (j + 1) = A ^ j * A := by
      rcases h with h | h
      · exact zpow_add_one₀ h j
      · lift j to ℕ using h
        rw [show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast, zpow_natCast, pow_succ]
    rw [zsucc _ _ hu0, zsucc _ _ hv0]
    have hpow : t ^ (n - 1) * t ^ n = t ^ (2 * n - 1) := by
      by_cases hz : t = 0
      · have hnpos : 0 < n := by
          by_contra h
          exact ht.1 (by omega) hz
        rw [hz, zero_zpow n (by omega), mul_zero, zero_zpow (2 * n - 1) (by omega)]
      · rw [← zpow_add₀ hz]
        congr 1
        omega
    rw [hn, hp] at hd ⊢
    push_cast at hd ⊢
    simp only [add_sub_cancel_right]
    rw [mul_inv_eq_iff_eq_mul₀ hd]
    linear_combination
      ((p : K) + 1) * (n : K) * (env "a1" + env "b1" * t ^ n) ^ p *
        (env "a2" + env "b2" * t ^ n) ^ p * t ^ (n - 1) * hcross +
      (2 * env "b1" * env "b2" * (n : K) * ((p : K) + 1) *
        (env "a1" + env "b1" * t ^ n) ^ p * (env "a2" + env "b2" * t ^ n) ^ p) * hpow

theorem rubi1132r4Nondeg_real : rubi1132r4Nondeg.Holds .real :=
  rubi1132r4Nondeg_holds Interp.real

theorem rubi1132r4Nondeg_complex : rubi1132r4Nondeg.Holds .complex :=
  rubi1132r4Nondeg_holds Interp.complex

end

end OSR.IntegrationRec199
