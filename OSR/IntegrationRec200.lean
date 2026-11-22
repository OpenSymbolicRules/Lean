import OSR.IntegrationNum1

/-!
# Integration (RUBI): algebra for the strengthened rule 1.1.3.2 #7

The product of the binomials has no linear term. Its derivative combines
with the power of `c * x` under the converted exponent condition.
-/

namespace OSR.IntegrationRec200

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-- The coefficient identity needed after differentiating the product. -/
theorem binomial_product_coefficient {K : Type} [CommRing K]
    (a1 a2 b1 b2 x m n p : K)
    (hcross : a2 * b1 + a1 * b2 = 0)
    (hexp : m + 1 + 2 * n * (p + 1) = 0) :
    (m + 1) * (a1 + b1 * x) * (a2 + b2 * x) +
      n * (p + 1) * x *
        (b1 * (a2 + b2 * x) + b2 * (a1 + b1 * x)) =
      (m + 1) * a1 * a2 := by
  linear_combination ((m + 1) * x + n * (p + 1) * x) * hcross +
    b1 * b2 * x ^ 2 * hexp

section
variable {K : Type} [NontriviallyNormedField K] [CharZero K]

omit [CharZero K] in
private theorem int_neg_one (I : Interp K) : I.toInt? (-1 : K) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

omit [CharZero K] in
private theorem zsucc (a : K) (k : ℤ) (h : a ≠ 0 ∨ 0 ≤ k) : a ^ (k + 1) = a ^ k * a := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, zpow_natCast, pow_succ]

/-- RUBI 1.1.3.2 #7 with its denominator required to be nonzero. -/
theorem rubi1132r7Nondeg_holds (I : Interp K) :
    AntiderivHoldsUnder I "x" rubi1132r7Nondeg.conditions rubi1132r7Nondeg.body
      rubi1132r7Nondeg.result := by
  intro env hc t hF
  have hd : env "a1" * env "a2" * env "c" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "a1") (.var "a2"))
      (.var "c")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1132r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hcross : env "a2" * env "b1" + env "a1" * env "b2" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1"))
      (.app2 .mul (.var "a1") (.var "b2"))) (.int 0)) (by simp [rubi1132r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.var "m") (.int 1))
    (.pow (.app2 .mul (.int 2) (.var "n")) (.int (-1)))) (.var "p")) (.int 1)) (.int 0))
    (by simp [rubi1132r7Nondeg])
  simp [Cond.Holds, Defined, eval, int_neg_one] at heq
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1132r7Nondeg, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1132r7Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1132r7Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : K) := (I.toInt?_eq _ _).1 hkm
  have hn : env "n" = (j : K) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : K) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hj0 : (j : K) ≠ 0 := by
    intro h
    apply heq.1
    rw [hn, h]
  have hqj : (k : K) + 1 + 2 * j * ((q : K) + 1) = 0 := by
    have h := heq.2
    rw [hm, hn, hp] at h
    field_simp at h
    linear_combination h
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1132r7Nondeg.body →
      (k < 0 → env "c" ≠ 0 ∧ w ≠ 0) ∧ (j < 0 → w ≠ 0) ∧
      (q < 0 → env "a1" + env "b1" * w ^ j ≠ 0) ∧
      (q < 0 → env "a2" + env "b2" * w ^ j ≠ 0) := by
    intro w h
    simp [rubi1132r7Nondeg, Defined, eval, hkm, hkn, hkp] at h
    tauto
  have hDG : ∀ w, Defined I (Function.update env "x" w) rubi1132r7Nondeg.body →
      Defined I (Function.update env "x" w) rubi1132r7Nondeg.result := by
    intro w h
    obtain ⟨hc, hx, hu, hv⟩ := hD w h
    simp [rubi1132r7Nondeg, Defined, eval, hkm1, hkn, hkp1, int_neg_one, hd]
    exact ⟨⟨fun h => hc (by omega), hx, fun h => hu (by omega)⟩,
      hx, fun h => hv (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w hw
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1132r7Nondeg.result =
      (env "c" * w) ^ (k + 1) * (env "a1" + env "b1" * w ^ j) ^ (q + 1) *
        (env "a2" + env "b2" * w ^ j) ^ (q + 1) *
        (env "a1" * env "a2" * env "c" * (env "m" + 1))⁻¹ := by
      intro w
      simp [rubi1132r7Nondeg, eval, hkm1, hkn, hkp1, int_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1132r7Nondeg.body =
      (env "c" * t) ^ k * (env "a1" + env "b1" * t ^ j) ^ q *
        (env "a2" + env "b2" * t ^ j) ^ q := by
      simp [rubi1132r7Nondeg, eval, hkm, hkn, hkp]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1132r7Nondeg.result) =
      fun w => (env "c" * w) ^ (k + 1) * (env "a1" + env "b1" * w ^ j) ^ (q + 1) *
        (env "a2" + env "b2" * w ^ j) ^ (q + 1) *
        (env "a1" * env "a2" * env "c" * (env "m" + 1))⁻¹ from funext hE]
    have hj : j ≠ 0 := fun h => hj0 (by rw [h]; simp)
    have hct : env "c" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (ht.1 h).1 (ht.1 h).2)
      · exact Or.inr (by omega)
    have hx : t ≠ 0 ∨ 0 ≤ j - 1 := by
      by_cases h : j < 0
      · exact Or.inl (ht.2.1 h)
      · exact Or.inr (by omega)
    have hu : env "a1" + env "b1" * t ^ j ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2.2.1 h)
      · exact Or.inr (by omega)
    have hv : env "a2" + env "b2" * t ^ j ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2.2.2 h)
      · exact Or.inr (by omega)
    have hct1 : env "c" * t ≠ 0 ∨ 0 ≤ k + 1 := hct.imp_right (by omega)
    have hx0 : t ≠ 0 ∨ 0 ≤ j := hx.imp_right (by omega)
    have hu1 : env "a1" + env "b1" * t ^ j ≠ 0 ∨ 0 ≤ q + 1 := hu.imp_right (by omega)
    have hv1 : env "a2" + env "b2" * t ^ j ≠ 0 ∨ 0 ≤ q + 1 := hv.imp_right (by omega)
    have htj : t ^ j = t ^ (j - 1) * t := by rw [← zsucc _ _ hx, sub_add_cancel]
    have hU := ((hasDerivAt_zpow j t hx0).const_mul (env "b1")).const_add (env "a1")
    have hV := ((hasDerivAt_zpow j t hx0).const_mul (env "b2")).const_add (env "a2")
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hct1)
      ((hasDerivAt_id' t).const_mul (env "c"))).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hu1) hU)).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hv1) hV)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [zsucc _ _ hct, zsucc _ _ hu, zsucc _ _ hv]
    generalize (env "c" * t) ^ k = C
    generalize (env "a1" + env "b1" * t ^ j) ^ q = U
    generalize (env "a2" + env "b2" * t ^ j) ^ q = V
    rw [htj]
    generalize t ^ (j - 1) = T
    rw [hm] at hd ⊢
    push_cast at hd ⊢
    rw [mul_inv_eq_iff_eq_mul₀ hd]
    linear_combination
      (C * U * V * env "c" * T * t * ((k : K) + 1 + (j : K) * ((q : K) + 1))) * hcross +
      (C * U * V * env "c" * env "b1" * env "b2" * T ^ 2 * t ^ 2) * hqj

theorem rubi1132r7Nondeg_real : rubi1132r7Nondeg.Holds .real :=
  rubi1132r7Nondeg_holds Interp.real

theorem rubi1132r7Nondeg_complex : rubi1132r7Nondeg.Holds .complex :=
  rubi1132r7Nondeg_holds Interp.complex

end

end OSR.IntegrationRec200
