import OSR.IntegrationNum1

/-!
# Integration (RUBI): a proved strengthened numerical variant

The strengthened variant of RUBI 1.1.3.3 #11 is valid when `a1 * a2 ≠ 0`.
The two binomials have opposite linear coefficients, so their product is a
binomial in `x^n`; differentiating the supplied antiderivative proves the
rule over both supported domains.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec197

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

omit [CharZero 𝕜] in
private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

omit [CharZero 𝕜] in
private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

omit [CharZero 𝕜] in
private theorem zpow_succ_of (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

omit [CharZero 𝕜] in
private theorem zpow_double (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) :
    A ^ (2 * k) = A ^ k * A ^ k := by
  rw [show 2 * k = k + k by omega]
  rcases h with h | h
  · exact zpow_add₀ h _ _
  · lift k to ℕ using h
    norm_cast
    exact pow_add A k k

/-- **1.1.3.3 #11** with `a1 * a2 ≠ 0`. -/
theorem rubi1133r11Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1133r11Nondeg.conditions rubi1133r11Nondeg.body
      rubi1133r11Nondeg.result := by
  intro env hc t hF
  have hA : env "a1" * env "a2" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "a1") (.var "a2")) (.int 0)) (by simp [rubi1133r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hcross : env "a2" * env "b1" + env "a1" * env "b2" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1"))
      (.app2 .mul (.var "a1") (.var "b2"))) (.int 0)) (by simp [rubi1133r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hcoef : env "a1" * env "a2" * env "d" +
      -1 * env "b1" * env "b2" * env "c" * (env "n" * (env "p" + 1) + 1) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a1") (.var "a2")) (.var "d"))
      (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b1")) (.var "b2"))
        (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))
          (.int 1)))) (.int 0)) (by simp [rubi1133r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hhalf : env "non2" = env "n" * (2 : 𝕜)⁻¹ := by
    have h := hc (.eq (.var "non2") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1)))))
      (by simp [rubi1133r11Nondeg])
    have h' : (2 : 𝕜) ≠ 0 ∧ env "non2" = env "n" * (2 : 𝕜)⁻¹ := by
      simpa [Cond.Holds, Defined, eval, toInt?_two, toInt?_neg_one] using h
    exact h'.2
  rcases hkr : I.toInt? (env "non2") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r11Nondeg, Defined, eval, hkr] at h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r11Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r11Nondeg, Defined, eval, hkp] at h
  have hr : env "non2" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkr
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hj : j = 2 * k := by
    have hcast : (j : 𝕜) = 2 * (k : 𝕜) := by
      rw [hr, hn] at hhalf
      calc
        (j : 𝕜) = 2 * ((j : 𝕜) * 2⁻¹) := by field_simp
        _ = 2 * (k : 𝕜) := by rw [← hhalf]
    exact_mod_cast hcast
  have hExp : I.toInt? (env "n" * (2 : 𝕜)⁻¹) = some k :=
    (I.toInt?_eq _ _).2 (by rw [hn, hj]; push_cast; field_simp)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1133r11Nondeg.body →
      (k < 0 → w ≠ 0) ∧
      (q < 0 → env "a1" + env "b1" * w ^ k ≠ 0) ∧
      (q < 0 → env "a2" + env "b2" * w ^ k ≠ 0) := by
    intro w h
    simp [rubi1133r11Nondeg, Defined, eval, hkr, hkn, hkp] at h
    exact ⟨fun hk => h.1.1.1 hk, h.1.1.2, h.1.2.2⟩
  have hDG : ∀ w, (k < 0 → w ≠ 0) →
      (q < 0 → env "a1" + env "b1" * w ^ k ≠ 0) →
      (q < 0 → env "a2" + env "b2" * w ^ k ≠ 0) →
      Defined I (Function.update env "x" w) rubi1133r11Nondeg.result := by
    intro w hx hu hv
    have htwo : (2 : 𝕜) ≠ 0 := by norm_num
    simp [rubi1133r11Nondeg, Defined, eval, hExp, hkp1, toInt?_neg_one, hA, htwo]
    constructor
    · constructor
      · exact fun hk => hx hk
      · exact fun hq => hu (by omega)
    · constructor
      · exact fun hk => hx hk
      · exact fun hq => hv (by omega)
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2.1 (hD w hw).2.2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1133r11Nondeg.result =
        env "c" * w * (env "a1" + env "b1" * w ^ k) ^ (q + 1) *
          (env "a2" + env "b2" * w ^ k) ^ (q + 1) * (env "a1" * env "a2")⁻¹ := by
      intro w
      simp [rubi1133r11Nondeg, eval, hExp, hkp1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1133r11Nondeg.body =
        (env "a1" + env "b1" * t ^ k) ^ q * (env "a2" + env "b2" * t ^ k) ^ q *
          (env "c" + env "d" * t ^ (2 * k)) := by
      simp [rubi1133r11Nondeg, eval, hkr, hkn, hkp, hj]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1133r11Nondeg.result) =
        fun w => env "c" * w * (env "a1" + env "b1" * w ^ k) ^ (q + 1) *
          (env "a2" + env "b2" * w ^ k) ^ (q + 1) * (env "a1" * env "a2")⁻¹ from funext hE]
    have hx : t ≠ 0 ∨ 0 ≤ k := by
      by_cases hk : k < 0
      · exact Or.inl (ht.1 hk)
      · exact Or.inr (by omega)
    have hu : env "a1" + env "b1" * t ^ k ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases hq : q + 1 < 0
      · exact Or.inl (ht.2.1 (by omega))
      · exact Or.inr (by omega)
    have hv : env "a2" + env "b2" * t ^ k ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases hq : q + 1 < 0
      · exact Or.inl (ht.2.2 (by omega))
      · exact Or.inr (by omega)
    have hu0 : env "a1" + env "b1" * t ^ k ≠ 0 ∨ 0 ≤ q := by
      by_cases hq : q < 0
      · exact Or.inl (ht.2.1 hq)
      · exact Or.inr (by omega)
    have hv0 : env "a2" + env "b2" * t ^ k ≠ 0 ∨ 0 ≤ q := by
      by_cases hq : q < 0
      · exact Or.inl (ht.2.2 hq)
      · exact Or.inr (by omega)
    have hkey : (k : 𝕜) * t ^ (k - 1) * t = (k : 𝕜) * t ^ k := by
      rcases em (k = 0) with hk | hk
      · subst hk; simp
      · have h' : t ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases hk' : k < 0
          · exact Or.inl (ht.1 hk')
          · exact Or.inr (by omega)
        rw [show t ^ k = t ^ (k - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have hU : HasDerivAt (fun w => env "a1" + env "b1" * w ^ k)
        (env "b1" * ((k : 𝕜) * t ^ (k - 1))) t :=
      ((hasDerivAt_zpow k t hx).const_mul (env "b1")).const_add (env "a1")
    have hV : HasDerivAt (fun w => env "a2" + env "b2" * w ^ k)
        (env "b2" * ((k : 𝕜) * t ^ (k - 1))) t :=
      ((hasDerivAt_zpow k t hx).const_mul (env "b2")).const_add (env "a2")
    refine (((((hasDerivAt_id' t).const_mul (env "c")).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hu) hU)).mul
        (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hv) hV)).mul_const _).congr_deriv ?_
    simp [Function.comp_def]
    rw [zpow_succ_of _ _ hu0, zpow_succ_of _ _ hv0, zpow_double _ _ hx]
    generalize t ^ (k - 1) = R at hkey ⊢
    generalize t ^ k = T at hkey ⊢
    generalize (env "a1" + env "b1" * T) ^ q = P
    generalize (env "a2" + env "b2" * T) ^ q = Q
    rw [hn, hp, hj] at hcoef
    push_cast at hcoef ⊢
    have hAi : (env "a2")⁻¹ * (env "a1")⁻¹ = (env "a1" * env "a2")⁻¹ := by
      rw [mul_inv]
      ring
    rw [hAi]
    rw [mul_inv_eq_iff_eq_mul₀ hA]
    linear_combination
      (env "c" * (q + 1) * P * Q * env "b1" * (env "a2" + env "b2" * T)) * hkey +
      (env "c" * (q + 1) * P * Q * (env "a1" + env "b1" * T) * env "b2") * hkey +
      (env "c" * P * Q * T * (1 + (q + 1) * k)) * hcross -
      (P * Q * T * T) * hcoef

theorem rubi1133r11Nondeg_real : rubi1133r11Nondeg.Holds .real :=
  rubi1133r11Nondeg_holds Interp.real

theorem rubi1133r11Nondeg_complex : rubi1133r11Nondeg.Holds .complex :=
  rubi1133r11Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec197
