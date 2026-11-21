import OSR.IntegrationNum1

/-!
# Integration (RUBI): a proved strengthened numerical variant

The strengthened variant of RUBI 1.1.3.3 #8 is valid when `a * c ≠ 0`.
The two equality conditions cancel the `x^n` and `x^(2n)` coefficients
obtained by differentiating the supplied antiderivative.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec198

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

omit [CharZero 𝕜] in
private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
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

/-- **1.1.3.3 #8** with `a * c ≠ 0`. -/
theorem rubi1133r8Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1133r8Nondeg.conditions rubi1133r8Nondeg.body
      rubi1133r8Nondeg.result := by
  intro env hc t hF
  have hA : env "a" * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "a") (.var "c")) (.int 0))
      (by simp [rubi1133r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hsum : env "n" * (env "p" + env "q" + 2) + 1 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "n")
      (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 2))) (.int 1)) (.int 0))
      (by simp [rubi1133r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hcoef : env "a" * env "d" * (env "p" + 1) +
      env "b" * env "c" * (env "q" + 1) = 0 := by
    have h := hc (.eq (.app2 .add
      (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "p") (.int 1)))
      (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "q") (.int 1))))
      (.int 0)) (by simp [rubi1133r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r8Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r8Nondeg, Defined, eval, hkp] at h
  rcases hkq : I.toInt? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r8Nondeg, Defined, eval, hkq] at h
  have hn : env "n" = (n : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (p : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hq : env "q" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkq
  have hkp1 : I.toInt? (env "p" + 1) = some (p + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hkq1 : I.toInt? (env "q" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1133r8Nondeg.body →
      (n < 0 → w ≠ 0) ∧
      (p < 0 → env "a" + env "b" * w ^ n ≠ 0) ∧
      (q < 0 → env "c" + env "d" * w ^ n ≠ 0) := by
    intro w h
    simp [rubi1133r8Nondeg, Defined, eval, hkn, hkp, hkq] at h
    exact ⟨h.1.1, h.1.2, h.2.2⟩
  have hDG : ∀ w, (n < 0 → w ≠ 0) →
      (p < 0 → env "a" + env "b" * w ^ n ≠ 0) →
      (q < 0 → env "c" + env "d" * w ^ n ≠ 0) →
      Defined I (Function.update env "x" w) rubi1133r8Nondeg.result := by
    intro w hx hu hv
    simp [rubi1133r8Nondeg, Defined, eval, hkn, hkp, hkq, hkp1, hkq1, toInt?_neg_one, hA]
    exact ⟨⟨fun hn => hx hn, fun hp => hu (by omega)⟩,
      ⟨fun hn => hx hn, fun hq => hv (by omega)⟩⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2.1 (hD w hw).2.2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1133r8Nondeg.result =
        w * (env "a" + env "b" * w ^ n) ^ (p + 1) *
          (env "c" + env "d" * w ^ n) ^ (q + 1) * (env "a" * env "c")⁻¹ := by
      intro w
      simp [rubi1133r8Nondeg, eval, hkn, hkp, hkq, hkp1, hkq1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1133r8Nondeg.body =
        (env "a" + env "b" * t ^ n) ^ p * (env "c" + env "d" * t ^ n) ^ q := by
      simp [rubi1133r8Nondeg, eval, hkn, hkp, hkq]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1133r8Nondeg.result) =
        fun w => w * (env "a" + env "b" * w ^ n) ^ (p + 1) *
          (env "c" + env "d" * w ^ n) ^ (q + 1) * (env "a" * env "c")⁻¹ from funext hE]
    have hx : t ≠ 0 ∨ 0 ≤ n := by
      by_cases h : n < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hu : env "a" + env "b" * t ^ n ≠ 0 ∨ 0 ≤ p + 1 := by
      by_cases h : p + 1 < 0
      · exact Or.inl (ht.2.1 (by omega))
      · exact Or.inr (by omega)
    have hv : env "c" + env "d" * t ^ n ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2.2 (by omega))
      · exact Or.inr (by omega)
    have hu0 : env "a" + env "b" * t ^ n ≠ 0 ∨ 0 ≤ p := by
      by_cases h : p < 0
      · exact Or.inl (ht.2.1 h)
      · exact Or.inr (by omega)
    have hv0 : env "c" + env "d" * t ^ n ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2.2 h)
      · exact Or.inr (by omega)
    have hkey : (n : 𝕜) * t ^ (n - 1) * t = (n : 𝕜) * t ^ n := by
      rcases em (n = 0) with h | h
      · subst h; simp
      · have h' : t ≠ 0 ∨ 0 ≤ n - 1 := by
          by_cases h' : n < 0
          · exact Or.inl (ht.1 h')
          · exact Or.inr (by omega)
        rw [show t ^ n = t ^ (n - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have hU : HasDerivAt (fun w => env "a" + env "b" * w ^ n)
        (env "b" * ((n : 𝕜) * t ^ (n - 1))) t :=
      ((hasDerivAt_zpow n t hx).const_mul (env "b")).const_add (env "a")
    have hV : HasDerivAt (fun w => env "c" + env "d" * w ^ n)
        (env "d" * ((n : 𝕜) * t ^ (n - 1))) t :=
      ((hasDerivAt_zpow n t hx).const_mul (env "d")).const_add (env "c")
    refine (((((hasDerivAt_id' t).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (p + 1) _ hu) hU)).mul
        (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hv) hV)).mul_const _).congr_deriv ?_)
    simp [Function.comp_def]
    rw [zpow_succ_of _ _ hu0, zpow_succ_of _ _ hv0]
    generalize t ^ (n - 1) = R at hkey ⊢
    generalize t ^ n = T at hkey ⊢
    generalize (env "a" + env "b" * T) ^ p = P
    generalize (env "c" + env "d" * T) ^ q = Q
    rw [hn] at hsum
    rw [hp, hq] at hsum hcoef
    push_cast at hsum hcoef ⊢
    have hAi : (env "c")⁻¹ * (env "a")⁻¹ = (env "a" * env "c")⁻¹ := by
      rw [mul_inv]
      ring
    rw [hAi]
    rw [mul_inv_eq_iff_eq_mul₀ hA]
    linear_combination
      (P * Q * ((↑p + 1) * env "b" * (env "c" + env "d" * T) +
        (↑q + 1) * env "d" * (env "a" + env "b" * T))) * hkey +
      (P * Q * T * (env "a" * env "d" + env "b" * env "c" + env "b" * env "d" * T)) * hsum -
      (P * Q * (↑n) * T) * hcoef

theorem rubi1133r8Nondeg_real : rubi1133r8Nondeg.Holds .real :=
  rubi1133r8Nondeg_holds Interp.real

theorem rubi1133r8Nondeg_complex : rubi1133r8Nondeg.Holds .complex :=
  rubi1133r8Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec198
