import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, fourth batch

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.2.3.3 #12, where
`c d² + a e² = 0` factors `a + c x²ⁿ` as `(d + e xⁿ) (a/d + c xⁿ/e)`, and
1.2.3.3 #19 and #20, whose reduction divides by `e (n (q + 2) + 1)`.  Proved
over ℝ and ℂ for every choice of antiderivatives of the residual integrand.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec52

open OSR OSR.Calculus OSR.IntegrationNum1 Filter Topology

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem zpow_succ_of (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_four (I : Interp 𝕜) : I.toInt? (4 : 𝕜) = some 4 :=
  (I.toInt?_eq _ _).2 (by simp)








/-- **1.2.3.3 #12** with `d ≠ 0` and `e ≠ 0`: `a + c x²ⁿ = (d + e xⁿ) (a/d + c xⁿ/e)`. -/
theorem rubi1233r12Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1233r12Nondeg.conditions rubi1233r12Nondeg.body rubi1233r12Nondeg.result rubi1233r12Nondeg.integrals := by
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1233r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1233r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1233r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1233r12Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hdi : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd
  have hei : env "e" * (env "e")⁻¹ = 1 := mul_inv_cancel₀ he
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r12Nondeg, Defined, eval, hkn] at h
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hkn2 : I.toInt? (env "n2") = some (2 * j) :=
    (I.toInt?_eq _ _).2 (by rw [hn2, hn]; push_cast; ring)
  have hQ : ∀ w : 𝕜, (env "a" + env "c" * w ^ (2 * j)) = (env "d" + env "e" * w ^ j) * (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ j) := fun w => by
    rw [show w ^ (2 * j) = (w ^ j) ^ 2 by rw [mul_comm, zpow_mul]; norm_cast]
    linear_combination (-(w ^ j) * (env "d")⁻¹ * (env "e")⁻¹) * h1 +
      (env "c" * env "d" * (env "e")⁻¹ * w ^ j) * hdi +
      (env "a" * env "e" * (env "d")⁻¹ * w ^ j) * hei - env "a" * hdi - env "c" * (w ^ j) ^ 2 * hei
  rcases hkm : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r12Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r12Nondeg, Defined, eval, hkp] at h
  have hm : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "p" + env "q") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1233r12Nondeg.body →
      (j < 0 → w ≠ 0) ∧ (k < 0 → (env "d" + env "e" * w ^ j) ≠ 0) ∧ (q < 0 → (env "a" + env "c" * w ^ (2 * j)) ≠ 0) := by
    intro w h
    simp [rubi1233r12Nondeg, Defined, eval, hkn, hkn2, hkm, hkp] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1233r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h0', h1', h2'⟩ := hD w hw
    simp [Defined, eval, hkn, hkmp, hkp, toInt?_neg_one, hd, he]
    refine ⟨⟨h0', fun hkq => ?_⟩, h0', fun hq h0 => h2' hq (by rw [hQ w, h0, mul_zero])⟩
    by_cases hq : q < 0
    · intro h0
      exact h2' hq (by rw [hQ w, h0, zero_mul])
    · exact h1' (by omega)
  · exact Eventually.of_forall fun w => by simp [rubi1233r12Nondeg, Defined, eval, recEnv]
  · simp only [rubi1233r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1233r12Nondeg.integrals.map (·.1)) Φ "x" w) rubi1233r12Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1233r12Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi1233r12Nondeg, eval, hkn, hkn2, hkm, hkp, hkmp, toInt?_neg_one]
    have hz : (env "d" + env "e" * t ^ j) ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases hD0 : (env "d" + env "e" * t ^ j) = 0
      · have hk : 0 ≤ k := by
          by_contra hk
          exact ht.2.1 (by omega) hD0
        have hq : 0 ≤ q := by
          by_contra hq
          exact ht.2.2 (by omega) (by rw [hQ t, hD0, zero_mul])
        by_cases hkq : k + q = 0
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inl hkq)
      · exact Or.inl hD0
    rw [hQ t, mul_zpow (env "d" + env "e" * t ^ j) _ q, zpow_add' hz]
    ring

theorem rubi1233r12Nondeg_real : rubi1233r12Nondeg.Holds .real :=
  rubi1233r12Nondeg_holds Interp.real

theorem rubi1233r12Nondeg_complex : rubi1233r12Nondeg.Holds .complex :=
  rubi1233r12Nondeg_holds Interp.complex

/-- **1.2.3.3 #20** with `e (n (q + 2) + 1) ≠ 0`. -/
theorem rubi1233r20Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1233r20Nondeg.conditions rubi1233r20Nondeg.body rubi1233r20Nondeg.result rubi1233r20Nondeg.integrals := by
  intro env hc t hF
  have hW : env "e" * (env "n" * (env "q" + 2) + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.int 0)) (by simp [rubi1233r20Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1233r20Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r20Nondeg, Defined, eval, hkn] at h
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hkn2 : I.toInt? (env "n2") = some (2 * j) :=
    (I.toInt?_eq _ _).2 (by rw [hn2, hn]; push_cast; ring)
  rcases hkm : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r20Nondeg, Defined, eval, hkm, hkn] at h
  have hm : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hkn1 : I.toInt? (env "n" + 1) = some (j + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hkm1 : I.toInt? (env "q" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1233r20Nondeg.body →
      (j < 0 → w ≠ 0) ∧ (k < 0 → (env "d" + env "e" * w ^ j) ≠ 0) := by
    intro w h
    simp [rubi1233r20Nondeg, Defined, eval, hkn, hkn2, hkm] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1233r20Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1', h2'⟩ := hD w hw
    simp [Defined, eval, hkn, hkm]
    exact ⟨⟨h1', h2'⟩, h1'⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1', h2'⟩ := hD w hw
    simp [rubi1233r20Nondeg, Defined, eval, recEnv, hkn1, hkn, hkm1, toInt?_neg_one]
    exact ⟨⟨fun h => h1' (by omega), h1', fun h => h2' (by omega)⟩,
      left_ne_zero_of_mul hW, right_ne_zero_of_mul hW⟩
  · simp only [rubi1233r20Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    set u := (env "e" * (env "n" * (env "q" + 2) + 1))⁻¹ with hu_def
    have hU : env "e" * (env "n" * (env "q" + 2) + 1) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ j) ^ k *
        (env "a" * env "e" * (env "n" * (env "q" + 2) + 1) + -1 * env "c" * env "d" * (env "n" + 1) * t ^ j)) t := by
      convert hΦ using 1
      simp [eval, hkn, hkm]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1233r20Nondeg.body =
        (env "d" + env "e" * t ^ j) ^ k * (env "a" + env "c" * t ^ (2 * j)) := by
      simp [rubi1233r20Nondeg, eval, hkn, hkn2, hkm]
    have hfun : (fun w => eval I (recEnv env (rubi1233r20Nondeg.integrals.map (·.1)) Φ "x" w) rubi1233r20Nondeg.result) =
        fun w => env "c" * w ^ (j + 1) * (env "d" + env "e" * w ^ j) ^ (k + 1) * u + u * Φ "I1" w := by
      funext w
      simp [rubi1233r20Nondeg, eval, recEnv, hkn1, hkn, hkm1, toInt?_neg_one, hu_def]
      try ring
    rw [hfun, hEF]
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hx1 : t ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hv : (env "d" + env "e" * t ^ j) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have hv0 : (env "d" + env "e" * t ^ j) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have key : (j : 𝕜) * t ^ (j - 1) * t = (j : 𝕜) * t ^ j := by
      rcases em (j = 0) with h0 | h0
      · subst h0; simp
      · have h' : t ≠ 0 ∨ 0 ≤ j - 1 := by
          by_cases h : j < 0
          · exact Or.inl (ht.1 h)
          · exact Or.inr (by omega)
        rw [show t ^ j = t ^ (j - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have hin : HasDerivAt (fun w => env "d" + env "e" * w ^ j) (env "e" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "e")).const_add (env "d")
    refine (((((hasDerivAt_zpow (j + 1) t hx1).const_mul (env "c")).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (k + 1) _ hv) hin)).mul_const u).add (hΦ'.const_mul u)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hx, zpow_succ_of _ _ hv0,
      show t ^ (2 * j) = (t ^ j) ^ 2 by rw [mul_comm, zpow_mul]; norm_cast]
    generalize (env "d" + env "e" * t ^ j) ^ k = Y
    generalize t ^ (j - 1) = R at key ⊢
    generalize t ^ j = T at key ⊢
    clear_value u
    simp only [hn, hm] at hU ⊢
    push_cast
    linear_combination (Y * (env "a" + env "c" * T ^ 2)) * hU +
      (env "c" * u * T * ((k : 𝕜) + 1) * Y * env "e") * key

theorem rubi1233r20Nondeg_real : rubi1233r20Nondeg.Holds .real :=
  rubi1233r20Nondeg_holds Interp.real

theorem rubi1233r20Nondeg_complex : rubi1233r20Nondeg.Holds .complex :=
  rubi1233r20Nondeg_holds Interp.complex

/-- **1.2.3.3 #19** with `e (n (q + 2) + 1) ≠ 0`. -/
theorem rubi1233r19Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1233r19Nondeg.conditions rubi1233r19Nondeg.body rubi1233r19Nondeg.result rubi1233r19Nondeg.integrals := by
  intro env hc t hF
  have hW : env "e" * (env "n" * (env "q" + 2) + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.int 0)) (by simp [rubi1233r19Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1233r19Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r19Nondeg, Defined, eval, hkn] at h
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hkn2 : I.toInt? (env "n2") = some (2 * j) :=
    (I.toInt?_eq _ _).2 (by rw [hn2, hn]; push_cast; ring)
  rcases hkm : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1233r19Nondeg, Defined, eval, hkm, hkn] at h
  have hm : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hkn1 : I.toInt? (env "n" + 1) = some (j + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hkm1 : I.toInt? (env "q" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1233r19Nondeg.body →
      (j < 0 → w ≠ 0) ∧ (k < 0 → (env "d" + env "e" * w ^ j) ≠ 0) := by
    intro w h
    simp [rubi1233r19Nondeg, Defined, eval, hkn, hkn2, hkm] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1233r19Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1', h2'⟩ := hD w hw
    simp [Defined, eval, hkn, hkm]
    tauto
  · filter_upwards [hF] with w hw
    obtain ⟨h1', h2'⟩ := hD w hw
    simp [rubi1233r19Nondeg, Defined, eval, recEnv, hkn1, hkn, hkm1, toInt?_neg_one]
    exact ⟨⟨fun h => h1' (by omega), h1', fun h => h2' (by omega)⟩,
      left_ne_zero_of_mul hW, right_ne_zero_of_mul hW⟩
  · simp only [rubi1233r19Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    set u := (env "e" * (env "n" * (env "q" + 2) + 1))⁻¹ with hu_def
    have hU : env "e" * (env "n" * (env "q" + 2) + 1) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t ^ j) ^ k *
        (env "a" * env "e" * (env "n" * (env "q" + 2) + 1) + -1 * (env "c" * env "d" * (env "n" + 1) + -1 * env "b" * env "e" * (env "n" * (env "q" + 2) + 1)) * t ^ j)) t := by
      convert hΦ using 1
      simp [eval, hkn, hkm]
      try ring
    have hEF : eval I (Function.update env "x" t) rubi1233r19Nondeg.body =
        (env "d" + env "e" * t ^ j) ^ k * (env "a" + env "b" * t ^ j + env "c" * t ^ (2 * j)) := by
      simp [rubi1233r19Nondeg, eval, hkn, hkn2, hkm]
    have hfun : (fun w => eval I (recEnv env (rubi1233r19Nondeg.integrals.map (·.1)) Φ "x" w) rubi1233r19Nondeg.result) =
        fun w => env "c" * w ^ (j + 1) * (env "d" + env "e" * w ^ j) ^ (k + 1) * u + u * Φ "I1" w := by
      funext w
      simp [rubi1233r19Nondeg, eval, recEnv, hkn1, hkn, hkm1, toInt?_neg_one, hu_def]
      try ring
    rw [hfun, hEF]
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hx1 : t ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hv : (env "d" + env "e" * t ^ j) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have hv0 : (env "d" + env "e" * t ^ j) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have key : (j : 𝕜) * t ^ (j - 1) * t = (j : 𝕜) * t ^ j := by
      rcases em (j = 0) with h0 | h0
      · subst h0; simp
      · have h' : t ≠ 0 ∨ 0 ≤ j - 1 := by
          by_cases h : j < 0
          · exact Or.inl (ht.1 h)
          · exact Or.inr (by omega)
        rw [show t ^ j = t ^ (j - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have hin : HasDerivAt (fun w => env "d" + env "e" * w ^ j) (env "e" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "e")).const_add (env "d")
    refine (((((hasDerivAt_zpow (j + 1) t hx1).const_mul (env "c")).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (k + 1) _ hv) hin)).mul_const u).add (hΦ'.const_mul u)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hx, zpow_succ_of _ _ hv0,
      show t ^ (2 * j) = (t ^ j) ^ 2 by rw [mul_comm, zpow_mul]; norm_cast]
    generalize (env "d" + env "e" * t ^ j) ^ k = Y
    generalize t ^ (j - 1) = R at key ⊢
    generalize t ^ j = T at key ⊢
    clear_value u
    simp only [hn, hm] at hU ⊢
    push_cast
    linear_combination (Y * (env "a" + env "b" * T + env "c" * T ^ 2)) * hU +
      (env "c" * u * T * ((k : 𝕜) + 1) * Y * env "e") * key

theorem rubi1233r19Nondeg_real : rubi1233r19Nondeg.Holds .real :=
  rubi1233r19Nondeg_holds Interp.real

theorem rubi1233r19Nondeg_complex : rubi1233r19Nondeg.Holds .complex :=
  rubi1233r19Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec52
