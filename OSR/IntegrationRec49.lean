import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically

Proofs of strengthened variants first distributed unproved
(`OSR.IntegrationNum1`, which keeps their definitions): 1.2.2.3 #7 and #8,
where `c d² - b d e + a e² = 0` factors the quartic as
`(d + e x²) (a/d + c x²/e)`, and 1.1.3.3 #15.  Proved over ℝ and ℂ for every
choice of antiderivatives of the residual integrands.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec49

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







/-- **rubi1223r7Nondeg** with `d ≠ 0` and `e ≠ 0`: the quartic factors as `(d + e x²) (a/d + c x²/e)`. -/
theorem rubi1223r7Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1223r7Nondeg.conditions rubi1223r7Nondeg.body rubi1223r7Nondeg.result rubi1223r7Nondeg.integrals := by
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1223r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1223r7Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1223r7Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hdi : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd
  have hei : env "e" * (env "e")⁻¹ = 1 := mul_inv_cancel₀ he
  have hQ : ∀ w : 𝕜, (env "a" + env "b" * w ^ 2 + env "c" * w ^ 4) = (env "d" + env "e" * w ^ 2) * (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ 2) := fun w => by
    linear_combination (-w ^ 2 * (env "d")⁻¹ * (env "e")⁻¹) * h1 +
      (env "c" * env "d" * (env "e")⁻¹ * w ^ 2 - env "b" * w ^ 2 * env "e" * (env "e")⁻¹) * hdi +
      (env "a" * env "e" * (env "d")⁻¹ * w ^ 2 - env "b" * w ^ 2) * hei - env "a" * hdi - env "c" * w ^ 4 * hei
  rcases hkm : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1223r7Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1223r7Nondeg, Defined, eval, hkp] at h
  have hm : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "p" + env "q") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1223r7Nondeg.body →
      (k < 0 → (env "d" + env "e" * w ^ 2) ≠ 0) ∧ (q < 0 → (env "a" + env "b" * w ^ 2 + env "c" * w ^ 4) ≠ 0) := by
    intro w h
    simp [rubi1223r7Nondeg, Defined, eval, hkm, hkp, toInt?_two, toInt?_four] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1223r7Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1', h2'⟩ := hD w hw
    simp [Defined, eval, hkmp, hkp, toInt?_neg_one, toInt?_two, hd, he]
    refine ⟨fun hkq hD0 => ?_, fun hq hL => h2' hq (by rw [hQ w, hL, mul_zero])⟩
    by_cases hq : q < 0
    · exact h2' hq (by rw [hQ w, hD0, zero_mul])
    · exact h1' (by omega) hD0
  · exact Eventually.of_forall fun w => by simp [rubi1223r7Nondeg, Defined, eval, recEnv]
  · simp only [rubi1223r7Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1223r7Nondeg.integrals.map (·.1)) Φ "x" w) rubi1223r7Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1223r7Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi1223r7Nondeg, eval, hkm, hkp, hkmp, toInt?_neg_one, toInt?_two, toInt?_four]
    have hz : (env "d" + env "e" * t ^ 2) ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases hD0 : (env "d" + env "e" * t ^ 2) = 0
      · have hk : 0 ≤ k := by
          by_contra hk
          exact ht.1 (by omega) hD0
        have hq : 0 ≤ q := by
          by_contra hq
          exact ht.2 (by omega) (by rw [hQ t, hD0, zero_mul])
        by_cases hkq : k + q = 0
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inl hkq)
      · exact Or.inl hD0
    rw [hQ t, mul_zpow, zpow_add' hz]
    ring

theorem rubi1223r7Nondeg_real : rubi1223r7Nondeg.Holds .real :=
  rubi1223r7Nondeg_holds Interp.real

theorem rubi1223r7Nondeg_complex : rubi1223r7Nondeg.Holds .complex :=
  rubi1223r7Nondeg_holds Interp.complex

/-- **rubi1223r8Nondeg** with `d ≠ 0` and `e ≠ 0`: the quartic factors as `(d + e x²) (a/d + c x²/e)`. -/
theorem rubi1223r8Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1223r8Nondeg.conditions rubi1223r8Nondeg.body rubi1223r8Nondeg.result rubi1223r8Nondeg.integrals := by
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1223r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1223r8Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1223r8Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hdi : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd
  have hei : env "e" * (env "e")⁻¹ = 1 := mul_inv_cancel₀ he
  have hQ : ∀ w : 𝕜, (env "a" + env "c" * w ^ 4) = (env "d" + env "e" * w ^ 2) * (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ 2) := fun w => by
    linear_combination (-w ^ 2 * (env "d")⁻¹ * (env "e")⁻¹) * h1 +
      (env "c" * env "d" * (env "e")⁻¹ * w ^ 2) * hdi +
      (env "a" * env "e" * (env "d")⁻¹ * w ^ 2) * hei - env "a" * hdi - env "c" * w ^ 4 * hei
  rcases hkm : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1223r8Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1223r8Nondeg, Defined, eval, hkp] at h
  have hm : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "p" + env "q") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1223r8Nondeg.body →
      (k < 0 → (env "d" + env "e" * w ^ 2) ≠ 0) ∧ (q < 0 → (env "a" + env "c" * w ^ 4) ≠ 0) := by
    intro w h
    simp [rubi1223r8Nondeg, Defined, eval, hkm, hkp, toInt?_two, toInt?_four] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1223r8Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1', h2'⟩ := hD w hw
    simp [Defined, eval, hkmp, hkp, toInt?_neg_one, toInt?_two, hd, he]
    refine ⟨fun hkq hD0 => ?_, fun hq hL => h2' hq (by rw [hQ w, hL, mul_zero])⟩
    by_cases hq : q < 0
    · exact h2' hq (by rw [hQ w, hD0, zero_mul])
    · exact h1' (by omega) hD0
  · exact Eventually.of_forall fun w => by simp [rubi1223r8Nondeg, Defined, eval, recEnv]
  · simp only [rubi1223r8Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1223r8Nondeg.integrals.map (·.1)) Φ "x" w) rubi1223r8Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1223r8Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi1223r8Nondeg, eval, hkm, hkp, hkmp, toInt?_neg_one, toInt?_two, toInt?_four]
    have hz : (env "d" + env "e" * t ^ 2) ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases hD0 : (env "d" + env "e" * t ^ 2) = 0
      · have hk : 0 ≤ k := by
          by_contra hk
          exact ht.1 (by omega) hD0
        have hq : 0 ≤ q := by
          by_contra hq
          exact ht.2 (by omega) (by rw [hQ t, hD0, zero_mul])
        by_cases hkq : k + q = 0
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inl hkq)
      · exact Or.inl hD0
    rw [hQ t, mul_zpow, zpow_add' hz]
    ring

theorem rubi1223r8Nondeg_real : rubi1223r8Nondeg.Holds .real :=
  rubi1223r8Nondeg_holds Interp.real

theorem rubi1223r8Nondeg_complex : rubi1223r8Nondeg.Holds .complex :=
  rubi1223r8Nondeg_holds Interp.complex

/-- **1.1.3.3 #15** with `b (n (p + 1) + 1) ≠ 0`. -/
theorem rubi1133r15Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1133r15Nondeg.conditions rubi1133r15Nondeg.body rubi1133r15Nondeg.result rubi1133r15Nondeg.integrals := by
  intro env hc t hF
  have hW : (env "b" * (env "n" * (env "p" + 1) + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.int 0)) (by simp [rubi1133r15Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r15Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r15Nondeg, Defined, eval, hkp] at h
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1133r15Nondeg.body →
      (j < 0 → w ≠ 0) ∧ (q < 0 → (env "a" + env "b" * w ^ j) ≠ 0) := by
    intro w h
    simp [rubi1133r15Nondeg, Defined, eval, hkn, hkp] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1133r15Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1', h2'⟩ := hD w hw
    simp [Defined, eval, hkn, hkp]
    exact ⟨h1', h2'⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1', h2'⟩ := hD w hw
    simp [rubi1133r15Nondeg, Defined, eval, recEnv, hkn, hkp1, toInt?_neg_one]
    exact ⟨⟨h1', fun h => h2' (by omega)⟩, left_ne_zero_of_mul hW, right_ne_zero_of_mul hW⟩
  · simp only [rubi1133r15Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * t ^ j) ^ q) t := by
      convert hΦ using 1
      simp [eval, hkn, hkp]
    have hEF : eval I (Function.update env "x" t) rubi1133r15Nondeg.body =
        (env "a" + env "b" * t ^ j) ^ q * (env "c" + env "d" * t ^ j) := by
      simp [rubi1133r15Nondeg, eval, hkn, hkp]
    have hfun : (fun w => eval I (recEnv env (rubi1133r15Nondeg.integrals.map (·.1)) Φ "x" w) rubi1133r15Nondeg.result) =
        fun w => env "d" * w * (env "a" + env "b" * w ^ j) ^ (q + 1) * (env "b" * (env "n" * (env "p" + 1) + 1))⁻¹ + -1 * (env "a" * env "d" + -1 * env "b" * env "c" * (env "n" * (env "p" + 1) + 1)) * (env "b" * (env "n" * (env "p" + 1) + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1133r15Nondeg, eval, recEnv, hkn, hkp1, toInt?_neg_one]
    rw [hfun, hEF]
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hu : (env "a" + env "b" * t ^ j) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hu0 : (env "a" + env "b" * t ^ j) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
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
    have hin : HasDerivAt (fun w => env "a" + env "b" * w ^ j) (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "b")).const_add (env "a")
    refine (((((hasDerivAt_id' t).const_mul (env "d")).mul (HasDerivAt.comp t
      (hasDerivAt_zpow (q + 1) _ hu) hin)).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hu0]
    generalize (env "a" + env "b" * t ^ j) ^ q = Y
    generalize t ^ (j - 1) = R at key ⊢
    generalize t ^ j = T at key ⊢
    simp only [hn, hp] at hW ⊢
    set u := (env "b" * ((j : 𝕜) * ((q : 𝕜) + 1) + 1))⁻¹ with hu_def
    have hU : env "b" * ((j : 𝕜) * ((q : 𝕜) + 1) + 1) * u = 1 := by rw [hu_def]; exact mul_inv_cancel₀ hW
    push_cast
    linear_combination (Y * (env "c" + env "d" * T)) * hU + (u * Y * env "d" * ((q : 𝕜) + 1) * env "b") * key

theorem rubi1133r15Nondeg_real : rubi1133r15Nondeg.Holds .real :=
  rubi1133r15Nondeg_holds Interp.real

theorem rubi1133r15Nondeg_complex : rubi1133r15Nondeg.Holds .complex :=
  rubi1133r15Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec49
