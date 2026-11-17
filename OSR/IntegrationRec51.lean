import OSR.IntegrationNum1

/-!
# Integration (RUBI): proofs of strengthened variants checked numerically, third batch

Proofs of the strengthened variants of 1.1.3.4 #17 and 1.2.1.3 #35, first
distributed unproved (`OSR.IntegrationNum1`, which keeps their definitions).  Proved over ℝ and ℂ for
every choice of antiderivatives of the residual integrand.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec51

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








/-- **1.1.3.4 #17** with `a b e (m + 1) ≠ 0` and `b ≠ 0`. -/
theorem rubi1134r17Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1134r17Nondeg.conditions rubi1134r17Nondeg.body rubi1134r17Nondeg.result rubi1134r17Nondeg.integrals := by
  intro env hc t hF
  have hW1 : (env "a" * env "b" * env "e" * (env "m" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "e")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1134r17Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hb : env "b" ≠ 0 := by
    have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi1134r17Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h2 : env "m" + env "n" * (env "p" + 1) + 1 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)) (.int 0)) (by simp [rubi1134r17Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r17Nondeg, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r17Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r17Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1134r17Nondeg.body →
      (k < 0 → env "e" ≠ 0 ∧ w ≠ 0) ∧ (j < 0 → w ≠ 0) ∧ (q < 0 → (env "a" + env "b" * w ^ j) ≠ 0) := by
    intro w h
    simp [rubi1134r17Nondeg, Defined, eval, hkm, hkn, hkp] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1134r17Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    simp [Defined, eval, hkm, hkn, hkp1]
    exact ⟨h1', h2', fun h => h3' (by omega)⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1', h2', h3'⟩ := hD w hw
    simp [rubi1134r17Nondeg, Defined, eval, recEnv, hkm1, hkn, hkp1, toInt?_neg_one]
    exact ⟨⟨⟨fun h => h1' (by omega), h2', fun h => h3' (by omega)⟩,
      ⟨⟨left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hW1)),
        right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hW1))⟩,
        right_ne_zero_of_mul (left_ne_zero_of_mul hW1)⟩, right_ne_zero_of_mul hW1⟩, hb⟩
  · simp only [rubi1134r17Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" * t) ^ k * (env "a" + env "b" * t ^ j) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, hkm, hkn, hkp1]
    have hEF : eval I (Function.update env "x" t) rubi1134r17Nondeg.body =
        (env "e" * t) ^ k * (env "a" + env "b" * t ^ j) ^ q * (env "c" + env "d" * t ^ j) := by
      simp [rubi1134r17Nondeg, eval, hkm, hkn, hkp]
    have hfun : (fun w => eval I (recEnv env (rubi1134r17Nondeg.integrals.map (·.1)) Φ "x" w) rubi1134r17Nondeg.result) =
        fun w => (env "b" * env "c" + -1 * env "a" * env "d") * (env "e" * w) ^ (k + 1) * (env "a" + env "b" * w ^ j) ^ (q + 1) * (env "a" * env "b" * env "e" * (env "m" + 1))⁻¹ +
          env "d" * (env "b")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1134r17Nondeg, eval, recEnv, hkm1, hkn, hkp1, toInt?_neg_one]
    rw [hfun, hEF]
    have hct : env "e" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (ht.1 h).1 (ht.1 h).2)
      · exact Or.inr (by omega)
    have hct0 : env "e" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (ht.1 h).1 (ht.1 h).2)
      · exact Or.inr (by omega)
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht.2.1 h)
      · exact Or.inr (by omega)
    have hu : (env "a" + env "b" * t ^ j) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2.2 (by omega))
      · exact Or.inr (by omega)
    have hu0 : (env "a" + env "b" * t ^ j) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2.2 h)
      · exact Or.inr (by omega)
    have key : (j : 𝕜) * t ^ (j - 1) * t = (j : 𝕜) * t ^ j := by
      rcases em (j = 0) with h0 | h0
      · subst h0; simp
      · have h' : t ≠ 0 ∨ 0 ≤ j - 1 := by
          by_cases h : j < 0
          · exact Or.inl (ht.2.1 h)
          · exact Or.inr (by omega)
        rw [show t ^ j = t ^ (j - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have hin : HasDerivAt (fun w => env "a" + env "b" * w ^ j) (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "b")).const_add (env "a")
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hct)
      ((hasDerivAt_id' t).const_mul (env "e"))).const_mul (env "b" * env "c" + -1 * env "a" * env "d")).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (q + 1) _ hu) hin)).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hct0, zpow_succ_of _ _ hu0]
    generalize (env "e" * t) ^ k = C
    generalize (env "a" + env "b" * t ^ j) ^ q = Y
    generalize t ^ (j - 1) = R at key ⊢
    generalize t ^ j = T at key ⊢
    simp only [hm, hn, hp] at hW1 h2 ⊢
    set u1 := (env "a" * env "b" * env "e" * ((k : 𝕜) + 1))⁻¹ with hu1_def
    set u2 := (env "b")⁻¹ with hu2_def
    have hU1 : env "a" * env "b" * env "e" * ((k : 𝕜) + 1) * u1 = 1 := by
      rw [hu1_def]; exact mul_inv_cancel₀ hW1
    have hU2 : env "b" * u2 = 1 := by rw [hu2_def]; exact mul_inv_cancel₀ hb
    have hrel : env "a" * env "e" * ((k : 𝕜) + 1) * u1 = u2 := by
      have h0 : env "b" * (env "a" * env "e" * ((k : 𝕜) + 1) * u1 - u2) = 0 := by
        linear_combination hU1 - hU2
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hb
      · linear_combination h
    push_cast
    linear_combination (C * Y * (env "c" + env "d" * T)) * hU2 +
      ((env "b" * env "c" + -1 * env "a" * env "d") * u1 * env "e" * C * Y * ((q : 𝕜) + 1) * env "b") * key +
      ((env "b" * env "c" + -1 * env "a" * env "d") * u1 * env "e" * C * Y * env "b" * T) * h2 + ((env "b" * env "c" + -1 * env "a" * env "d") * C * Y) * hrel

theorem rubi1134r17Nondeg_real : rubi1134r17Nondeg.Holds .real :=
  rubi1134r17Nondeg_holds Interp.real

theorem rubi1134r17Nondeg_complex : rubi1134r17Nondeg.Holds .complex :=
  rubi1134r17Nondeg_holds Interp.complex

/-- **1.2.1.3 #35** with `c ≠ 0`: `x² = (a + c x²)/c - a/c`. -/
theorem rubi1213r35Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1213r35Nondeg.conditions rubi1213r35Nondeg.body rubi1213r35Nondeg.result rubi1213r35Nondeg.integrals := by
  intro env hc t hF
  have hc0 : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi1213r35Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r35Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1213r35Nondeg.body → (q < 0 → (env "a" + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1213r35Nondeg, Defined, eval, hkp, toInt?_two] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1213r35Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, hkp1, toInt?_two]
      exact fun h' => h (by omega)
    · filter_upwards [hF] with w hw
      have h := hD w hw
      simp [Defined, eval, hkp, toInt?_two]
      exact h
  · exact Eventually.of_forall fun w => by
      simp [rubi1213r35Nondeg, Defined, eval, recEnv, toInt?_neg_one, hc0]
  · simp only [rubi1213r35Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" + env "g" * t) * (env "a" + env "c" * t ^ 2) ^ (q + 1)) t := by
      convert hΦ1 using 1
      simp [eval, hkp1, toInt?_two]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" + env "g" * t) * (env "a" + env "c" * t ^ 2) ^ q) t := by
      convert hΦ2 using 1
      simp [eval, hkp, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1213r35Nondeg.body =
        t ^ 2 * (env "f" + env "g" * t) * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1213r35Nondeg, eval, hkp, toInt?_two]
    have hfun : (fun w => eval I (recEnv env (rubi1213r35Nondeg.integrals.map (·.1)) Φ "x" w) rubi1213r35Nondeg.result) =
        fun w => 1 * (env "c")⁻¹ * Φ "I1" w + -1 * env "a" * (env "c")⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1213r35Nondeg, eval, recEnv, toInt?_neg_one]
    rw [hfun, hEF]
    have hu0 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    rw [zpow_succ_of _ _ hu0]
    have hci : env "c" * (env "c")⁻¹ = 1 := mul_inv_cancel₀ hc0
    linear_combination ((env "f" + env "g" * t) * (env "a" + env "c" * t ^ 2) ^ q * t ^ 2) * hci

theorem rubi1213r35Nondeg_real : rubi1213r35Nondeg.Holds .real :=
  rubi1213r35Nondeg_holds Interp.real

theorem rubi1213r35Nondeg_complex : rubi1213r35Nondeg.Holds .complex :=
  rubi1213r35Nondeg_holds Interp.complex

/-- **rubi1224r11Nondeg** with `d ≠ 0` and `e ≠ 0`: the quartic factors as `(d + e x²) (a/d + c x²/e)`. -/
theorem rubi1224r11Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1224r11Nondeg.conditions rubi1224r11Nondeg.body rubi1224r11Nondeg.result rubi1224r11Nondeg.integrals := by
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1224r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1224r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1224r11Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hdi : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd
  have hei : env "e" * (env "e")⁻¹ = 1 := mul_inv_cancel₀ he
  have hQ : ∀ w : 𝕜, (env "a" + env "b" * w ^ 2 + env "c" * w ^ 4) = (env "d" + env "e" * w ^ 2) * (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ 2) := fun w => by
    linear_combination (-w ^ 2 * (env "d")⁻¹ * (env "e")⁻¹) * h1 +
      (env "c" * env "d" * (env "e")⁻¹ * w ^ 2 - env "b" * w ^ 2 * env "e" * (env "e")⁻¹) * hdi +
      (env "a" * env "e" * (env "d")⁻¹ * w ^ 2 - env "b" * w ^ 2) * hei - env "a" * hdi - env "c" * w ^ 4 * hei
  rcases hkf : I.toInt? (env "m") with _ | k0
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r11Nondeg, Defined, eval, hkf] at h
  rcases hkm : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r11Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r11Nondeg, Defined, eval, hkp] at h
  have hm : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "q" + env "p") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1224r11Nondeg.body →
      (k0 < 0 → env "f" ≠ 0 ∧ w ≠ 0) ∧ (k < 0 → (env "d" + env "e" * w ^ 2) ≠ 0) ∧ (q < 0 → (env "a" + env "b" * w ^ 2 + env "c" * w ^ 4) ≠ 0) := by
    intro w h
    simp [rubi1224r11Nondeg, Defined, eval, hkf, hkm, hkp, toInt?_two, toInt?_four] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r11Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h0', h1', h2'⟩ := hD w hw
    simp [Defined, eval, hkf, hkmp, hkp, toInt?_neg_one, toInt?_two, hd, he]
    refine ⟨⟨h0', fun hkq hD0 => ?_⟩, fun hq hL => h2' hq (by rw [hQ w, hL, mul_zero])⟩
    by_cases hq : q < 0
    · exact h2' hq (by rw [hQ w, hD0, zero_mul])
    · exact h1' (by omega) hD0
  · exact Eventually.of_forall fun w => by simp [rubi1224r11Nondeg, Defined, eval, recEnv]
  · simp only [rubi1224r11Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1224r11Nondeg.integrals.map (·.1)) Φ "x" w) rubi1224r11Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1224r11Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi1224r11Nondeg, eval, hkf, hkm, hkp, hkmp, toInt?_neg_one, toInt?_two, toInt?_four]
    have hz : (env "d" + env "e" * t ^ 2) ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases hD0 : (env "d" + env "e" * t ^ 2) = 0
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
    rw [hQ t, mul_zpow (env "d" + env "e" * t ^ 2) _ q, zpow_add' hz]
    ring

theorem rubi1224r11Nondeg_real : rubi1224r11Nondeg.Holds .real :=
  rubi1224r11Nondeg_holds Interp.real

theorem rubi1224r11Nondeg_complex : rubi1224r11Nondeg.Holds .complex :=
  rubi1224r11Nondeg_holds Interp.complex

/-- **rubi1224r12Nondeg** with `d ≠ 0` and `e ≠ 0`: the quartic factors as `(d + e x²) (a/d + c x²/e)`. -/
theorem rubi1224r12Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1224r12Nondeg.conditions rubi1224r12Nondeg.body rubi1224r12Nondeg.result rubi1224r12Nondeg.integrals := by
  intro env hc t hF
  have hd : env "d" ≠ 0 := by
    have h := hc (.ne (.var "d") (.int 0)) (by simp [rubi1224r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1224r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1224r12Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have hdi : env "d" * (env "d")⁻¹ = 1 := mul_inv_cancel₀ hd
  have hei : env "e" * (env "e")⁻¹ = 1 := mul_inv_cancel₀ he
  have hQ : ∀ w : 𝕜, (env "a" + env "c" * w ^ 4) = (env "d" + env "e" * w ^ 2) * (env "a" * (env "d")⁻¹ + env "c" * (env "e")⁻¹ * w ^ 2) := fun w => by
    linear_combination (-w ^ 2 * (env "d")⁻¹ * (env "e")⁻¹) * h1 +
      (env "c" * env "d" * (env "e")⁻¹ * w ^ 2) * hdi +
      (env "a" * env "e" * (env "d")⁻¹ * w ^ 2) * hei - env "a" * hdi - env "c" * w ^ 4 * hei
  rcases hkf : I.toInt? (env "m") with _ | k0
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r12Nondeg, Defined, eval, hkf] at h
  rcases hkm : I.toInt? (env "q") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r12Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1224r12Nondeg, Defined, eval, hkp] at h
  have hm : env "q" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkmp : I.toInt? (env "q" + env "p") = some (k + q) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1224r12Nondeg.body →
      (k0 < 0 → env "f" ≠ 0 ∧ w ≠ 0) ∧ (k < 0 → (env "d" + env "e" * w ^ 2) ≠ 0) ∧ (q < 0 → (env "a" + env "c" * w ^ 4) ≠ 0) := by
    intro w h
    simp [rubi1224r12Nondeg, Defined, eval, hkf, hkm, hkp, toInt?_two, toInt?_four] at h
    tauto
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1224r12Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h0', h1', h2'⟩ := hD w hw
    simp [Defined, eval, hkf, hkmp, hkp, toInt?_neg_one, toInt?_two, hd, he]
    refine ⟨⟨h0', fun hkq hD0 => ?_⟩, fun hq hL => h2' hq (by rw [hQ w, hL, mul_zero])⟩
    by_cases hq : q < 0
    · exact h2' hq (by rw [hQ w, hD0, zero_mul])
    · exact h1' (by omega) hD0
  · exact Eventually.of_forall fun w => by simp [rubi1224r12Nondeg, Defined, eval, recEnv]
  · simp only [rubi1224r12Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (rubi1224r12Nondeg.integrals.map (·.1)) Φ "x" w) rubi1224r12Nondeg.result) =
        Φ "I1" := by
      funext w
      simp [rubi1224r12Nondeg, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi1224r12Nondeg, eval, hkf, hkm, hkp, hkmp, toInt?_neg_one, toInt?_two, toInt?_four]
    have hz : (env "d" + env "e" * t ^ 2) ≠ 0 ∨ k + q ≠ 0 ∨ k = 0 ∧ q = 0 := by
      by_cases hD0 : (env "d" + env "e" * t ^ 2) = 0
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
    rw [hQ t, mul_zpow (env "d" + env "e" * t ^ 2) _ q, zpow_add' hz]
    ring

theorem rubi1224r12Nondeg_real : rubi1224r12Nondeg.Holds .real :=
  rubi1224r12Nondeg_holds Interp.real

theorem rubi1224r12Nondeg_complex : rubi1224r12Nondeg.Holds .complex :=
  rubi1224r12Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec51
