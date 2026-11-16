import OSR.IntegrationRec45

/-!
# Integration (RUBI): corrected variants, tenth batch

Strengthened variant (Specification V1-R-005e) of the refuted RUBI rule
1.2.1.3 #24, with two conditions appended to the converted conditions,
`c (m + 2 p + 2) ≠ 0` and `e ≠ 0`.  Proved over ℝ and ℂ; the refutation of
the rule as stated is kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec46

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.1.3 #24 when c (m + 2 p + 2) ≠ 0 and e ≠ 0 -/
def rubi1213r24Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r24_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:24"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.var "g") (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.var "f")))) (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))))) (.int 0),
    .ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int 0),
    .ne (.var "e") (.int 0)]
  priority := 7260
  description := "RUBI 1.2.1.3 #24 when c (m + 2 p + 2) ≠ 0 and e ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:24" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#24"

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





/-- **1.2.1.3 #24** with `c (m + 2 p + 2) ≠ 0` and `e ≠ 0`. -/
theorem rubi1213r24Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1213r24Nondeg.conditions rubi1213r24Nondeg.body rubi1213r24Nondeg.result := by
  intro env hc t hF
  have hW : (env "c" * (env "m" + 2 * env "p" + 2)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int 0)) (by simp [rubi1213r24Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1213r24Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r24Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have h2 : env "m" * (env "g" * (env "c" * env "d" + -1 * env "b" * env "e") + env "c" * env "e" * env "f") +
      env "e" * (env "p" + 1) * (2 * env "c" * env "f" + -1 * env "b" * env "g") = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.var "g") (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.var "f")))) (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))))) (.int 0)) (by simp [rubi1213r24Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r24Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r24Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1213r24Nondeg.body →
      (k < 0 → (env "d" + env "e" * w) ≠ 0) ∧ (q < 0 → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1213r24Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have hDG : ∀ w, (k < 0 → (env "d" + env "e" * w) ≠ 0) → (q < 0 → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0) →
      Defined I (Function.update env "x" w) rubi1213r24Nondeg.result := by
    intro w h1 h2
    have hW' := hW
    simp only [mul_ne_zero_iff] at hW'
    simp [rubi1213r24Nondeg, Defined, eval, hkm, hkp1, toInt?_neg_one, toInt?_two]
    exact ⟨⟨h1, fun h => h2 (by omega)⟩, hW'.1, hW'.2⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1213r24Nondeg.result =
        env "g" * (env "d" + env "e" * w) ^ k * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) * (env "c" * (env "m" + 2 * env "p" + 2))⁻¹ := by
      intro w
      simp [rubi1213r24Nondeg, eval, hkm, hkp1, toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1213r24Nondeg.body =
        (env "d" + env "e" * t) ^ k * (env "f" + env "g" * t) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1213r24Nondeg, eval, hkm, hkp, toInt?_two]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1213r24Nondeg.result) =
        fun w => env "g" * (env "d" + env "e" * w) ^ k * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) * (env "c" * (env "m" + 2 * env "p" + 2))⁻¹ from funext hE]
    have hA : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hB : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hB0 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have key : (k : 𝕜) * (env "d" + env "e" * t) ^ (k - 1) * (env "d" + env "e" * t) = (k : 𝕜) * (env "d" + env "e" * t) ^ k := by
      rcases em (k = 0) with h0 | h0
      · subst h0; simp
      · have h' : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases h : k < 0
          · exact Or.inl (ht.1 h)
          · exact Or.inr (by omega)
        rw [show (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 1) * (env "d" + env "e" * t) by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have hQ : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2)
        (env "b" * 1 + env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
        (((hasDerivAt_id' t).pow 2).const_mul (env "c"))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow k _ hA)
      (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))).const_mul (env "g")).mul
        (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hB) hQ)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [zpow_succ_of _ _ hB0]
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = Y
    generalize (env "d" + env "e" * t) ^ (k - 1) = Z at key ⊢
    generalize (env "d" + env "e" * t) ^ k = X at key ⊢
    simp only [hm, hp] at h2 hW ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hW]
    refine mul_left_cancel₀ (pow_ne_zero 2 he) ?_
    linear_combination (env "g" * env "e" * Y * (env "c" * env "e" * t + env "b" * env "e" - env "c" * env "d")) * key +
      (env "g" * (k : 𝕜) * env "e" * Y * Z) * h1 - (env "e" * X * Y) * h2

theorem rubi1213r24Nondeg_real : rubi1213r24Nondeg.Holds .real :=
  rubi1213r24Nondeg_holds Interp.real

theorem rubi1213r24Nondeg_complex : rubi1213r24Nondeg.Holds .complex :=
  rubi1213r24Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec46
