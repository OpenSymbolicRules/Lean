import OSR.IntegrationRec42

/-!
# Integration (RUBI): corrected variants, seventh batch

Strengthened variants (Specification V1-R-005e) of the refuted RUBI rules
1.2.3.5 #2 and 1.2.1.3 #14, with a non-degeneracy condition appended to the
converted conditions.  Proved over ℝ and ℂ; the refutations of the rules as
stated are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec43

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.3.5 #2 when a ≠ 0 -/
def rubi1235r2Nondeg : CRule where
  id := "integration.rubi_1_2_3_5_r2_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:2"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "f") (.pow (.var "x") (.var "n2")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.var "a") (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "n", "p", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "a") (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0),
    .ne (.var "a") (.int 0)]
  priority := 7200
  description := "RUBI 1.2.3.5 #2 when a ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:2" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p.m#2"

/-- RUBI 1.2.1.3 #14 when 2 c (p + 1) (2 p + 3) ≠ 0 -/
def rubi1213r14Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r14_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:14"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g"))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "g")) (.app2 .add (.var "p") (.int 1))) (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int (-1))))
  independent := ["a", "c", "d", "e", "f", "g", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))) (.int 0),
    .ne (.var "p") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 0)]
  priority := 7210
  description := "RUBI 1.2.1.3 #14 when 2 c (p + 1) (2 p + 3) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:14" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#14"

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



/-- **1.2.3.5 #2** with `a ≠ 0`. -/
theorem rubi1235r2Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1235r2Nondeg.conditions rubi1235r2Nondeg.body rubi1235r2Nondeg.result := by
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi1235r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1235r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "a" * env "e" + -1 * env "b" * env "d" * (env "n" * (env "p" + 1) + 1) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0)) (by simp [rubi1235r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h2 : env "a" * env "f" + -1 * env "c" * env "d" * (2 * env "n" * (env "p" + 1) + 1) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0)) (by simp [rubi1235r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1235r2Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1235r2Nondeg, Defined, eval, hkp] at h
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkn2 : I.toInt? (env "n2") = some (2 * j) :=
    (I.toInt?_eq _ _).2 (by rw [hn2, hn]; push_cast; ring)
  have hk2n : I.toInt? (2 * env "n") = some (2 * j) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1235r2Nondeg.body →
      (j < 0 → w ≠ 0) ∧ (q < 0 → (env "a" + env "b" * w ^ j + env "c" * w ^ (2 * j)) ≠ 0) := by
    intro w h
    simp [rubi1235r2Nondeg, Defined, eval, hkn, hkn2, hkp] at h
    refine ⟨fun hj => ?_, fun hq => ?_⟩ <;> tauto
  have hDG : ∀ w, (j < 0 → w ≠ 0) → (q < 0 → (env "a" + env "b" * w ^ j + env "c" * w ^ (2 * j)) ≠ 0) →
      Defined I (Function.update env "x" w) rubi1235r2Nondeg.result := by
    intro w h1 h2
    simp [rubi1235r2Nondeg, Defined, eval, hkn, hk2n, hkp1, toInt?_neg_one, ha]
    exact ⟨⟨h1, fun h => h1 (by omega)⟩, fun h => h2 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1235r2Nondeg.result =
        env "d" * w * (env "a" + env "b" * w ^ j + env "c" * w ^ (2 * j)) ^ (q + 1) *
          (env "a")⁻¹ := by
      intro w
      simp [rubi1235r2Nondeg, eval, hkn, hk2n, hkp1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1235r2Nondeg.body =
        (env "d" + env "e" * t ^ j + env "f" * t ^ (2 * j)) * (env "a" + env "b" * t ^ j + env "c" * t ^ (2 * j)) ^ q := by
      simp [rubi1235r2Nondeg, eval, hkn, hkn2, hkp]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1235r2Nondeg.result) =
        fun w => env "d" * w * (env "a" + env "b" * w ^ j + env "c" * w ^ (2 * j)) ^ (q + 1) *
          (env "a")⁻¹ from funext hE]
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hx2 : t ≠ 0 ∨ 0 ≤ 2 * j := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hu : (env "a" + env "b" * t ^ j + env "c" * t ^ (2 * j)) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hu0 : (env "a" + env "b" * t ^ j + env "c" * t ^ (2 * j)) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have kA : (j : 𝕜) * t ^ (j - 1) * t = (j : 𝕜) * t ^ j := by
      rcases em (j = 0) with h0 | h0
      · subst h0; simp
      · have h' : t ≠ 0 ∨ 0 ≤ j - 1 := by
          by_cases h : j < 0
          · exact Or.inl (ht.1 h)
          · exact Or.inr (by omega)
        rw [show t ^ j = t ^ (j - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have kB : ((2 * j : ℤ) : 𝕜) * t ^ (2 * j - 1) * t = ((2 * j : ℤ) : 𝕜) * t ^ (2 * j) := by
      rcases em (j = 0) with h0 | h0
      · subst h0; simp
      · have h' : t ≠ 0 ∨ 0 ≤ 2 * j - 1 := by
          by_cases h : j < 0
          · exact Or.inl (ht.1 h)
          · exact Or.inr (by omega)
        rw [show t ^ (2 * j) = t ^ (2 * j - 1) * t by rw [← zpow_succ_of _ _ h', sub_add_cancel]]
        ring
    have hin : HasDerivAt (fun w => env "a" + env "b" * w ^ j + env "c" * w ^ (2 * j))
        (env "b" * ((j : 𝕜) * t ^ (j - 1)) + env "c" * (((2 * j : ℤ) : 𝕜) * t ^ (2 * j - 1))) t :=
      (((hasDerivAt_zpow j t hx).const_mul (env "b")).const_add (env "a")).add
        ((hasDerivAt_zpow (2 * j) t hx2).const_mul (env "c"))
    refine ((((hasDerivAt_id' t).const_mul (env "d")).mul (HasDerivAt.comp t
      (hasDerivAt_zpow (q + 1) _ hu) hin)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hu0]
    generalize (env "a" + env "b" * t ^ j + env "c" * t ^ (2 * j)) ^ q = V
    generalize t ^ (j - 1) = R1 at kA ⊢
    generalize t ^ (2 * j - 1) = R2 at kB ⊢
    generalize t ^ j = T1 at kA ⊢
    generalize t ^ (2 * j) = T2 at kB ⊢
    rw [hn, hp] at h1 h2
    push_cast at kB ⊢
    rw [mul_inv_eq_iff_eq_mul₀ ha]
    linear_combination (env "d" * ((q : 𝕜) + 1) * V * env "b") * kA +
      (env "d" * ((q : 𝕜) + 1) * V * env "c") * kB - (V * T1) * h1 - (V * T2) * h2

theorem rubi1235r2Nondeg_real : rubi1235r2Nondeg.Holds .real :=
  rubi1235r2Nondeg_holds Interp.real

theorem rubi1235r2Nondeg_complex : rubi1235r2Nondeg.Holds .complex :=
  rubi1235r2Nondeg_holds Interp.complex

/-- **1.2.1.3 #14** with `2 c (p + 1) (2 p + 3) ≠ 0`. -/
theorem rubi1213r14Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1213r14Nondeg.conditions rubi1213r14Nondeg.body rubi1213r14Nondeg.result := by
  intro env hc t hF
  have hW : (2 * env "c" * (env "p" + 1) * (2 * env "p" + 3)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 0)) (by simp [rubi1213r14Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "a" * env "e" * env "g" + -1 * env "c" * env "d" * env "f" * (2 * env "p" + 3) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))) (.int 0)) (by simp [rubi1213r14Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r14Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1213r14Nondeg.body ↔
      (q < 0 → env "a" + env "c" * w ^ 2 ≠ 0) := by
    intro w
    simp [rubi1213r14Nondeg, Defined, eval, hkp, toInt?_two]
  have hDG : ∀ w, (q < 0 → env "a" + env "c" * w ^ 2 ≠ 0) →
      Defined I (Function.update env "x" w) rubi1213r14Nondeg.result := by
    intro w h
    have hW' := hW
    simp only [mul_ne_zero_iff] at hW'
    simp [rubi1213r14Nondeg, Defined, eval, hkp1, toInt?_neg_one, toInt?_two]
    exact ⟨fun h' => h (by omega), hW'.1, hW'.2⟩
  have ht := (hD t).1 hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w ((hD w).1 hw)
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1213r14Nondeg.result =
        ((env "e" * env "f" + env "d" * env "g") * (2 * env "p" + 3) + 2 * env "e" * env "g" * (env "p" + 1) * w) * (env "a" + env "c" * w ^ 2) ^ (q + 1) * (2 * env "c" * (env "p" + 1) * (2 * env "p" + 3))⁻¹ := by
      intro w
      simp [rubi1213r14Nondeg, eval, hkp1, toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1213r14Nondeg.body =
        (env "d" + env "e" * t) * (env "f" + env "g" * t) * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1213r14Nondeg, eval, hkp, toInt?_two]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1213r14Nondeg.result) =
        fun w => ((env "e" * env "f" + env "d" * env "g") * (2 * env "p" + 3) + 2 * env "e" * env "g" * (env "p" + 1) * w) * (env "a" + env "c" * w ^ 2) ^ (q + 1) * (2 * env "c" * (env "p" + 1) * (2 * env "p" + 3))⁻¹ from funext hE]
    have hu : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hu0 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hQ : HasDerivAt (fun w => env "a" + env "c" * w ^ 2) (env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).pow 2).const_mul (env "c")).const_add (env "a")
    refine (((((hasDerivAt_id' t).const_mul (2 * env "e" * env "g" * (env "p" + 1))).const_add
      ((env "e" * env "f" + env "d" * env "g") * (2 * env "p" + 3))).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (q + 1) _ hu) hQ)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [zpow_succ_of _ _ hu0]
    generalize (env "a" + env "c" * t ^ 2) ^ q = Y
    simp only [hp] at h1 hW ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hW]
    linear_combination (Y * ((q : 𝕜) + 1) * 2) * h1

theorem rubi1213r14Nondeg_real : rubi1213r14Nondeg.Holds .real :=
  rubi1213r14Nondeg_holds Interp.real

theorem rubi1213r14Nondeg_complex : rubi1213r14Nondeg.Holds .complex :=
  rubi1213r14Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec43
