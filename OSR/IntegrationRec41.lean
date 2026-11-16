import OSR.IntegrationRec40

/-!
# Integration (RUBI): corrected variants, fifth batch

Strengthened variants (Specification V1-R-005e) of the refuted RUBI rules
1.1.1.3 #2 and 1.2.1.1 #3, with a non-degeneracy condition appended to the
converted conditions.  Proved over ℝ and ℂ; the refutations of the rules as
stated are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec41

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.1.1.3 #2 when d f (n + p + 2) ≠ 0 -/
def rubi1113r2Nondeg : CRule where
  id := "integration.rubi_1_1_1_3_r2_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:2"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2)) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1)))))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.int 0)]
  priority := 7130
  description := "RUBI 1.1.1.3 #2 when d f (n + p + 2) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:2" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#2"

/-- RUBI 1.2.1.1 #3 when 2 c (2 p + 1) ≠ 0 -/
def rubi1211r3Nondeg : CRule where
  id := "integration.rubi_1_2_1_1_r3_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:3"
  shape := .antideriv; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))
  result := (.app2 .mul (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.var "p") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1)))),
    .ne (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.int 0)]
  priority := 7140
  description := "RUBI 1.2.1.1 #3 when 2 c (2 p + 1) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:3" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p.m#3"

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


/-- **1.1.1.3 #2** with `d f (n + p + 2) ≠ 0`. -/
theorem rubi1113r2Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1113r2Nondeg.conditions rubi1113r2Nondeg.body
      rubi1113r2Nondeg.result := by
  intro env hc t hF
  have hK : env "d" * env "f" * (env "n" + env "p" + 2) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.int 0)) (by simp [rubi1113r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : env "a" * env "d" * env "f" * (env "n" + env "p" + 2) +
      -1 * env "b" * (env "d" * env "e" * (env "n" + 1) + env "c" * env "f" * (env "p" + 1)) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1)))))) (.int 0)) (by simp [rubi1113r2Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1113r2Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1113r2Nondeg, Defined, eval, hkp] at h
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkn1 : I.toInt? (env "n" + 1) = some (j + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1113r2Nondeg.body →
      (j < 0 → env "c" + env "d" * w ≠ 0) ∧ (q < 0 → env "e" + env "f" * w ≠ 0) := by
    intro w h
    simp [rubi1113r2Nondeg, Defined, eval, hkn, hkp] at h
    tauto
  have hDG : ∀ w, (j < 0 → env "c" + env "d" * w ≠ 0) → (q < 0 → env "e" + env "f" * w ≠ 0) →
      Defined I (Function.update env "x" w) rubi1113r2Nondeg.result := by
    intro w h1 h2
    simp [rubi1113r2Nondeg, Defined, eval, hkn1, hkp1, toInt?_neg_one, hK]
    exact ⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1113r2Nondeg.result =
        env "b" * ((env "c" + env "d" * w) ^ (j + 1) * (env "e" + env "f" * w) ^ (q + 1)) *
          (env "d" * env "f" * (env "n" + env "p" + 2))⁻¹ := by
      intro w
      simp [rubi1113r2Nondeg, eval, hkn1, hkp1, toInt?_neg_one, mul_assoc]
    have hEF : eval I (Function.update env "x" t) rubi1113r2Nondeg.body =
        (env "a" + env "b" * t) * (env "c" + env "d" * t) ^ j * (env "e" + env "f" * t) ^ q := by
      simp [rubi1113r2Nondeg, eval, hkn, hkp]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1113r2Nondeg.result) =
        fun w => env "b" * ((env "c" + env "d" * w) ^ (j + 1) * (env "e" + env "f" * w) ^ (q + 1)) *
          (env "d" * env "f" * (env "n" + env "p" + 2))⁻¹ from funext hE]
    have hC : env "c" + env "d" * t ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases h : j + 1 < 0
      · exact Or.inl (ht.1 (by omega))
      · exact Or.inr (by omega)
    have hC0 : env "c" + env "d" * t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hE1 : env "e" + env "f" * t ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hE0 : env "e" + env "f" * t ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (j + 1) _ hC)
      (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c"))).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (q + 1) _ hE1)
        (((hasDerivAt_id' t).const_mul (env "f")).const_add (env "e")))).const_mul
          (env "b")).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hC0, zpow_succ_of _ _ hE0]
    generalize (env "c" + env "d" * t) ^ j = X
    generalize (env "e" + env "f" * t) ^ q = Y
    rw [hn, hp] at hK heq ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hK]
    linear_combination (-(X * Y)) * heq

theorem rubi1113r2Nondeg_real : rubi1113r2Nondeg.Holds .real :=
  rubi1113r2Nondeg_holds Interp.real

theorem rubi1113r2Nondeg_complex : rubi1113r2Nondeg.Holds .complex :=
  rubi1113r2Nondeg_holds Interp.complex

/-- **1.2.1.1 #3** with `2 c (2 p + 1) ≠ 0`. -/
theorem rubi1211r3Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1211r3Nondeg.conditions rubi1211r3Nondeg.body
      rubi1211r3Nondeg.result := by
  intro env hc t hF
  have hK : 2 * env "c" * (2 * env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.int 0)) (by simp [rubi1211r3Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : env "b" ^ 2 + -1 * 4 * env "a" * env "c" = 0 := by
    have h := hc (.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [rubi1211r3Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1211r3Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1211r3Nondeg.body ↔
      (q < 0 → env "a" + env "b" * w + env "c" * w ^ 2 ≠ 0) := by
    intro w
    simp [rubi1211r3Nondeg, Defined, eval, hkp, toInt?_two]
  have hDG : ∀ w, Defined I (Function.update env "x" w) rubi1211r3Nondeg.result ↔
      (q < 0 → env "a" + env "b" * w + env "c" * w ^ 2 ≠ 0) := by
    intro w
    simp [rubi1211r3Nondeg, Defined, eval, hkp, toInt?_neg_one, toInt?_two, hK]
  have hE : ∀ w, eval I (Function.update env "x" w) rubi1211r3Nondeg.result =
      (env "b" + 2 * env "c" * w) * (env "a" + env "b" * w + env "c" * w ^ 2) ^ q *
        (2 * env "c" * (2 * env "p" + 1))⁻¹ := by
    intro w
    simp [rubi1211r3Nondeg, eval, hkp, toInt?_neg_one, toInt?_two]
  have hEF : eval I (Function.update env "x" t) rubi1211r3Nondeg.body =
      (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
    simp [rubi1211r3Nondeg, eval, hkp, toInt?_two]
  have ht := (hD t).1 hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact (hDG w).2 ((hD w).1 hw)
  · have hne : env "a" + env "b" * t + env "c" * t ^ 2 ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have key : (q : 𝕜) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ (q - 1) *
        (env "a" + env "b" * t + env "c" * t ^ 2) =
          (q : 𝕜) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      rcases em (q = 0) with h0 | h0
      · subst h0
        simp
      · have hx1 : env "a" + env "b" * t + env "c" * t ^ 2 ≠ 0 ∨ 0 ≤ q - 1 := by
          by_cases h : q < 0
          · exact Or.inl (ht h)
          · exact Or.inr (by omega)
        rw [show (env "a" + env "b" * t + env "c" * t ^ 2) ^ q =
            (env "a" + env "b" * t + env "c" * t ^ 2) ^ (q - 1) *
              (env "a" + env "b" * t + env "c" * t ^ 2) by
          rw [← zpow_succ_of _ _ hx1, sub_add_cancel]]
        ring
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1211r3Nondeg.result) =
        fun w => (env "b" + 2 * env "c" * w) * (env "a" + env "b" * w + env "c" * w ^ 2) ^ q *
          (2 * env "c" * (2 * env "p" + 1))⁻¹ from funext hE]
    have hQ : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2)
        (env "b" * 1 + env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
        (((hasDerivAt_id' t).pow 2).const_mul (env "c"))
    refine (((((hasDerivAt_id' t).const_mul (2 * env "c")).const_add (env "b")).mul
      (HasDerivAt.comp t (hasDerivAt_zpow q _ hne) hQ)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ (q - 1) = R at key ⊢
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = V at key ⊢
    rw [hp] at hK ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hK]
    linear_combination (4 * env "c") * key + ((q : 𝕜) * R) * heq

theorem rubi1211r3Nondeg_real : rubi1211r3Nondeg.Holds .real :=
  rubi1211r3Nondeg_holds Interp.real

theorem rubi1211r3Nondeg_complex : rubi1211r3Nondeg.Holds .complex :=
  rubi1211r3Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec41
