import OSR.IntegrationRec38

/-!
# Integration (RUBI): corrected variants, third batch

Strengthened variants (Specification V1-R-005e) of the refuted RUBI rules
1.1.3.3 #10 and 1.1.3.4 #14, with a non-degeneracy condition appended to the
converted conditions.  Proved over ℝ and ℂ; the refutations of the rules as
stated are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec39

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.1.3.3 #10 when a ≠ 0 -/
def rubi1133r10Nondeg : CRule where
  id := "integration.rubi_1_1_3_3_r10_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:10"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.var "a") (.int (-1))))
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0),
    .ne (.var "a") (.int 0)]
  priority := 7080
  description := "RUBI 1.1.3.3 #10 when a ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:10" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#10"

/-- RUBI 1.1.3.4 #14 when a e (m + 1) ≠ 0 -/
def rubi1134r14Nondeg : CRule where
  id := "integration.rubi_1_1_3_4_r14_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:14"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)))) (.int 0),
    .ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1))) (.int 0)]
  priority := 7090
  description := "RUBI 1.1.3.4 #14 when a e (m + 1) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:14" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#14"

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

/-- **1.1.3.3 #10** with `a ≠ 0`. -/
theorem rubi1133r10Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1133r10Nondeg.conditions rubi1133r10Nondeg.body
      rubi1133r10Nondeg.result := by
  intro env hc t hF
  have ha : env "a" ≠ 0 := by
    have h := hc (.ne (.var "a") (.int 0)) (by simp [rubi1133r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hbc : env "b" * env "c" + -1 * env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1133r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : env "a" * env "d" + -1 * env "b" * env "c" * (env "n" * (env "p" + 1) + 1) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0)) (by simp [rubi1133r10Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r10Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1133r10Nondeg, Defined, eval, hkp] at h
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  rw [hn, hp] at heq
  have hj : j ≠ 0 := by
    intro h
    apply hbc
    rw [h] at heq
    push_cast at heq
    linear_combination (-1 : 𝕜) * heq
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1133r10Nondeg.body →
      (j < 0 → w ≠ 0) ∧ (q < 0 → env "a" + env "b" * w ^ j ≠ 0) := by
    intro w h
    simp [rubi1133r10Nondeg, Defined, eval, hkn, hkp] at h
    tauto
  have hDG : ∀ w, (j < 0 → w ≠ 0) → (q < 0 → env "a" + env "b" * w ^ j ≠ 0) →
      Defined I (Function.update env "x" w) rubi1133r10Nondeg.result := by
    intro w h1 h2
    simp [rubi1133r10Nondeg, Defined, eval, hkn, hkp1, toInt?_neg_one, ha]
    exact ⟨fun h => h1 h, fun h => h2 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1133r10Nondeg.result =
        env "c" * w * (env "a" + env "b" * w ^ j) ^ (q + 1) * (env "a")⁻¹ := by
      intro w
      simp [rubi1133r10Nondeg, eval, hkn, hkp1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1133r10Nondeg.body =
        (env "a" + env "b" * t ^ j) ^ q * (env "c" + env "d" * t ^ j) := by
      simp [rubi1133r10Nondeg, eval, hkn, hkp]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1133r10Nondeg.result) =
        fun w => env "c" * w * (env "a" + env "b" * w ^ j) ^ (q + 1) * (env "a")⁻¹ from funext hE]
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hx1 : t ≠ 0 ∨ 0 ≤ j - 1 := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hu : env "a" + env "b" * t ^ j ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hu0 : env "a" + env "b" * t ^ j ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have htj : t ^ j = t ^ (j - 1) * t := by
      rw [← zpow_succ_of _ _ hx1, sub_add_cancel]
    have hin : HasDerivAt (fun w => env "a" + env "b" * w ^ j)
        (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "b")).const_add (env "a")
    refine ((((hasDerivAt_id' t).const_mul (env "c")).mul (HasDerivAt.comp t
      (hasDerivAt_zpow (q + 1) _ hu) hin)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hu0]
    generalize (env "a" + env "b" * t ^ j) ^ q = V
    rw [htj]
    generalize t ^ (j - 1) = T
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ ha]
    linear_combination (-(V * T * t)) * heq

theorem rubi1133r10Nondeg_real : rubi1133r10Nondeg.Holds .real :=
  rubi1133r10Nondeg_holds Interp.real

theorem rubi1133r10Nondeg_complex : rubi1133r10Nondeg.Holds .complex :=
  rubi1133r10Nondeg_holds Interp.complex

/-- **1.1.3.4 #14** with `a e (m + 1) ≠ 0`. -/
theorem rubi1134r14Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1134r14Nondeg.conditions rubi1134r14Nondeg.body
      rubi1134r14Nondeg.result := by
  intro env hc t hF
  have hae : env "a" * env "e" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1134r14Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hbc : env "b" * env "c" + -1 * env "a" * env "d" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [rubi1134r14Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : env "a" * env "d" * (env "m" + 1) +
      -1 * env "b" * env "c" * (env "m" + env "n" * (env "p" + 1) + 1) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)))) (.int 0)) (by simp [rubi1134r14Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r14Nondeg, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r14Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1134r14Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  rw [hm, hn, hp] at heq
  have hm1 : (k : 𝕜) + 1 ≠ 0 := by rw [← hm]; exact right_ne_zero_of_mul hae
  have hj : j ≠ 0 := by
    intro h
    apply hbc
    rw [h] at heq
    push_cast at heq
    have : (env "a" * env "d" + -1 * env "b" * env "c") * ((k : 𝕜) + 1) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.1 this with h0 | h0
    · linear_combination (-1 : 𝕜) * h0
    · exact absurd h0 hm1
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1134r14Nondeg.body →
      (k < 0 → env "e" ≠ 0 ∧ w ≠ 0) ∧ (j < 0 → w ≠ 0) ∧
        (q < 0 → env "a" + env "b" * w ^ j ≠ 0) := by
    intro w h
    simp [rubi1134r14Nondeg, Defined, eval, hkm, hkn, hkp] at h
    tauto
  have hDG : ∀ w, (k < 0 → env "e" ≠ 0 ∧ w ≠ 0) → (j < 0 → w ≠ 0) →
      (q < 0 → env "a" + env "b" * w ^ j ≠ 0) →
      Defined I (Function.update env "x" w) rubi1134r14Nondeg.result := by
    intro w h1 h2 h3
    simp [rubi1134r14Nondeg, Defined, eval, hkm1, hkn, hkp1, toInt?_neg_one, hae]
    exact ⟨fun h => h1 (by omega), h2, fun h => h3 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2.1 (hD w hw).2.2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1134r14Nondeg.result =
        env "c" * (env "e" * w) ^ (k + 1) * (env "a" + env "b" * w ^ j) ^ (q + 1) *
          (env "a" * env "e" * (env "m" + 1))⁻¹ := by
      intro w
      simp [rubi1134r14Nondeg, eval, hkm1, hkn, hkp1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1134r14Nondeg.body =
        (env "e" * t) ^ k * (env "a" + env "b" * t ^ j) ^ q * (env "c" + env "d" * t ^ j) := by
      simp [rubi1134r14Nondeg, eval, hkm, hkn, hkp]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1134r14Nondeg.result) =
        fun w => env "c" * (env "e" * w) ^ (k + 1) * (env "a" + env "b" * w ^ j) ^ (q + 1) *
          (env "a" * env "e" * (env "m" + 1))⁻¹ from funext hE]
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
    have hx1 : t ≠ 0 ∨ 0 ≤ j - 1 := by
      by_cases h : j < 0
      · exact Or.inl (ht.2.1 h)
      · exact Or.inr (by omega)
    have hu : env "a" + env "b" * t ^ j ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2.2 (by omega))
      · exact Or.inr (by omega)
    have hu0 : env "a" + env "b" * t ^ j ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2.2 h)
      · exact Or.inr (by omega)
    have htj : t ^ j = t ^ (j - 1) * t := by
      rw [← zpow_succ_of _ _ hx1, sub_add_cancel]
    have hin : HasDerivAt (fun w => env "a" + env "b" * w ^ j)
        (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "b")).const_add (env "a")
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hct)
      ((hasDerivAt_id' t).const_mul (env "e"))).const_mul (env "c")).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (q + 1) _ hu) hin)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hct0, zpow_succ_of _ _ hu0]
    generalize (env "e" * t) ^ k = C
    generalize (env "a" + env "b" * t ^ j) ^ q = V
    rw [htj]
    generalize t ^ (j - 1) = T
    rw [hm] at hae ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hae]
    linear_combination (-(C * V * env "e" * T * t)) * heq

theorem rubi1134r14Nondeg_real : rubi1134r14Nondeg.Holds .real :=
  rubi1134r14Nondeg_holds Interp.real

theorem rubi1134r14Nondeg_complex : rubi1134r14Nondeg.Holds .complex :=
  rubi1134r14Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec39
