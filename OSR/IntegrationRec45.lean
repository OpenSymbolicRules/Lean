import OSR.IntegrationRec44

/-!
# Integration (RUBI): corrected variants, ninth batch

Strengthened variants (Specification V1-R-005e) of the refuted RUBI rules
1.1.1.3 #9 and 1.2.1.3 #25, with non-degeneracy conditions appended to the
converted conditions (two for 1.2.1.3 #25: `c (m + 2 p + 2) ≠ 0` and
`e ≠ 0`).  Proved over ℝ and ℂ; the refutations of the rules as stated are
kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec45

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.1.1.3 #9 when d^2 f^2 (n + p + 2) (n + p + 3) ≠ 0 -/
def rubi1113r9Nondeg : CRule where
  id := "integration.rubi_1_1_1_3_r9_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:9"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 2)))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.var "x")))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 2))) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2)) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3)) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "e")) (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1))))))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1))))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 4))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 2)))))))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 2))) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.int 0)]
  priority := 7240
  description := "RUBI 1.1.1.3 #9 when d^2 f^2 (n + p + 2) (n + p + 3) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:9" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#9"

/-- RUBI 1.2.1.3 #25 when c (m + 2 p + 2) ≠ 0 and e ≠ 0 -/
def rubi1213r25Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r25_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:25"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int (-1))))
  independent := ["a", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.var "e") (.var "f")))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "f")) (.app2 .add (.var "p") (.int 1)))) (.int 0),
    .ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int 0),
    .ne (.var "e") (.int 0)]
  priority := 7250
  description := "RUBI 1.2.1.3 #25 when c (m + 2 p + 2) ≠ 0 and e ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:25" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#25"

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





/-- **1.1.1.3 #9** with `d² f² (n + p + 2) (n + p + 3) ≠ 0`. -/
theorem rubi1113r9Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1113r9Nondeg.conditions rubi1113r9Nondeg.body rubi1113r9Nondeg.result := by
  intro env hc t hF
  have hW : (env "d" ^ 2 * env "f" ^ 2 * (env "n" + env "p" + 2) * (env "n" + env "p" + 3)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 2))) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.int 0)) (by simp [rubi1113r9Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have h1 : env "d" * env "f" * (env "n" + env "p" + 2) * (env "a" ^ 2 * env "d" * env "f" * (env "n" + env "p" + 3) + -1 * env "b" * (env "b" * env "c" * env "e" + env "a" * (env "d" * env "e" * (env "n" + 1) + env "c" * env "f" * (env "p" + 1)))) + -1 * env "b" * (env "d" * env "e" * (env "n" + 1) + env "c" * env "f" * (env "p" + 1)) * (env "a" * env "d" * env "f" * (env "n" + env "p" + 4) + -1 * env "b" * (env "d" * env "e" * (env "n" + 2) + env "c" * env "f" * (env "p" + 2))) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "e")) (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1))))))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1))))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 4))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 2)))))))) (.int 0)) (by simp [rubi1113r9Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1113r9Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1113r9Nondeg, Defined, eval, hkp] at h
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkn1 : I.toInt? (env "n" + 1) = some (j + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1113r9Nondeg.body →
      (j < 0 → (env "c" + env "d" * w) ≠ 0) ∧ (q < 0 → (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi1113r9Nondeg, Defined, eval, hkn, hkp, toInt?_two] at h
    tauto
  have hDG : ∀ w, (j < 0 → (env "c" + env "d" * w) ≠ 0) → (q < 0 → (env "e" + env "f" * w) ≠ 0) →
      Defined I (Function.update env "x" w) rubi1113r9Nondeg.result := by
    intro w h1 h2
    have hW' := hW
    simp only [mul_ne_zero_iff] at hW'
    simp [rubi1113r9Nondeg, Defined, eval, hkn1, hkp1, toInt?_neg_one, toInt?_two]
    exact ⟨⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩,
      ⟨⟨fun h0 => hW'.1.1.1 (by rw [h0]; ring), fun h0 => hW'.1.1.2 (by rw [h0]; ring)⟩,
        hW'.1.2⟩, hW'.2⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1113r9Nondeg.result =
        env "b" * (env "c" + env "d" * w) ^ (j + 1) * (env "e" + env "f" * w) ^ (q + 1) * ((2 * env "a" * env "d" * env "f" * (env "n" + env "p" + 3) + -1 * env "b" * (env "d" * env "e" * (env "n" + 2) + env "c" * env "f" * (env "p" + 2))) + (env "b" * env "d" * env "f" * (env "n" + env "p" + 2)) * w) * (env "d" ^ 2 * env "f" ^ 2 * (env "n" + env "p" + 2) * (env "n" + env "p" + 3))⁻¹ := by
      intro w
      simp [rubi1113r9Nondeg, eval, hkn1, hkp1, toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1113r9Nondeg.body =
        (env "a" + env "b" * t) ^ 2 * (env "c" + env "d" * t) ^ j * (env "e" + env "f" * t) ^ q := by
      simp [rubi1113r9Nondeg, eval, hkn, hkp, toInt?_two]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1113r9Nondeg.result) =
        fun w => env "b" * (env "c" + env "d" * w) ^ (j + 1) * (env "e" + env "f" * w) ^ (q + 1) * ((2 * env "a" * env "d" * env "f" * (env "n" + env "p" + 3) + -1 * env "b" * (env "d" * env "e" * (env "n" + 2) + env "c" * env "f" * (env "p" + 2))) + (env "b" * env "d" * env "f" * (env "n" + env "p" + 2)) * w) * (env "d" ^ 2 * env "f" ^ 2 * (env "n" + env "p" + 2) * (env "n" + env "p" + 3))⁻¹ from funext hE]
    have hC : (env "c" + env "d" * t) ≠ 0 ∨ 0 ≤ j + 1 := by
      by_cases h : j + 1 < 0
      · exact Or.inl (ht.1 (by omega))
      · exact Or.inr (by omega)
    have hC0 : (env "c" + env "d" * t) ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hE1 : (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hE0 : (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    refine (((((HasDerivAt.comp t (hasDerivAt_zpow (j + 1) _ hC)
      (((hasDerivAt_id' t).const_mul (env "d")).const_add (env "c"))).const_mul (env "b")).mul
        (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hE1)
          (((hasDerivAt_id' t).const_mul (env "f")).const_add (env "e")))).mul
        (((hasDerivAt_id' t).const_mul (env "b" * env "d" * env "f" * (env "n" + env "p" + 2))).const_add (2 * env "a" * env "d" * env "f" * (env "n" + env "p" + 3) + -1 * env "b" * (env "d" * env "e" * (env "n" + 2) + env "c" * env "f" * (env "p" + 2))))).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply]
    rw [zpow_succ_of _ _ hC0, zpow_succ_of _ _ hE0]
    generalize (env "c" + env "d" * t) ^ j = X
    generalize (env "e" + env "f" * t) ^ q = Y
    simp only [hn, hp] at h1 hW ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hW]
    linear_combination (-(X * Y)) * h1

theorem rubi1113r9Nondeg_real : rubi1113r9Nondeg.Holds .real :=
  rubi1113r9Nondeg_holds Interp.real

theorem rubi1113r9Nondeg_complex : rubi1113r9Nondeg.Holds .complex :=
  rubi1113r9Nondeg_holds Interp.complex

/-- **1.2.1.3 #25** with `c (m + 2 p + 2) ≠ 0` and `e ≠ 0`. -/
theorem rubi1213r25Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1213r25Nondeg.conditions rubi1213r25Nondeg.body rubi1213r25Nondeg.result := by
  intro env hc t hF
  have hW : (env "c" * (env "m" + 2 * env "p" + 2)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int 0)) (by simp [rubi1213r25Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have he : env "e" ≠ 0 := by
    have h := hc (.ne (.var "e") (.int 0)) (by simp [rubi1213r25Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1213r25Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have h2 : env "m" * (env "d" * env "g" + env "e" * env "f") + 2 * env "e" * env "f" * (env "p" + 1) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.var "e") (.var "f")))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "f")) (.app2 .add (.var "p") (.int 1)))) (.int 0)) (by simp [rubi1213r25Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r25Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r25Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1213r25Nondeg.body →
      (k < 0 → (env "d" + env "e" * w) ≠ 0) ∧ (q < 0 → (env "a" + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1213r25Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have hDG : ∀ w, (k < 0 → (env "d" + env "e" * w) ≠ 0) → (q < 0 → (env "a" + env "c" * w ^ 2) ≠ 0) →
      Defined I (Function.update env "x" w) rubi1213r25Nondeg.result := by
    intro w h1 h2
    have hW' := hW
    simp only [mul_ne_zero_iff] at hW'
    simp [rubi1213r25Nondeg, Defined, eval, hkm, hkp1, toInt?_neg_one, toInt?_two]
    exact ⟨⟨h1, fun h => h2 (by omega)⟩, hW'.1, hW'.2⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1213r25Nondeg.result =
        env "g" * (env "d" + env "e" * w) ^ k * (env "a" + env "c" * w ^ 2) ^ (q + 1) * (env "c" * (env "m" + 2 * env "p" + 2))⁻¹ := by
      intro w
      simp [rubi1213r25Nondeg, eval, hkm, hkp1, toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1213r25Nondeg.body =
        (env "d" + env "e" * t) ^ k * (env "f" + env "g" * t) * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1213r25Nondeg, eval, hkm, hkp, toInt?_two]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1213r25Nondeg.result) =
        fun w => env "g" * (env "d" + env "e" * w) ^ k * (env "a" + env "c" * w ^ 2) ^ (q + 1) * (env "c" * (env "m" + 2 * env "p" + 2))⁻¹ from funext hE]
    have hA : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hB : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hB0 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
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
    have hQ : HasDerivAt (fun w => env "a" + env "c" * w ^ 2) (env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).pow 2).const_mul (env "c")).const_add (env "a")
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow k _ hA)
      (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))).const_mul (env "g")).mul
        (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hB) hQ)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, Pi.mul_apply,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [zpow_succ_of _ _ hB0]
    generalize (env "a" + env "c" * t ^ 2) ^ q = Y
    generalize (env "d" + env "e" * t) ^ (k - 1) = Z at key ⊢
    generalize (env "d" + env "e" * t) ^ k = X at key ⊢
    simp only [hm, hp] at h2 hW ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hW]
    refine mul_left_cancel₀ (pow_ne_zero 2 he) ?_
    linear_combination (env "g" * env "e" * Y * env "c" * (env "e" * t - env "d")) * key +
      (env "g" * (k : 𝕜) * env "e" * Y * Z) * h1 - (env "c" * env "e" * X * Y) * h2

theorem rubi1213r25Nondeg_real : rubi1213r25Nondeg.Holds .real :=
  rubi1213r25Nondeg_holds Interp.real

theorem rubi1213r25Nondeg_complex : rubi1213r25Nondeg.Holds .complex :=
  rubi1213r25Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec45
