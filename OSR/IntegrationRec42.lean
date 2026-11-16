import OSR.IntegrationRec41

/-!
# Integration (RUBI): corrected variants, sixth batch

Strengthened variants (Specification V1-R-005e) of the refuted RUBI rules
1.2.1.2 #55, 4.1.12 #81 and #82, 1.2.1.4 #65 and #66, with a non-degeneracy
condition appended to the converted conditions.  Proved over ℝ and ℂ; the refutations of the rules as
stated are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec42

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.1.2 #55 when e (p + 1) (b^2 - 4 a c) ≠ 0 -/
def rubi1212r55Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r55_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:55"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .ne (.var "p") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)]
  priority := 7150
  description := "RUBI 1.2.1.2 #55 when e (p + 1) (b^2 - 4 a c) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:55" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#55"

/-- RUBI 4.1.12 #81 when b n (p + 1) ≠ 0 -/
def rubi4112r81Nondeg : CRule where
  id := "integration.rubi_4_1_12_r81_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:81"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .mul (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 7160
  description := "RUBI 4.1.12 #81 when b n (p + 1) ≠ 0"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:81" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#81"

/-- RUBI 4.1.12 #82 when b n (p + 1) ≠ 0 -/
def rubi4112r82Nondeg : CRule where
  id := "integration.rubi_4_1_12_r82_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:82"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 7170
  description := "RUBI 4.1.12 #82 when b n (p + 1) ≠ 0"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:82" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#82"

/-- RUBI 1.2.1.4 #65 when c e (m + 2 p + 3) ≠ 0 -/
def rubi1214r65Nondeg : CRule where
  id := "integration.rubi_1_2_1_4_r65_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:65"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "p") (.int 1))) (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1)))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.int 0)]
  priority := 7180
  description := "RUBI 1.2.1.4 #65 when c e (m + 2 p + 3) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:65" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p.m#65"

/-- RUBI 1.2.1.4 #66 when c e (m + 2 p + 3) ≠ 0 -/
def rubi1214r66Nondeg : CRule where
  id := "integration.rubi_1_2_1_4_r66_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:66"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.int (-1))))
  independent := ["a", "c", "d", "e", "m", "p"]
  conditions := [.eq (.app2 .mul (.var "d") (.app2 .add (.var "p") (.int 1))) (.int 0),
    .eq (.app2 .mul (.var "a") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.int 0)]
  priority := 7190
  description := "RUBI 1.2.1.4 #66 when c e (m + 2 p + 3) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:66" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p.m#66"


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


/-- **1.2.1.2 #55** with `e (p + 1) (b² - 4 a c) ≠ 0`. -/
theorem rubi1212r55Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1212r55Nondeg.conditions rubi1212r55Nondeg.body
      rubi1212r55Nondeg.result := by
  intro env hc t hF
  have hW : env "e" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c") ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)) (by simp [rubi1212r55Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have h1 : 2 * env "c" * env "d" + -1 * env "b" * env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi1212r55Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h2 : env "m" + 2 * env "p" + 3 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)) (by simp [rubi1212r55Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r55Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r55Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r55Nondeg.body →
      (k < 0 → env "d" + env "e" * w ≠ 0) ∧
        (q < 0 → env "a" + env "b" * w + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1212r55Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have hDG : ∀ w, (k < 0 → env "d" + env "e" * w ≠ 0) →
      (q < 0 → env "a" + env "b" * w + env "c" * w ^ 2 ≠ 0) →
      Defined I (Function.update env "x" w) rubi1212r55Nondeg.result := by
    intro w h1 h2
    simp [rubi1212r55Nondeg, Defined, eval, hkm1, hkp1, toInt?_neg_one, toInt?_two, hW]
    have hW' := hW
    simp only [mul_ne_zero_iff] at hW'
    refine ⟨⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩, hW'.1, fun h => hW'.2 ?_⟩
    linear_combination h
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1212r55Nondeg.result =
        2 * env "c" * ((env "d" + env "e" * w) ^ (k + 1) *
          (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1)) *
          (env "e" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹ := by
      intro w
      simp [rubi1212r55Nondeg, eval, hkm1, hkp1, toInt?_neg_one, toInt?_two, mul_assoc]
    have hEF : eval I (Function.update env "x" t) rubi1212r55Nondeg.body =
        (env "d" + env "e" * t) ^ k * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r55Nondeg, eval, hkm, hkp, toInt?_two]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1212r55Nondeg.result) =
        fun w => 2 * env "c" * ((env "d" + env "e" * w) ^ (k + 1) *
          (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1)) *
          (env "e" * (env "p" + 1) * (env "b" ^ 2 + -1 * 4 * env "a" * env "c"))⁻¹ from funext hE]
    have hA : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (ht.1 (by omega))
      · exact Or.inr (by omega)
    have hA0 : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ k := by
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
    have hQ : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2)
        (env "b" * 1 + env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
        (((hasDerivAt_id' t).pow 2).const_mul (env "c"))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hA)
      (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (q + 1) _ hB) hQ)).const_mul (2 * env "c")).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [zpow_succ_of _ _ hA0, zpow_succ_of _ _ hB0]
    generalize (env "d" + env "e" * t) ^ k = X
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = Y
    simp only [hm, hp] at h2 hW ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hW]
    linear_combination (X * Y) * ((2 * env "c" * env "e" * (env "a" + env "b" * t + env "c" * t ^ 2)) * h2 +
      (((q : 𝕜) + 1) * (env "b" + 2 * env "c" * t)) * h1)

theorem rubi1212r55Nondeg_real : rubi1212r55Nondeg.Holds .real :=
  rubi1212r55Nondeg_holds Interp.real

theorem rubi1212r55Nondeg_complex : rubi1212r55Nondeg.Holds .complex :=
  rubi1212r55Nondeg_holds Interp.complex

/-- **4.1.12 #81** with `b n (p + 1) ≠ 0`. -/
theorem rubi4112r81Nondeg_holds (I : Interp 𝕜) (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) :
    AntiderivHoldsUnder I "x" rubi4112r81Nondeg.conditions rubi4112r81Nondeg.body rubi4112r81Nondeg.result := by
  intro env hc t hF
  have hbn : env "b" * env "n" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi4112r81Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hmn : env "m" = env "n" + -1 * 1 := by
    have h := hc (.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi4112r81Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r81Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r81Nondeg, Defined, eval, hkp] at h
  have hmk : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hpq : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkn : I.toInt? (env "n") = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [show env "n" = env "m" + 1 by rw [hmn]; ring, hmk]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hpq]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi4112r81Nondeg.body →
      (k < 0 → w ≠ 0) ∧ (q < 0 → I.sin (env "a" + env "b" * w ^ (k + 1)) ≠ 0) := by
    intro w h
    simp [rubi4112r81Nondeg, Defined, eval, hkm, hkp, hkn] at h
    tauto
  have hDG : ∀ w, (k < 0 → w ≠ 0) → (q < 0 → I.sin (env "a" + env "b" * w ^ (k + 1)) ≠ 0) →
      Defined I (Function.update env "x" w) rubi4112r81Nondeg.result := by
    intro w h1 h2
    simp [rubi4112r81Nondeg, Defined, eval, hkn, hkp1, toInt?_neg_one, hbn]
    exact ⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi4112r81Nondeg.result =
        I.sin (env "a" + env "b" * w ^ (k + 1)) ^ (q + 1) * (env "b" * env "n" * (env "p" + 1))⁻¹ := by
      intro w
      simp [rubi4112r81Nondeg, eval, hkn, hkp1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi4112r81Nondeg.body =
        t ^ k * I.sin (env "a" + env "b" * t ^ (k + 1)) ^ q * I.cos (env "a" + env "b" * t ^ (k + 1)) := by
      simp [rubi4112r81Nondeg, eval, hkm, hkp, hkn]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi4112r81Nondeg.result) =
        fun w => I.sin (env "a" + env "b" * w ^ (k + 1)) ^ (q + 1) * (env "b" * env "n" * (env "p" + 1))⁻¹ from funext hE]
    have hx : t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (ht.1 (by omega))
      · exact Or.inr (by omega)
    have hu : I.sin (env "a" + env "b" * t ^ (k + 1)) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hin : HasDerivAt (fun w => env "a" + env "b" * w ^ (k + 1))
        (env "b" * (((k + 1 : ℤ) : 𝕜) * t ^ (k + 1 - 1))) t :=
      ((hasDerivAt_zpow (k + 1) t hx).const_mul (env "b")).const_add (env "a")
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hu)
      (HasDerivAt.comp t (hs _) hin))).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hn : env "n" = (k : 𝕜) + 1 := by
      rw [show env "n" = env "m" + 1 by rw [hmn]; ring, hmk]
    rw [hn, hpq] at hbn ⊢
    generalize t ^ k = X
    generalize I.sin (env "a" + env "b" * t ^ (k + 1)) ^ q = V
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hbn]
    ring

theorem rubi4112r81Nondeg_real : rubi4112r81Nondeg.Holds .real :=
  rubi4112r81Nondeg_holds Interp.real Real.hasDerivAt_sin

theorem rubi4112r81Nondeg_complex : rubi4112r81Nondeg.Holds .complex :=
  rubi4112r81Nondeg_holds Interp.complex Complex.hasDerivAt_sin

/-- **4.1.12 #82** with `b n (p + 1) ≠ 0`. -/
theorem rubi4112r82Nondeg_holds (I : Interp 𝕜) (hcd : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivHoldsUnder I "x" rubi4112r82Nondeg.conditions rubi4112r82Nondeg.body rubi4112r82Nondeg.result := by
  intro env hc t hF
  have hbn : env "b" * env "n" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi4112r82Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hmn : env "m" = env "n" + -1 * 1 := by
    have h := hc (.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi4112r82Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r82Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi4112r82Nondeg, Defined, eval, hkp] at h
  have hmk : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hpq : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkn : I.toInt? (env "n") = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [show env "n" = env "m" + 1 by rw [hmn]; ring, hmk]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hpq]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi4112r82Nondeg.body →
      (k < 0 → w ≠ 0) ∧ (q < 0 → I.cos (env "a" + env "b" * w ^ (k + 1)) ≠ 0) := by
    intro w h
    simp [rubi4112r82Nondeg, Defined, eval, hkm, hkp, hkn] at h
    tauto
  have hDG : ∀ w, (k < 0 → w ≠ 0) → (q < 0 → I.cos (env "a" + env "b" * w ^ (k + 1)) ≠ 0) →
      Defined I (Function.update env "x" w) rubi4112r82Nondeg.result := by
    intro w h1 h2
    simp [rubi4112r82Nondeg, Defined, eval, hkn, hkp1, toInt?_neg_one, hbn]
    exact ⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi4112r82Nondeg.result =
        -1 * I.cos (env "a" + env "b" * w ^ (k + 1)) ^ (q + 1) * (env "b" * env "n" * (env "p" + 1))⁻¹ := by
      intro w
      simp [rubi4112r82Nondeg, eval, hkn, hkp1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi4112r82Nondeg.body =
        t ^ k * I.cos (env "a" + env "b" * t ^ (k + 1)) ^ q * I.sin (env "a" + env "b" * t ^ (k + 1)) := by
      simp [rubi4112r82Nondeg, eval, hkm, hkp, hkn]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi4112r82Nondeg.result) =
        fun w => -1 * I.cos (env "a" + env "b" * w ^ (k + 1)) ^ (q + 1) * (env "b" * env "n" * (env "p" + 1))⁻¹ from funext hE]
    have hx : t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (ht.1 (by omega))
      · exact Or.inr (by omega)
    have hu : I.cos (env "a" + env "b" * t ^ (k + 1)) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hin : HasDerivAt (fun w => env "a" + env "b" * w ^ (k + 1))
        (env "b" * (((k + 1 : ℤ) : 𝕜) * t ^ (k + 1 - 1))) t :=
      ((hasDerivAt_zpow (k + 1) t hx).const_mul (env "b")).const_add (env "a")
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hu)
      (HasDerivAt.comp t (hcd _) hin)).const_mul (-1)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have hn : env "n" = (k : 𝕜) + 1 := by
      rw [show env "n" = env "m" + 1 by rw [hmn]; ring, hmk]
    rw [hn, hpq] at hbn ⊢
    generalize t ^ k = X
    generalize I.cos (env "a" + env "b" * t ^ (k + 1)) ^ q = V
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hbn]
    ring

theorem rubi4112r82Nondeg_real : rubi4112r82Nondeg.Holds .real :=
  rubi4112r82Nondeg_holds Interp.real Real.hasDerivAt_cos

theorem rubi4112r82Nondeg_complex : rubi4112r82Nondeg.Holds .complex :=
  rubi4112r82Nondeg_holds Interp.complex Complex.hasDerivAt_cos

/-- **1.2.1.4 #65** with `c e (m + 2 p + 3) ≠ 0`. -/
theorem rubi1214r65Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1214r65Nondeg.conditions rubi1214r65Nondeg.body rubi1214r65Nondeg.result := by
  intro env hc t hF
  have hW : env "c" * env "e" * (env "m" + 2 * env "p" + 3) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.int 0)) (by simp [rubi1214r65Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1)))) (.int 0)) (by simp [rubi1214r65Nondeg])
  have h2 := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "p") (.int 1))) (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1)))) (.int 0)) (by simp [rubi1214r65Nondeg])
  replace h1 : env "b" * env "e" * (env "m" + env "p" + 2) + 2 * env "c" * env "d" * (env "p" + 1) = 0 := by simpa [Cond.Holds, Defined, eval] using h1
  replace h2 : env "b" * env "d" * (env "p" + 1) + env "a" * env "e" * (env "m" + 1) = 0 := by simpa [Cond.Holds, Defined, eval] using h2
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1214r65Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1214r65Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1214r65Nondeg.body →
      (k < 0 → env "d" + env "e" * w ≠ 0) ∧ (q < 0 → env "a" + env "b" * w + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1214r65Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have hDG : ∀ w, (k < 0 → env "d" + env "e" * w ≠ 0) → (q < 0 → env "a" + env "b" * w + env "c" * w ^ 2 ≠ 0) →
      Defined I (Function.update env "x" w) rubi1214r65Nondeg.result := by
    intro w h1 h2
    have hW' := hW
    simp only [mul_ne_zero_iff] at hW'
    simp [rubi1214r65Nondeg, Defined, eval, hkm1, hkp1, toInt?_neg_one, toInt?_two]
    exact ⟨⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩, hW'.1, hW'.2⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1214r65Nondeg.result =
        (env "d" + env "e" * w) ^ (k + 1) * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) *
          (env "c" * env "e" * (env "m" + 2 * env "p" + 3))⁻¹ := by
      intro w
      simp [rubi1214r65Nondeg, eval, hkm1, hkp1, toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1214r65Nondeg.body =
        t ^ 2 * (env "d" + env "e" * t) ^ k * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1214r65Nondeg, eval, hkm, hkp, toInt?_two]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1214r65Nondeg.result) =
        fun w => (env "d" + env "e" * w) ^ (k + 1) * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) *
          (env "c" * env "e" * (env "m" + 2 * env "p" + 3))⁻¹ from funext hE]
    have hA : env "d" + env "e" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (ht.1 (by omega))
      · exact Or.inr (by omega)
    have hA0 : env "d" + env "e" * t ≠ 0 ∨ 0 ≤ k := by
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
    have hQ : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2)
        (env "b" * 1 + env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
        (((hasDerivAt_id' t).pow 2).const_mul (env "c"))
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hA)
      (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (q + 1) _ hB) hQ)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [zpow_succ_of _ _ hA0, zpow_succ_of _ _ hB0]
    generalize (env "d" + env "e" * t) ^ k = X
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = Y
    simp only [hm, hp] at h1 h2 hW ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hW]
    linear_combination (X * Y) * (t * h1 + h2)

theorem rubi1214r65Nondeg_real : rubi1214r65Nondeg.Holds .real :=
  rubi1214r65Nondeg_holds Interp.real

theorem rubi1214r65Nondeg_complex : rubi1214r65Nondeg.Holds .complex :=
  rubi1214r65Nondeg_holds Interp.complex

/-- **1.2.1.4 #66** with `c e (m + 2 p + 3) ≠ 0`. -/
theorem rubi1214r66Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1214r66Nondeg.conditions rubi1214r66Nondeg.body rubi1214r66Nondeg.result := by
  intro env hc t hF
  have hW : env "c" * env "e" * (env "m" + 2 * env "p" + 3) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.int 0)) (by simp [rubi1214r66Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 := hc (.eq (.app2 .mul (.var "d") (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1214r66Nondeg])
  have h2 := hc (.eq (.app2 .mul (.var "a") (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1214r66Nondeg])
  replace h1 : env "d" * (env "p" + 1) = 0 := by simpa [Cond.Holds, Defined, eval] using h1
  replace h2 : env "a" * (env "m" + 1) = 0 := by simpa [Cond.Holds, Defined, eval] using h2
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1214r66Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1214r66Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkm1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1214r66Nondeg.body →
      (k < 0 → env "d" + env "e" * w ≠ 0) ∧ (q < 0 → env "a" + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1214r66Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have hDG : ∀ w, (k < 0 → env "d" + env "e" * w ≠ 0) → (q < 0 → env "a" + env "c" * w ^ 2 ≠ 0) →
      Defined I (Function.update env "x" w) rubi1214r66Nondeg.result := by
    intro w h1 h2
    have hW' := hW
    simp only [mul_ne_zero_iff] at hW'
    simp [rubi1214r66Nondeg, Defined, eval, hkm1, hkp1, toInt?_neg_one, toInt?_two]
    exact ⟨⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩, hW'.1, hW'.2⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1214r66Nondeg.result =
        (env "d" + env "e" * w) ^ (k + 1) * (env "a" + env "c" * w ^ 2) ^ (q + 1) *
          (env "c" * env "e" * (env "m" + 2 * env "p" + 3))⁻¹ := by
      intro w
      simp [rubi1214r66Nondeg, eval, hkm1, hkp1, toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1214r66Nondeg.body =
        t ^ 2 * (env "d" + env "e" * t) ^ k * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1214r66Nondeg, eval, hkm, hkp, toInt?_two]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1214r66Nondeg.result) =
        fun w => (env "d" + env "e" * w) ^ (k + 1) * (env "a" + env "c" * w ^ 2) ^ (q + 1) *
          (env "c" * env "e" * (env "m" + 2 * env "p" + 3))⁻¹ from funext hE]
    have hA : env "d" + env "e" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (ht.1 (by omega))
      · exact Or.inr (by omega)
    have hA0 : env "d" + env "e" * t ≠ 0 ∨ 0 ≤ k := by
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
    have hQ : HasDerivAt (fun w => env "a" + env "c" * w ^ 2) (env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).pow 2).const_mul (env "c")).const_add (env "a")
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hA)
      (((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d"))).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (q + 1) _ hB) hQ)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [zpow_succ_of _ _ hA0, zpow_succ_of _ _ hB0]
    generalize (env "d" + env "e" * t) ^ k = X
    generalize (env "a" + env "c" * t ^ 2) ^ q = Y
    simp only [hm, hp] at h1 h2 hW ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hW]
    linear_combination (X * Y) * (env "e" * h2 + 2 * env "c" * t * h1)

theorem rubi1214r66Nondeg_real : rubi1214r66Nondeg.Holds .real :=
  rubi1214r66Nondeg_holds Interp.real

theorem rubi1214r66Nondeg_complex : rubi1214r66Nondeg.Holds .complex :=
  rubi1214r66Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec42
