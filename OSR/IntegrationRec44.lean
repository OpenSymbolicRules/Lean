import OSR.IntegrationRec43

/-!
# Integration (RUBI): corrected variants, eighth batch

Strengthened variants (Specification V1-R-005e) of the refuted RUBI rules
1.2.1.3 #13 and 1.1.1.7 #6, with a non-degeneracy condition appended to the
converted conditions.  Proved over ℝ and ℂ; the refutations of the rules as
stated are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec44

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.1.3 #13 when 2 c^2 (p + 1) (2 p + 3) ≠ 0 -/
def rubi1213r13Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r13_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:13"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "g")) (.app2 .add (.var "p") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g")))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "e")) (.var "g")) (.app2 .add (.var "p") (.int 1))) (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "g", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.var "p") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c")) (.var "e")) (.var "g"))) (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g")))))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))) (.int 0),
    .ne (.var "p") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 0)]
  priority := 7220
  description := "RUBI 1.2.1.3 #13 when 2 c^2 (p + 1) (2 p + 3) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:13" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#13"

/-- RUBI 1.1.1.7 #6 when 2 b1 b2 n (p + 1) ≠ 0 -/
def rubi1117r6Nondeg : CRule where
  id := "integration.rubi_1_1_1_7_r6_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:6"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b1")) (.var "b2")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a1", "b1", "a2", "b2", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)) (.int 0),
    .ne (.var "p") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b1")) (.var "b2")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 7230
  description := "RUBI 1.1.1.7 #6 when 2 b1 b2 n (p + 1) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:6" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#6"

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




/-- **1.2.1.3 #13** with `2 c² (p + 1) (2 p + 3) ≠ 0`. -/
theorem rubi1213r13Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1213r13Nondeg.conditions rubi1213r13Nondeg.body rubi1213r13Nondeg.result := by
  intro env hc t hF
  have hW : (2 * env "c" ^ 2 * (env "p" + 1) * (2 * env "p" + 3)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 0)) (by simp [rubi1213r13Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  have h1 : env "b" ^ 2 * env "e" * env "g" * (env "p" + 2) + -1 * 2 * env "a" * env "c" * env "e" * env "g" +
      env "c" * (2 * env "c" * env "d" * env "f" + -1 * env "b" * (env "e" * env "f" + env "d" * env "g")) *
        (2 * env "p" + 3) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.var "p") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c")) (.var "e")) (.var "g"))) (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g")))))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))) (.int 0)) (by simp [rubi1213r13Nondeg])
    simpa [Cond.Holds, Defined, eval, toInt?_two] using h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r13Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1213r13Nondeg.body ↔ (q < 0 → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0) := by
    intro w
    simp [rubi1213r13Nondeg, Defined, eval, hkp, toInt?_two]
  have hDG : ∀ w, (q < 0 → (env "a" + env "b" * w + env "c" * w ^ 2) ≠ 0) → Defined I (Function.update env "x" w) rubi1213r13Nondeg.result := by
    intro w h
    have hW' := hW
    simp only [mul_ne_zero_iff, pow_ne_zero_iff, ne_eq] at hW'
    simp [rubi1213r13Nondeg, Defined, eval, hkp1, toInt?_neg_one, toInt?_two]
    exact ⟨fun h' => h (by omega), ⟨⟨hW'.1.1.1, fun hc0 => hW'.1.1.2 (by rw [hc0]; ring)⟩,
      hW'.1.2⟩, hW'.2⟩
  have ht := (hD t).1 hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w ((hD w).1 hw)
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1213r13Nondeg.result =
        -1 * ((env "b" * env "e" * env "g" * (env "p" + 2) + -1 * env "c" * (env "e" * env "f" + env "d" * env "g") * (2 * env "p" + 3)) + (-1 * 2 * env "c" * env "e" * env "g" * (env "p" + 1)) * w) * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) * (2 * env "c" ^ 2 * (env "p" + 1) * (2 * env "p" + 3))⁻¹ := by
      intro w
      simp [rubi1213r13Nondeg, eval, hkp1, toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1213r13Nondeg.body =
        (env "d" + env "e" * t) * (env "f" + env "g" * t) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1213r13Nondeg, eval, hkp, toInt?_two]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1213r13Nondeg.result) =
        fun w => -1 * ((env "b" * env "e" * env "g" * (env "p" + 2) + -1 * env "c" * (env "e" * env "f" + env "d" * env "g") * (2 * env "p" + 3)) + (-1 * 2 * env "c" * env "e" * env "g" * (env "p" + 1)) * w) * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) * (2 * env "c" ^ 2 * (env "p" + 1) * (2 * env "p" + 3))⁻¹ from funext hE]
    have hu : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hu0 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht h)
      · exact Or.inr (by omega)
    have hQ : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2)
        (env "b" * 1 + env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
        (((hasDerivAt_id' t).pow 2).const_mul (env "c"))
    refine (((((hasDerivAt_id' t).const_mul (-1 * 2 * env "c" * env "e" * env "g" * (env "p" + 1))).const_add (env "b" * env "e" * env "g" * (env "p" + 2) + -1 * env "c" * (env "e" * env "f" + env "d" * env "g") * (2 * env "p" + 3))).const_mul (-1)).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hu) hQ)).mul_const _ |>.congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [zpow_succ_of _ _ hu0]
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = Y
    simp only [hp] at h1 hW ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hW]
    linear_combination (-(Y * ((q : 𝕜) + 1))) * h1

theorem rubi1213r13Nondeg_real : rubi1213r13Nondeg.Holds .real :=
  rubi1213r13Nondeg_holds Interp.real

theorem rubi1213r13Nondeg_complex : rubi1213r13Nondeg.Holds .complex :=
  rubi1213r13Nondeg_holds Interp.complex

/-- **1.1.1.7 #6** with `2 b1 b2 n (p + 1) ≠ 0`. -/
theorem rubi1117r6Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1117r6Nondeg.conditions rubi1117r6Nondeg.body rubi1117r6Nondeg.result := by
  intro env hc t hF
  have hW : (2 * env "b1" * env "b2" * env "n" * (env "p" + 1)) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b1")) (.var "b2")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1117r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h1 : env "a2" * env "b1" + env "a1" * env "b2" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0)) (by simp [rubi1117r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have h2 : env "m" + -1 * 2 * env "n" + 1 = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)) (.int 0)) (by simp [rubi1117r6Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkn : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1117r6Nondeg, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1117r6Nondeg, Defined, eval, hkp] at h
  have hn : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkm : I.toInt? (env "m") = some (2 * j - 1) :=
    (I.toInt?_eq _ _).2 (by rw [show env "m" = 2 * env "n" - 1 by linear_combination h2, hn]; push_cast; ring)
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1117r6Nondeg.body →
      (2 * j - 1 < 0 → w ≠ 0) ∧ (q < 0 → (env "a1" + env "b1" * w ^ j) ≠ 0) ∧ (q < 0 → (env "a2" + env "b2" * w ^ j) ≠ 0) := by
    intro w h
    simp [rubi1117r6Nondeg, Defined, eval, hkm, hkn, hkp] at h
    exact ⟨fun hj => h.1.1 (by omega), h.1.2.2, h.2.2⟩
  have hDG : ∀ w, (2 * j - 1 < 0 → w ≠ 0) → (q < 0 → (env "a1" + env "b1" * w ^ j) ≠ 0) → (q < 0 → (env "a2" + env "b2" * w ^ j) ≠ 0) →
      Defined I (Function.update env "x" w) rubi1117r6Nondeg.result := by
    intro w h1 h2 h3
    simp [rubi1117r6Nondeg, Defined, eval, hkn, hkp1, toInt?_neg_one, hW]
    exact ⟨⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩, fun h => h1 (by omega),
      fun h => h3 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2.1 (hD w hw).2.2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1117r6Nondeg.result =
        (env "a1" + env "b1" * w ^ j) ^ (q + 1) * (env "a2" + env "b2" * w ^ j) ^ (q + 1) * (2 * env "b1" * env "b2" * env "n" * (env "p" + 1))⁻¹ := by
      intro w
      simp [rubi1117r6Nondeg, eval, hkn, hkp1, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1117r6Nondeg.body =
        t ^ (2 * j - 1) * (env "a1" + env "b1" * t ^ j) ^ q * (env "a2" + env "b2" * t ^ j) ^ q := by
      simp [rubi1117r6Nondeg, eval, hkm, hkn, hkp]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1117r6Nondeg.result) =
        fun w => (env "a1" + env "b1" * w ^ j) ^ (q + 1) * (env "a2" + env "b2" * w ^ j) ^ (q + 1) * (2 * env "b1" * env "b2" * env "n" * (env "p" + 1))⁻¹ from funext hE]
    have hx : t ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · exact Or.inl (ht.1 (by omega))
      · exact Or.inr (by omega)
    have hu1 : (env "a1" + env "b1" * t ^ j) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2.1 (by omega))
      · exact Or.inr (by omega)
    have hu10 : (env "a1" + env "b1" * t ^ j) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2.1 h)
      · exact Or.inr (by omega)
    have hu2 : (env "a2" + env "b2" * t ^ j) ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2.2 (by omega))
      · exact Or.inr (by omega)
    have hu20 : (env "a2" + env "b2" * t ^ j) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2.2 h)
      · exact Or.inr (by omega)
    have key : t ^ (j - 1) * t ^ j = t ^ (2 * j - 1) := by
      rw [← zpow_add' (Or.inr (Or.inl (by omega)))]
      congr 1
      ring
    have hin1 : HasDerivAt (fun w => env "a1" + env "b1" * w ^ j)
        (env "b1" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "b1")).const_add (env "a1")
    have hin2 : HasDerivAt (fun w => env "a2" + env "b2" * w ^ j)
        (env "b2" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t hx).const_mul (env "b2")).const_add (env "a2")
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hu1) hin1).mul
      (HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hu2) hin2)).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hu10, zpow_succ_of _ _ hu20]
    generalize (env "a1" + env "b1" * t ^ j) ^ q = X1
    generalize (env "a2" + env "b2" * t ^ j) ^ q = X2
    generalize t ^ (j - 1) = R at key ⊢
    generalize t ^ (2 * j - 1) = M at key ⊢
    generalize t ^ j = T at key ⊢
    simp only [hn, hp] at hW ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hW]
    linear_combination (((q : 𝕜) + 1) * j * X1 * X2 * R) * h1 +
      (((q : 𝕜) + 1) * j * X1 * X2 * 2 * env "b1" * env "b2") * key

theorem rubi1117r6Nondeg_real : rubi1117r6Nondeg.Holds .real :=
  rubi1117r6Nondeg_holds Interp.real

theorem rubi1117r6Nondeg_complex : rubi1117r6Nondeg.Holds .complex :=
  rubi1117r6Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec44
