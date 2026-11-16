import OSR.IntegrationRec39

/-!
# Integration (RUBI): corrected variants, fourth batch

Strengthened variants (Specification V1-R-005e) of refuted RUBI rules on
quadratic trinomials, with a non-degeneracy condition appended to the
converted conditions.  Proved over ℝ and ℂ; the refutations of the rules as
stated are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec40

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.1.2 #4 when b (p + 1) ≠ 0 -/
def rubi1212r4Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r4_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:4"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .ne (.var "p") (.int (-1)),
    .ne (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 7100
  description := "RUBI 1.2.1.2 #4 when b (p + 1) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:4" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#4"

/-- RUBI 1.2.1.3 #1 when c (m + 2 p + 2) ≠ 0 -/
def rubi1213r1Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r1_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "x")) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m"))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "x")) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int (-1))))
  independent := ["b", "c", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0),
    .ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int 0)]
  priority := 7110
  description := "RUBI 1.2.1.3 #1 when c (m + 2 p + 2) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:1" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#1"

/-- RUBI 1.2.1.4 #1 when g (m + n + 3) ≠ 0 -/
def rubi1214r1Nondeg : CRule where
  id := "integration.rubi_1_2_1_4_r1_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "n"))) (.app2 .add (.app2 .mul (.var "b") (.var "x")) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .add (.var "m") (.int 2)))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "g") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3))) (.int (-1))))
  independent := ["b", "c", "f", "g", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "m") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)) (.int 0),
    .ne (.app2 .mul (.var "g") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3))) (.int 0)]
  priority := 7120
  description := "RUBI 1.2.1.4 #1 when g (m + n + 3) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:1" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p.m#1"

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


/-- **1.2.1.2 #4** with `b (p + 1) ≠ 0`. -/
theorem rubi1212r4Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1212r4Nondeg.conditions rubi1212r4Nondeg.body
      rubi1212r4Nondeg.result := by
  intro env hc t hF
  have hbp : env "b" * (env "p" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : 2 * env "c" * env "d" + -1 * env "b" * env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [rubi1212r4Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1212r4Nondeg, Defined, eval, hkp] at h
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1212r4Nondeg.body ↔
      (q < 0 → env "a" + env "b" * w + env "c" * w ^ 2 ≠ 0) := by
    intro w
    simp [rubi1212r4Nondeg, Defined, eval, hkp, toInt?_two]
  have hDG : ∀ w, Defined I (Function.update env "x" w) rubi1212r4Nondeg.result ↔
      (q + 1 < 0 → env "a" + env "b" * w + env "c" * w ^ 2 ≠ 0) := by
    intro w
    simp [rubi1212r4Nondeg, Defined, eval, hkp1, toInt?_neg_one, toInt?_two, hbp]
  have hE : ∀ w, eval I (Function.update env "x" w) rubi1212r4Nondeg.result =
      env "d" * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) *
        (env "b" * (env "p" + 1))⁻¹ := by
    intro w
    simp [rubi1212r4Nondeg, eval, hkp1, toInt?_neg_one, toInt?_two]
  have hEF : eval I (Function.update env "x" t) rubi1212r4Nondeg.body =
      (env "d" + env "e" * t) * (env "a" + env "b" * t + env "c" * t ^ 2) ^ q := by
    simp [rubi1212r4Nondeg, eval, hkp, toInt?_two]
  have ht := (hD t).1 hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact (hDG w).2 fun h => (hD w).1 hw (by omega)
  · have hne : env "a" + env "b" * t + env "c" * t ^ 2 ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1212r4Nondeg.result) =
        fun w => env "d" * (env "a" + env "b" * w + env "c" * w ^ 2) ^ (q + 1) *
          (env "b" * (env "p" + 1))⁻¹ from funext hE]
    have hQ : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2)
        (env "b" * 1 + env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
        (((hasDerivAt_id' t).pow 2).const_mul (env "c"))
    refine (((HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hne) hQ).const_mul
      (env "d")).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [hp] at hbp ⊢
    generalize (env "a" + env "b" * t + env "c" * t ^ 2) ^ q = V
    have hb0 : env "b" ≠ 0 := left_ne_zero_of_mul hbp
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hbp]
    linear_combination (V * t * ((q : 𝕜) + 1)) * heq

theorem rubi1212r4Nondeg_real : rubi1212r4Nondeg.Holds .real :=
  rubi1212r4Nondeg_holds Interp.real

theorem rubi1212r4Nondeg_complex : rubi1212r4Nondeg.Holds .complex :=
  rubi1212r4Nondeg_holds Interp.complex

/-- **1.2.1.3 #1** with `c (m + 2 p + 2) ≠ 0`. -/
theorem rubi1213r1Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1213r1Nondeg.conditions rubi1213r1Nondeg.body
      rubi1213r1Nondeg.result := by
  intro env hc t hF
  have hcK : env "c" * (env "m" + 2 * env "p" + 2) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int 0)) (by simp [rubi1213r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : env "b" * env "g" * (env "m" + env "p" + 1) +
      -1 * env "c" * env "f" * (env "m" + 2 * env "p" + 2) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)))) (.int 0)) (by simp [rubi1213r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r1Nondeg, Defined, eval, hkm] at h
  rcases hkp : I.toInt? (env "p") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1213r1Nondeg, Defined, eval, hkp] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hp : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkp
  have hkp1 : I.toInt? (env "p" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hp]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1213r1Nondeg.body →
      (k < 0 → env "e" ≠ 0 ∧ w ≠ 0) ∧ (q < 0 → env "b" * w + env "c" * w ^ 2 ≠ 0) := by
    intro w h
    simp [rubi1213r1Nondeg, Defined, eval, hkm, hkp, toInt?_two] at h
    tauto
  have hDG : ∀ w, (k < 0 → env "e" ≠ 0 ∧ w ≠ 0) →
      (q < 0 → env "b" * w + env "c" * w ^ 2 ≠ 0) →
      Defined I (Function.update env "x" w) rubi1213r1Nondeg.result := by
    intro w h1 h2
    simp [rubi1213r1Nondeg, Defined, eval, hkm, hkp1, toInt?_neg_one, toInt?_two, hcK]
    exact ⟨h1, fun h => h2 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1213r1Nondeg.result =
        env "g" * ((env "e" * w) ^ k * (env "b" * w + env "c" * w ^ 2) ^ (q + 1)) *
          (env "c" * (env "m" + 2 * env "p" + 2))⁻¹ := by
      intro w
      simp [rubi1213r1Nondeg, eval, hkm, hkp1, toInt?_neg_one, toInt?_two, mul_assoc]
    have hEF : eval I (Function.update env "x" t) rubi1213r1Nondeg.body =
        (env "e" * t) ^ k * (env "f" + env "g" * t) * (env "b" * t + env "c" * t ^ 2) ^ q := by
      simp [rubi1213r1Nondeg, eval, hkm, hkp, toInt?_two]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1213r1Nondeg.result) =
        fun w => env "g" * ((env "e" * w) ^ k * (env "b" * w + env "c" * w ^ 2) ^ (q + 1)) *
          (env "c" * (env "m" + 2 * env "p" + 2))⁻¹ from funext hE]
    have hct : env "e" * t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (mul_ne_zero (ht.1 h).1 (ht.1 h).2)
      · exact Or.inr (by omega)
    have hu : env "b" * t + env "c" * t ^ 2 ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hu0 : env "b" * t + env "c" * t ^ 2 ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have key : ((k : ℤ) : 𝕜) * (env "e" * t) ^ (k - 1) * (env "e" * 1) *
        (env "b" * t + env "c" * t ^ 2) = (k : 𝕜) * (env "e" * t) ^ k * (env "b" + env "c" * t) := by
      rcases em (k = 0) with h0 | h0
      · subst h0
        simp
      · have hx1 : env "e" * t ≠ 0 ∨ 0 ≤ k - 1 := by
          by_cases h : k < 0
          · exact Or.inl (mul_ne_zero (ht.1 h).1 (ht.1 h).2)
          · exact Or.inr (by omega)
        rw [show (env "e" * t) ^ k = (env "e" * t) ^ (k - 1) * (env "e" * t) by
          rw [← zpow_succ_of _ _ hx1, sub_add_cancel]]
        ring
    have hQ : HasDerivAt (fun w => env "b" * w + env "c" * w ^ 2)
        (env "b" * 1 + env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      ((hasDerivAt_id' t).const_mul (env "b")).add (((hasDerivAt_id' t).pow 2).const_mul (env "c"))
    refine ((((HasDerivAt.comp t (hasDerivAt_zpow k _ hct)
      ((hasDerivAt_id' t).const_mul (env "e"))).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (q + 1) _ hu) hQ)).const_mul (env "g")).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [zpow_succ_of _ _ hu0]
    generalize (env "b" * t + env "c" * t ^ 2) ^ q = V at key ⊢
    generalize (env "e" * t) ^ (k - 1) = Pm at key ⊢
    generalize (env "e" * t) ^ k = C at key ⊢
    rw [hm, hp] at hcK heq ⊢
    push_cast at key ⊢
    rw [mul_inv_eq_iff_eq_mul₀ hcK]
    linear_combination (env "g" * V) * key + (C * V) * heq

theorem rubi1213r1Nondeg_real : rubi1213r1Nondeg.Holds .real :=
  rubi1213r1Nondeg_holds Interp.real

theorem rubi1213r1Nondeg_complex : rubi1213r1Nondeg.Holds .complex :=
  rubi1213r1Nondeg_holds Interp.complex

/-- **1.2.1.4 #1** with `g (m + n + 3) ≠ 0`. -/
theorem rubi1214r1Nondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" rubi1214r1Nondeg.conditions rubi1214r1Nondeg.body
      rubi1214r1Nondeg.result := by
  intro env hc t hF
  have hgK : env "g" * (env "m" + env "n" + 3) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "g") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3))) (.int 0)) (by simp [rubi1214r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : env "c" * env "f" * (env "m" + 2) +
      -1 * env "b" * env "g" * (env "m" + env "n" + 3) = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "m") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))) (.int 0)) (by simp [rubi1214r1Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1214r1Nondeg, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [rubi1214r1Nondeg, Defined, eval, hkn] at h
  have hm : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hkm
  have hn : env "n" = (q : 𝕜) := (I.toInt?_eq _ _).1 hkn
  have hkm2 : I.toInt? (env "m" + 2) = some (k + 2) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hkn1 : I.toInt? (env "n" + 1) = some (q + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) rubi1214r1Nondeg.body →
      (k < 0 → w ≠ 0) ∧ (q < 0 → env "f" + env "g" * w ≠ 0) := by
    intro w h
    simp [rubi1214r1Nondeg, Defined, eval, hkm, hkn, toInt?_two] at h
    tauto
  have hDG : ∀ w, (k < 0 → w ≠ 0) → (q < 0 → env "f" + env "g" * w ≠ 0) →
      Defined I (Function.update env "x" w) rubi1214r1Nondeg.result := by
    intro w h1 h2
    simp [rubi1214r1Nondeg, Defined, eval, hkm2, hkn1, toInt?_neg_one, hgK]
    exact ⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩
  have ht := hD t hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w (hD w hw).1 (hD w hw).2
  · have hE : ∀ w, eval I (Function.update env "x" w) rubi1214r1Nondeg.result =
        env "c" * (w ^ (k + 2) * (env "f" + env "g" * w) ^ (q + 1)) *
          (env "g" * (env "m" + env "n" + 3))⁻¹ := by
      intro w
      simp [rubi1214r1Nondeg, eval, hkm2, hkn1, toInt?_neg_one, mul_assoc]
    have hEF : eval I (Function.update env "x" t) rubi1214r1Nondeg.body =
        t ^ k * (env "f" + env "g" * t) ^ q * (env "b" * t + env "c" * t ^ 2) := by
      simp [rubi1214r1Nondeg, eval, hkm, hkn, toInt?_two]
    rw [hEF, show (fun w => eval I (Function.update env "x" w) rubi1214r1Nondeg.result) =
        fun w => env "c" * (w ^ (k + 2) * (env "f" + env "g" * w) ^ (q + 1)) *
          (env "g" * (env "m" + env "n" + 3))⁻¹ from funext hE]
    have hx2 : t ≠ 0 ∨ 0 ≤ k + 2 := by
      by_cases h : k < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hx1 : t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hx0 : t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have hu : env "f" + env "g" * t ≠ 0 ∨ 0 ≤ q + 1 := by
      by_cases h : q + 1 < 0
      · exact Or.inl (ht.2 (by omega))
      · exact Or.inr (by omega)
    have hu0 : env "f" + env "g" * t ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    refine ((((hasDerivAt_zpow (k + 2) t hx2).mul (HasDerivAt.comp t
        (hasDerivAt_zpow (q + 1) _ hu)
        (((hasDerivAt_id' t).const_mul (env "g")).const_add (env "f")))).const_mul
          (env "c")).mul_const _).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right, show k + 2 - 1 = k + 1 by ring]
    rw [show k + 2 = k + 1 + 1 by ring, zpow_succ_of _ _ hx1, zpow_succ_of _ _ hx0,
      zpow_succ_of _ _ hu0]
    generalize (env "f" + env "g" * t) ^ q = V
    generalize t ^ k = X
    rw [hm, hn] at hgK heq ⊢
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ hgK]
    linear_combination (X * t * V) * heq

theorem rubi1214r1Nondeg_real : rubi1214r1Nondeg.Holds .real :=
  rubi1214r1Nondeg_holds Interp.real

theorem rubi1214r1Nondeg_complex : rubi1214r1Nondeg.Holds .complex :=
  rubi1214r1Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec40
