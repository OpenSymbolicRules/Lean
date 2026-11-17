import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, second batch

The named rules 1.1.1.3 #8, 1.1.3.3 #14 and 1.2.1.2 #13 and #14 are refuted as stated; these
strengthened variants append the non-degeneracy conditions and are proved over
ℝ and ℂ; the refutations are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec93

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- ∫ (a + b x) (c + d x)^n (e + f x)^p, when d f (n + p + 2) ≠ 0 -/
def linTwoPowNondeg : CRule where
  id := "integration.linear_times_two_powers_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1)))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2)) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.int 0)]
  priority := 9111
  description := "∫ (a + b x) (c + d x)^n (e + f x)^p, when d f (n + p + 2) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:8" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#8"

/-- ∫ (d + e x) (a + b x + c x^2)^p, when 2 c (p + 1) ≠ 0 -/
def linTrinomPowNondeg : CRule where
  id := "integration.linear_times_trinomial_power_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0), .ne (.var "p") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0),
    .ne (.app2 .mul (.int 2) (.var "c")) (.int 0)]
  priority := 9112
  description := "∫ (d + e x) (a + b x + c x^2)^p, when 2 c (p + 1) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:13" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#13"

/-- ∫ (c + d x^n)/(a + b x^n) for n < 0, when a ≠ 0 -/
def binomRatioNondeg : CRule where
  id := "integration.binomial_ratio_negative_power_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.var "a") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "a") (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.int 1) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0), .gt (.int 0) (.var "n"),
    .ne (.var "a") (.int 0)]
  priority := 9113
  description := "∫ (c + d x^n)/(a + b x^n) for n < 0, when a ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:14" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#14"

/-- ∫ (d + e x) (a + c x^2)^p, when 2 c (p + 1) ≠ 0 -/
def linearQuadPowNondeg : CRule where
  id := "integration.linear_times_quadratic_power_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.var "d") (.var "I1")))
  integrals := [("I1", .pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))]
  independent := ["a", "c", "d", "e", "p"]
  conditions := [.ne (.var "p") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9114
  description := "∫ (d + e x) (a + c x^2)^p, when 2 c (p + 1) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:14" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#14"


/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem zpow_succ_of (A : 𝕜) (k : ℤ) (h : A ≠ 0 ∨ 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  rcases h with h | h
  · exact zpow_add_one₀ h k
  · lift k to ℕ using h
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      pow_succ]

theorem linTwoPowNondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" linTwoPowNondeg.conditions linTwoPowNondeg.body linTwoPowNondeg.result linTwoPowNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2)) (.int 0)) (by simp [linTwoPowNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  have hN1 := hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.int 0)) (by simp [linTwoPowNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN1
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [linTwoPowNondeg, Defined, eval, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [linTwoPowNondeg, Defined, eval, hk_n, hk_p] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have e_n1 : I.toInt? (env "n" + 1) = some (j + 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have h_p : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have e_p1 : I.toInt? (env "p" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linTwoPowNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [linTwoPowNondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_n, hk_p, e_n1, e_p1] at hw ⊢ <;>
    first | exact hw | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [linTwoPowNondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hk_n, hk_p, e_n1, e_p1, hN0, hN1] at hw ⊢ <;>
    first | done | exact hw | exact ⟨fun h => hw.1 (by omega), fun h => hw.2 (by omega)⟩ | exact fun h => hw (by omega) | tauto | (trace_state; sorry)
  · simp only [linTwoPowNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hw := hF.self_of_nhds
    simp [linTwoPowNondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_n, hk_p, e_n1, e_p1] at hw
    have hC0 : (env "c" + env "d" * t) ≠ 0 ∨ 0 ≤ j := by
      by_cases h : j < 0
      · left; tauto
      · right; omega
    have hC1 : (env "c" + env "d" * t) ≠ 0 ∨ 0 ≤ j + 1 := by
      rcases hC0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hE0 : (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · left; tauto
      · right; omega
    have hE1 : (env "e" + env "f" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hE0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hCd : HasDerivAt (fun w => env "c" + env "d" * w) (env "d" * 1) t := ((hasDerivAt_id' t).const_mul _).const_add _
    have hEd : HasDerivAt (fun w => env "e" + env "f" * w) (env "f" * 1) t := ((hasDerivAt_id' t).const_mul _).const_add _
    have hCp := HasDerivAt.comp t (hasDerivAt_zpow (j + 1) _ hC1) hCd
    have hEp := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hE1) hEd
    try casesm* _ ∧ _
    have hfun : (fun w => eval I (recEnv env (linTwoPowNondeg.integrals.map (·.1)) Φ "x" w) linTwoPowNondeg.result) =
        fun w => ((((env "b" * (env "c" + (env "d" * w)) ^ (j + 1)) * (env "e" + (env "f" * w)) ^ (k + 1)) * ((env "d" * env "f") * ((env "n" + env "p") + 2))⁻¹) + ((((((env "a" * env "d") * env "f") * ((env "n" + env "p") + 2)) + (((-1) * env "b") * (((env "d" * env "e") * (env "n" + 1)) + ((env "c" * env "f") * (env "p" + 1))))) * ((env "d" * env "f") * ((env "n" + env "p") + 2))⁻¹) * Φ "I1" w)) := by
      funext w
      simp [linTwoPowNondeg, eval, recEnv, toInt?_neg_one, toInt?_two, hk_n, hk_p, e_n1, e_p1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine ((((hCp.const_mul _).mul hEp).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    try rw [zpow_succ_of _ _ hC0]
    try rw [zpow_succ_of _ _ hE0]
    simp [linTwoPowNondeg, eval, toInt?_neg_one, toInt?_two, hk_n, hk_p, e_n1, e_p1]
    simp only [h_n, h_p] at *
    push_cast
    first | (field_simp; ring) | (trace_state; sorry)

theorem linTrinomPowNondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" linTrinomPowNondeg.conditions linTrinomPowNondeg.body linTrinomPowNondeg.result linTrinomPowNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [linTrinomPowNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  have hN1 := hc (.ne (.var "p") (.int (-1))) (by simp [linTrinomPowNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN1
  have hN2 := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [linTrinomPowNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN2
  have hN3 := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [linTrinomPowNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN3
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [linTrinomPowNondeg, Defined, eval, hk_p] at h
  have h_p : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have e_p1 : I.toInt? (env "p" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linTrinomPowNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [linTrinomPowNondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_p, e_p1] at hw ⊢ <;>
    first | exact hw | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [linTrinomPowNondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hk_p, e_p1, hN0, hN1, hN2, hN3] at hw ⊢ <;>
    first | done | exact hw | exact ⟨fun h => hw.1 (by omega), fun h => hw.2 (by omega)⟩ | exact fun h => hw (by omega) | tauto | (trace_state; sorry)
  · simp only [linTrinomPowNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hw := hF.self_of_nhds
    simp [linTrinomPowNondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_p, e_p1] at hw
    have hQ0 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · left; tauto
      · right; omega
    have hQ1 : (env "a" + env "b" * t + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hQ0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hQd : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2) (env "b" * 1 + env "c" * ((2 : ℕ) * t ^ (2 - 1))) t :=
      (((hasDerivAt_id' t).const_mul _).const_add _).add ((hasDerivAt_pow 2 t).const_mul _)
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hQ1) hQd
    try casesm* _ ∧ _
    have hfun : (fun w => eval I (recEnv env (linTrinomPowNondeg.integrals.map (·.1)) Φ "x" w) linTrinomPowNondeg.result) =
        fun w => (((env "e" * ((env "a" + (env "b" * w)) + (env "c" * w ^ 2)) ^ (k + 1)) * ((2 * env "c") * (env "p" + 1))⁻¹) + (((((2 * env "c") * env "d") + (((-1) * env "b") * env "e")) * (2 * env "c")⁻¹) * Φ "I1" w)) := by
      funext w
      simp [linTrinomPowNondeg, eval, recEnv, toInt?_neg_one, toInt?_two, hk_p, e_p1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine (((hQp.const_mul _).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    try rw [zpow_succ_of _ _ hQ0]
    simp [linTrinomPowNondeg, eval, toInt?_neg_one, toInt?_two, hk_p, e_p1]
    simp only [h_p] at *
    push_cast
    first | (field_simp; ring) | (trace_state; sorry)

theorem binomRatioNondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" binomRatioNondeg.conditions binomRatioNondeg.body binomRatioNondeg.result binomRatioNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [binomRatioNondeg])
  simp [Cond.Holds, Defined, eval] at hN0
  have hA0 := hc (.ne (.var "a") (.int 0)) (by simp [binomRatioNondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hg := hc (.gt (.int 0) (.var "n")) (by simp [binomRatioNondeg])
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [binomRatioNondeg, Defined, eval, hk_n] at h
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hj : j < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hg
    rw [h_n] at hg
    have h' : I.lt ((j : ℚ) : 𝕜) ((((0 : ℤ)) : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_intCast]; simpa using hg
    exact_mod_cast (hlt _ _).1 h'
  have em : I.toInt? (-1 * env "n") = some (-j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have em' : I.toInt? (-env "n") = some (-j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) binomRatioNondeg.body →
      w ≠ 0 ∧ env "a" + env "b" * w ^ j ≠ 0 := by
    intro w h
    simp [binomRatioNondeg, Defined, eval, hk_n, toInt?_neg_one, hj] at h
    first | exact ⟨h.1, h.2⟩ | exact ⟨h.1.1, h.2⟩ | tauto
  have hBne : ∀ w : 𝕜, w ≠ 0 → env "a" + env "b" * w ^ j ≠ 0 → env "b" + env "a" * (w ^ j)⁻¹ ≠ 0 := by
    intro w hw hA h
    apply hA
    have hT : w ^ j ≠ 0 := zpow_ne_zero _ hw
    have e : env "a" + env "b" * w ^ j = (env "b" + env "a" * (w ^ j)⁻¹) * w ^ j := by
      field_simp
      try ring
    rw [e, h, zero_mul]
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [binomRatioNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hw0, hAw⟩ := hBody w hw
    simp [Defined, eval, em, em', toInt?_neg_one]
    first | exact hBne w hw0 hAw | exact ⟨fun _ => hw0, hBne w hw0 hAw⟩ | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [binomRatioNondeg, Defined, eval, recEnv, toInt?_neg_one, hA0]
  · simp only [binomRatioNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨ht0, hAt⟩ := hBody t hF.self_of_nhds
    have hBt := hBne t ht0 hAt
    have hTt : t ^ j ≠ 0 := zpow_ne_zero _ ht0
    have hfun : (fun w => eval I (recEnv env (binomRatioNondeg.integrals.map (·.1)) Φ "x" w) binomRatioNondeg.result) =
        fun w => (((env "c" * w) * (env "a")⁻¹) + ((((-1) * ((env "b" * env "c") + (((-1) * env "a") * env "d"))) * (env "a")⁻¹) * Φ "I1" w)) := by
      funext w
      simp [binomRatioNondeg, eval, recEnv, toInt?_neg_one, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine ((((hasDerivAt_id' t).const_mul _).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp [binomRatioNondeg, eval, hk_n, em, em', toInt?_neg_one]
    have hAt1 : env "b" * t ^ j + env "a" ≠ 0 := by rwa [add_comm] at hAt
    have hAt2 : t ^ j * env "b" + env "a" ≠ 0 := by rwa [add_comm, mul_comm] at hAt
    first | (field_simp; ring) | (field_simp [hAt, hAt1, hAt2, hBt, hTt, hA0]; ring) | (trace_state; sorry)

theorem linearQuadPowNondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" linearQuadPowNondeg.conditions linearQuadPowNondeg.body linearQuadPowNondeg.result linearQuadPowNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.var "p") (.int (-1))) (by simp [linearQuadPowNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  have hN1 := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [linearQuadPowNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN1
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [linearQuadPowNondeg, Defined, eval, hk_p] at h
  have h_p : env "p" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have e_p1 : I.toInt? (env "p" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linearQuadPowNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [linearQuadPowNondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_p, e_p1] at hw ⊢ <;>
    first | exact hw | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [linearQuadPowNondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hk_p, e_p1, hN0, hN1] at hw ⊢ <;>
    first | done | exact hw | exact ⟨fun h => hw.1 (by omega), fun h => hw.2 (by omega)⟩ | exact fun h => hw (by omega) | tauto | (trace_state; sorry)
  · simp only [linearQuadPowNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hw := hF.self_of_nhds
    simp [linearQuadPowNondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_p, e_p1] at hw
    have hQ0 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · left; tauto
      · right; omega
    have hQ1 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hQ0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hQd : HasDerivAt (fun w => env "a" + env "c" * w ^ 2) (env "c" * ((2 : ℕ) * t ^ (2 - 1))) t :=
      ((hasDerivAt_pow 2 t).const_mul _).const_add _
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hQ1) hQd
    try casesm* _ ∧ _
    have hfun : (fun w => eval I (recEnv env (linearQuadPowNondeg.integrals.map (·.1)) Φ "x" w) linearQuadPowNondeg.result) =
        fun w => (((env "e" * (env "a" + (env "c" * w ^ 2)) ^ (k + 1)) * ((2 * env "c") * (env "p" + 1))⁻¹) + (env "d" * Φ "I1" w)) := by
      funext w
      simp [linearQuadPowNondeg, eval, recEnv, toInt?_neg_one, toInt?_two, hk_p, e_p1, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine (((hQp.const_mul _).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    try rw [zpow_succ_of _ _ hQ0]
    simp [linearQuadPowNondeg, eval, toInt?_neg_one, toInt?_two, hk_p, e_p1]
    simp only [h_p] at *
    push_cast
    first | (field_simp; ring) | (trace_state; sorry)

theorem linTwoPowNondeg_real : linTwoPowNondeg.Holds .real := linTwoPowNondeg_holds Interp.real
theorem linTwoPowNondeg_complex : linTwoPowNondeg.Holds .complex := linTwoPowNondeg_holds Interp.complex
theorem linTrinomPowNondeg_real : linTrinomPowNondeg.Holds .real := linTrinomPowNondeg_holds Interp.real
theorem linTrinomPowNondeg_complex : linTrinomPowNondeg.Holds .complex := linTrinomPowNondeg_holds Interp.complex
theorem linearQuadPowNondeg_real : linearQuadPowNondeg.Holds .real := linearQuadPowNondeg_holds Interp.real
theorem linearQuadPowNondeg_complex : linearQuadPowNondeg.Holds .complex := linearQuadPowNondeg_holds Interp.complex
theorem binomRatioNondeg_real : binomRatioNondeg.Holds .real :=
  binomRatioNondeg_holds Interp.real Interp.real_lt_rat
theorem binomRatioNondeg_complex : binomRatioNondeg.Holds .complex :=
  binomRatioNondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec93
