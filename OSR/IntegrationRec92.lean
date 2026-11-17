import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, first batch

The named rules 1.1.1.4 #17, 1.1.3.5 #10 and #2, and 1.2.1.3 #11 and #12 are
refuted as stated (a coefficient the result divides by may vanish).  These
strengthened variants keep their conditions and append the non-degeneracy
condition; they are proved over ℝ and ℂ, and the refutations are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec92

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- ∫ (c + d x)^n (e + f x)^p (g + h x)/(a + b x), split, when b ≠ 0 -/
def linOverLinNondeg : CRule where
  id := "integration.linear_factor_over_linear_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "h") (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h"))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))), ("I2", .app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "n", "p"]
  conditions := [.ne (.var "b") (.int 0)]
  priority := 9101
  description := "∫ (c + d x)^n (e + f x)^p (g + h x)/(a + b x), split, when b ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:17" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#17"

/-- ∫ (a + b x^n)^p (e + f x^n)/(c + d x^n), split, when d ≠ 0 -/
def powerRatioNondeg : CRule where
  id := "integration.power_ratio_split_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "f") (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", .pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")), ("I2", .app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "n"]
  conditions := [.ne (.var "d") (.int 0)]
  priority := 9102
  description := "∫ (a + b x^n)^p (e + f x^n)/(c + d x^n), split, when d ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:10" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#10"

/-- Partial fractions of (e + f x^n)/((a + b x^n) (c + d x^n)), when b c - a d ≠ 0 -/
def pfGeneralNondeg : CRule where
  id := "integration.partial_fractions_general_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.int 1) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.int (-1)))), ("I2", .app2 .mul (.int 1) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 9103
  description := "Partial fractions of (e + f x^n)/((a + b x^n) (c + d x^n)), when b c - a d ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:2" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#2"

/-- ∫ (d + e x) (f + g x)/(a + b x + c x^2), when c ≠ 0 -/
def prodOverTrinomNondeg : CRule where
  id := "integration.product_over_trinomial_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "g")) (.var "x")) (.pow (.var "c") (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e")) (.var "g"))) (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.var "f")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "g"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "g"))) (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.var "c") (.int 0)]
  priority := 9104
  description := "∫ (d + e x) (f + g x)/(a + b x + c x^2), when c ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:11" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#11"

/-- ∫ (d + e x) (f + g x)/(a + c x^2), when c ≠ 0 -/
def prodOverQuadNondeg : CRule where
  id := "integration.product_over_quadratic_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "g")) (.var "x")) (.pow (.var "c") (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e")) (.var "g"))) (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g")))) (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int (-1))))]
  independent := ["a", "c", "d", "e", "f", "g"]
  conditions := [.ne (.var "c") (.int 0)]
  priority := 9105
  description := "∫ (d + e x) (f + g x)/(a + c x^2), when c ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:12" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#12"


/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

theorem linOverLinNondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" linOverLinNondeg.conditions linOverLinNondeg.body linOverLinNondeg.result linOverLinNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.var "b") (.int 0)) (by simp [linOverLinNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [linOverLinNondeg, Defined, eval, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [linOverLinNondeg, Defined, eval, hk_n, hk_p] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linOverLinNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
      simp [linOverLinNondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_n, hk_p] at hw ⊢ <;> first | exact hw | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [linOverLinNondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hk_n, hk_p, hN0] at hw ⊢
    first | done | exact hw | tauto | (trace_state; sorry)
  · simp only [linOverLinNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hw := hF.self_of_nhds
    simp [linOverLinNondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_n, hk_p] at hw
    try casesm* _ ∧ _
    have hfun : (fun w => eval I (recEnv env (linOverLinNondeg.integrals.map (·.1)) Φ "x" w) linOverLinNondeg.result) =
        fun w => (((env "h" * (env "b")⁻¹) * Φ "I1" w) + ((((env "b" * env "g") + (((-1) * env "a") * env "h")) * (env "b")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [linOverLinNondeg, eval, recEnv, toInt?_neg_one, toInt?_two, hk_n, hk_p, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    simp [linOverLinNondeg, eval, toInt?_neg_one, toInt?_two, hk_n, hk_p]
    first | (field_simp; ring) | (trace_state; sorry)

theorem powerRatioNondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" powerRatioNondeg.conditions powerRatioNondeg.body powerRatioNondeg.result powerRatioNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.var "d") (.int 0)) (by simp [powerRatioNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [powerRatioNondeg, Defined, eval, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [powerRatioNondeg, Defined, eval, hk_n, hk_p] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powerRatioNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
      simp [powerRatioNondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_n, hk_p] at hw ⊢ <;> first | exact hw | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [powerRatioNondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hk_n, hk_p, hN0] at hw ⊢
    first | done | exact hw | tauto | (trace_state; sorry)
  · simp only [powerRatioNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hw := hF.self_of_nhds
    simp [powerRatioNondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_n, hk_p] at hw
    try casesm* _ ∧ _
    have hfun : (fun w => eval I (recEnv env (powerRatioNondeg.integrals.map (·.1)) Φ "x" w) powerRatioNondeg.result) =
        fun w => (((env "f" * (env "d")⁻¹) * Φ "I1" w) + ((((env "d" * env "e") + (((-1) * env "c") * env "f")) * (env "d")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [powerRatioNondeg, eval, recEnv, toInt?_neg_one, toInt?_two, hk_n, hk_p, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    simp [powerRatioNondeg, eval, toInt?_neg_one, toInt?_two, hk_n, hk_p]
    first | (field_simp; ring) | (trace_state; sorry)

theorem pfGeneralNondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" pfGeneralNondeg.conditions pfGeneralNondeg.body pfGeneralNondeg.result pfGeneralNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [pfGeneralNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso
    have h := hF.self_of_nhds
    simp [pfGeneralNondeg, Defined, eval, hk_n] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [pfGeneralNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
      simp [pfGeneralNondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_n] at hw ⊢ <;> first | exact hw | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [pfGeneralNondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hk_n, hN0] at hw ⊢
    first | done | exact hw | tauto | (trace_state; sorry)
  · simp only [pfGeneralNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hw := hF.self_of_nhds
    simp [pfGeneralNondeg, Defined, eval, toInt?_neg_one, toInt?_two, hk_n] at hw
    try casesm* _ ∧ _
    have hfun : (fun w => eval I (recEnv env (pfGeneralNondeg.integrals.map (·.1)) Φ "x" w) pfGeneralNondeg.result) =
        fun w => (((((env "b" * env "e") + (((-1) * env "a") * env "f")) * ((env "b" * env "c") + (((-1) * env "a") * env "d"))⁻¹) * Φ "I1" w) + ((((-1) * ((env "d" * env "e") + (((-1) * env "c") * env "f"))) * ((env "b" * env "c") + (((-1) * env "a") * env "d"))⁻¹) * Φ "I2" w)) := by
      funext w
      simp [pfGeneralNondeg, eval, recEnv, toInt?_neg_one, toInt?_two, hk_n, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    simp [pfGeneralNondeg, eval, toInt?_neg_one, toInt?_two, hk_n]
    first | (field_simp; ring) | (trace_state; sorry)

theorem prodOverTrinomNondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" prodOverTrinomNondeg.conditions prodOverTrinomNondeg.body prodOverTrinomNondeg.result prodOverTrinomNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [prodOverTrinomNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  have hN1 := hc (.ne (.var "c") (.int 0)) (by simp [prodOverTrinomNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [prodOverTrinomNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [prodOverTrinomNondeg, Defined, eval, toInt?_neg_one, toInt?_two] at hw ⊢
    first | exact hw | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [prodOverTrinomNondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hN0, hN1] at hw ⊢
    first | done | exact hw | tauto | (trace_state; sorry)
  · simp only [prodOverTrinomNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hw := hF.self_of_nhds
    simp [prodOverTrinomNondeg, Defined, eval, toInt?_neg_one, toInt?_two] at hw
    try casesm* _ ∧ _
    have hfun : (fun w => eval I (recEnv env (prodOverTrinomNondeg.integrals.map (·.1)) Φ "x" w) prodOverTrinomNondeg.result) =
        fun w => ((((env "e" * env "g") * w) * (env "c")⁻¹) + ((1 * (env "c")⁻¹) * Φ "I1" w)) := by
      funext w
      simp [prodOverTrinomNondeg, eval, recEnv, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine ((((hasDerivAt_id' t).const_mul _).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp [prodOverTrinomNondeg, eval, toInt?_neg_one, toInt?_two]
    first | (field_simp; ring) | (trace_state; sorry)

theorem prodOverQuadNondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" prodOverQuadNondeg.conditions prodOverQuadNondeg.body prodOverQuadNondeg.result prodOverQuadNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.var "c") (.int 0)) (by simp [prodOverQuadNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [prodOverQuadNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [prodOverQuadNondeg, Defined, eval, toInt?_neg_one, toInt?_two] at hw ⊢
    first | exact hw | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [prodOverQuadNondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hN0] at hw ⊢
    first | done | exact hw | tauto | (trace_state; sorry)
  · simp only [prodOverQuadNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hw := hF.self_of_nhds
    simp [prodOverQuadNondeg, Defined, eval, toInt?_neg_one, toInt?_two] at hw
    try casesm* _ ∧ _
    have hfun : (fun w => eval I (recEnv env (prodOverQuadNondeg.integrals.map (·.1)) Φ "x" w) prodOverQuadNondeg.result) =
        fun w => ((((env "e" * env "g") * w) * (env "c")⁻¹) + ((1 * (env "c")⁻¹) * Φ "I1" w)) := by
      funext w
      simp [prodOverQuadNondeg, eval, recEnv, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine ((((hasDerivAt_id' t).const_mul _).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp [prodOverQuadNondeg, eval, toInt?_neg_one, toInt?_two]
    first | (field_simp; ring) | (trace_state; sorry)

theorem linOverLinNondeg_real : linOverLinNondeg.Holds .real := linOverLinNondeg_holds Interp.real
theorem linOverLinNondeg_complex : linOverLinNondeg.Holds .complex := linOverLinNondeg_holds Interp.complex
theorem powerRatioNondeg_real : powerRatioNondeg.Holds .real := powerRatioNondeg_holds Interp.real
theorem powerRatioNondeg_complex : powerRatioNondeg.Holds .complex := powerRatioNondeg_holds Interp.complex
theorem pfGeneralNondeg_real : pfGeneralNondeg.Holds .real := pfGeneralNondeg_holds Interp.real
theorem pfGeneralNondeg_complex : pfGeneralNondeg.Holds .complex := pfGeneralNondeg_holds Interp.complex
theorem prodOverTrinomNondeg_real : prodOverTrinomNondeg.Holds .real := prodOverTrinomNondeg_holds Interp.real
theorem prodOverTrinomNondeg_complex : prodOverTrinomNondeg.Holds .complex := prodOverTrinomNondeg_holds Interp.complex
theorem prodOverQuadNondeg_real : prodOverQuadNondeg.Holds .real := prodOverQuadNondeg_holds Interp.real
theorem prodOverQuadNondeg_complex : prodOverQuadNondeg.Holds .complex := prodOverQuadNondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec92
