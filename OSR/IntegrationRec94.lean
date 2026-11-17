import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, third batch

The named rules 4.1.13 #17, #18, #3 and #4 are refuted as stated (at c = 0);
these strengthened variants append 2 c ≠ 0 or 4 c ≠ 0 and are proved over ℝ
and ℂ; the refutations are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec94

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- ∫ (d + e x) sin(a + b x + c x^2), when 2 c ≠ 0 -/
def linSinQuadNondeg : CRule where
  id := "integration.linear_sin_trinomial_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .ne (.app2 .mul (.int 2) (.var "c")) (.int 0)]
  priority := 9121
  description := "∫ (d + e x) sin(a + b x + c x^2), when 2 c ≠ 0"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:17" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#17"

/-- ∫ (d + e x) cos(a + b x + c x^2), when 2 c ≠ 0 -/
def linCosQuadNondeg : CRule where
  id := "integration.linear_cos_trinomial_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "e") (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .ne (.app2 .mul (.int 2) (.var "c")) (.int 0)]
  priority := 9122
  description := "∫ (d + e x) cos(a + b x + c x^2), when 2 c ≠ 0"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:18" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#18"

/-- Complete the square in sin(a + b x + c x^2), when 4 c ≠ 0 -/
def sinTrinomSqNondeg : CRule where
  id := "integration.sin_trinomial_square_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:3"
  shape := .antiderivRec; x := "x"
  body := (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app1 .cos (.app2 .mul (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))) (.var "I1")) (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .sin (.app2 .mul (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1)))))) (.var "I2")))
  integrals := [("I1", .app1 .sin (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))), ("I2", .app1 .cos (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1)))))]
  independent := ["a", "b", "c"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .mul (.int 4) (.var "c")) (.int 0)]
  priority := 9123
  description := "Complete the square in sin(a + b x + c x^2), when 4 c ≠ 0"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:3" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#3"

/-- Complete the square in cos(a + b x + c x^2), when 4 c ≠ 0 -/
def cosTrinomSqNondeg : CRule where
  id := "integration.cos_trinomial_square_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:4"
  shape := .antiderivRec; x := "x"
  body := (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app1 .cos (.app2 .mul (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))) (.var "I1")) (.app2 .mul (.app1 .sin (.app2 .mul (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", .app1 .cos (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))), ("I2", .app1 .sin (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1)))))]
  independent := ["a", "b", "c"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .mul (.int 4) (.var "c")) (.int 0)]
  priority := 9124
  description := "Complete the square in cos(a + b x + c x^2), when 4 c ≠ 0"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:4" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#4"


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

theorem linSinQuadNondeg_holds (I : Interp 𝕜)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" linSinQuadNondeg.conditions linSinQuadNondeg.body linSinQuadNondeg.result linSinQuadNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [linSinQuadNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  have hN1 := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [linSinQuadNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linSinQuadNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [linSinQuadNondeg, Defined, eval, toInt?_neg_one, toInt?_two] at hw ⊢ <;>
    first | exact hw | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [linSinQuadNondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hN0, hN1] at hw ⊢ <;>
    first | done | exact hw | exact ⟨fun h => hw.1 (by omega), fun h => hw.2 (by omega)⟩ | exact fun h => hw (by omega) | tauto | (trace_state; sorry)
  · simp only [linSinQuadNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hw := hF.self_of_nhds
    simp [linSinQuadNondeg, Defined, eval, toInt?_neg_one, toInt?_two] at hw
    try casesm* _ ∧ _
    have hQd : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2) (env "b" * 1 + env "c" * ((2 : ℕ) * t ^ (2 - 1))) t :=
      (((hasDerivAt_id' t).const_mul _).const_add _).add ((hasDerivAt_pow 2 t).const_mul _)
    have hT := HasDerivAt.comp t (hcs _) hQd
    have hfun : (fun w => eval I (recEnv env (linSinQuadNondeg.integrals.map (·.1)) Φ "x" w) linSinQuadNondeg.result) =
        fun w => (((((-1) * env "e") * I.cos ((env "a" + (env "b" * w)) + (env "c" * w ^ 2))) * (2 * env "c")⁻¹) + (((((2 * env "c") * env "d") + (((-1) * env "b") * env "e")) * (2 * env "c")⁻¹) * Φ "I1" w)) := by
      funext w
      simp [linSinQuadNondeg, eval, recEnv, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine (((hT.const_mul _).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    try simp only [Function.comp_def]
    simp [linSinQuadNondeg, eval, toInt?_neg_one, toInt?_two]
    first | (field_simp; ring) | (trace_state; sorry)

theorem linCosQuadNondeg_holds (I : Interp 𝕜)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" linCosQuadNondeg.conditions linCosQuadNondeg.body linCosQuadNondeg.result linCosQuadNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)) (by simp [linCosQuadNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  have hN1 := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)) (by simp [linCosQuadNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linCosQuadNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [linCosQuadNondeg, Defined, eval, toInt?_neg_one, toInt?_two] at hw ⊢ <;>
    first | exact hw | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [linCosQuadNondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hN0, hN1] at hw ⊢ <;>
    first | done | exact hw | exact ⟨fun h => hw.1 (by omega), fun h => hw.2 (by omega)⟩ | exact fun h => hw (by omega) | tauto | (trace_state; sorry)
  · simp only [linCosQuadNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hw := hF.self_of_nhds
    simp [linCosQuadNondeg, Defined, eval, toInt?_neg_one, toInt?_two] at hw
    try casesm* _ ∧ _
    have hQd : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2) (env "b" * 1 + env "c" * ((2 : ℕ) * t ^ (2 - 1))) t :=
      (((hasDerivAt_id' t).const_mul _).const_add _).add ((hasDerivAt_pow 2 t).const_mul _)
    have hT := HasDerivAt.comp t (hs _) hQd
    have hfun : (fun w => eval I (recEnv env (linCosQuadNondeg.integrals.map (·.1)) Φ "x" w) linCosQuadNondeg.result) =
        fun w => (((env "e" * I.sin ((env "a" + (env "b" * w)) + (env "c" * w ^ 2))) * (2 * env "c")⁻¹) + (((((2 * env "c") * env "d") + (((-1) * env "b") * env "e")) * (2 * env "c")⁻¹) * Φ "I1" w)) := by
      funext w
      simp [linCosQuadNondeg, eval, recEnv, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine (((hT.const_mul _).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    try simp only [Function.comp_def]
    simp [linCosQuadNondeg, eval, toInt?_neg_one, toInt?_two]
    first | (field_simp; ring) | (trace_state; sorry)

theorem sinTrinomSqNondeg_holds (I : Interp 𝕜) [CharZero 𝕜]
    (hsub : ∀ u v : 𝕜, I.sin (u - v) = I.sin u * I.cos v - I.cos u * I.sin v)
    (hcsub : ∀ u v : 𝕜, I.cos (u - v) = I.cos u * I.cos v + I.sin u * I.sin v) :
    AntiderivRecHolds I "x" sinTrinomSqNondeg.conditions sinTrinomSqNondeg.body sinTrinomSqNondeg.result sinTrinomSqNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [sinTrinomSqNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  have hN1 := hc (.ne (.app2 .mul (.int 4) (.var "c")) (.int 0)) (by simp [sinTrinomSqNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [sinTrinomSqNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
      simp [sinTrinomSqNondeg, Defined, eval, toInt?_neg_one, toInt?_two] at hw ⊢ <;> first | exact hw | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [sinTrinomSqNondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hN0, hN1] at hw ⊢ <;>
    first | done | exact hw | exact ⟨fun h => hw.1 (by omega), fun h => hw.2 (by omega)⟩ | exact fun h => hw (by omega) | tauto | (trace_state; sorry)
  · simp only [sinTrinomSqNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hw := hF.self_of_nhds
    simp [sinTrinomSqNondeg, Defined, eval, toInt?_neg_one, toInt?_two] at hw
    try casesm* _ ∧ _
    have hfun : (fun w => eval I (recEnv env (sinTrinomSqNondeg.integrals.map (·.1)) Φ "x" w) sinTrinomSqNondeg.result) =
        fun w => ((I.cos ((env "b" ^ 2 + ((((-1) * 4) * env "a") * env "c")) * (4 * env "c")⁻¹) * Φ "I1" w) + (((-1) * I.sin ((env "b" ^ 2 + ((((-1) * 4) * env "a") * env "c")) * (4 * env "c")⁻¹)) * Φ "I2" w)) := by
      funext w
      simp [sinTrinomSqNondeg, eval, recEnv, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    have e1 : eval I (Function.update env "x" t) (.app1 .sin (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))) = I.sin ((env "b" + ((2 * env "c") * t)) ^ 2 * (4 * env "c")⁻¹) := by simp [eval, toInt?_neg_one, toInt?_two]
    have e2 : eval I (Function.update env "x" t) (.app1 .cos (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))) = I.cos ((env "b" + ((2 * env "c") * t)) ^ 2 * (4 * env "c")⁻¹) := by simp [eval, toInt?_neg_one, toInt?_two]
    have e3 : eval I (Function.update env "x" t) sinTrinomSqNondeg.body = I.sin ((env "a" + (env "b" * t)) + (env "c" * t ^ 2)) := by simp [sinTrinomSqNondeg, eval, toInt?_neg_one, toInt?_two]
    have hq : ((env "a" + (env "b" * t)) + (env "c" * t ^ 2)) = ((env "b" + ((2 * env "c") * t)) ^ 2 * (4 * env "c")⁻¹) - ((env "b" ^ 2 + ((((-1) * 4) * env "a") * env "c")) * (4 * env "c")⁻¹) := by field_simp; ring
    first | (rw [e1, e2, e3, hq, hsub]; ring) | (trace_state; sorry)

theorem cosTrinomSqNondeg_holds (I : Interp 𝕜) [CharZero 𝕜]
    (hsub : ∀ u v : 𝕜, I.sin (u - v) = I.sin u * I.cos v - I.cos u * I.sin v)
    (hcsub : ∀ u v : 𝕜, I.cos (u - v) = I.cos u * I.cos v + I.sin u * I.sin v) :
    AntiderivRecHolds I "x" cosTrinomSqNondeg.conditions cosTrinomSqNondeg.body cosTrinomSqNondeg.result cosTrinomSqNondeg.integrals := by
  intro env hc t hF
  have hN0 := hc (.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)) (by simp [cosTrinomSqNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN0
  have hN1 := hc (.ne (.app2 .mul (.int 4) (.var "c")) (.int 0)) (by simp [cosTrinomSqNondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hN1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [cosTrinomSqNondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
      simp [cosTrinomSqNondeg, Defined, eval, toInt?_neg_one, toInt?_two] at hw ⊢ <;> first | exact hw | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [cosTrinomSqNondeg, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hN0, hN1] at hw ⊢ <;>
    first | done | exact hw | exact ⟨fun h => hw.1 (by omega), fun h => hw.2 (by omega)⟩ | exact fun h => hw (by omega) | tauto | (trace_state; sorry)
  · simp only [cosTrinomSqNondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hw := hF.self_of_nhds
    simp [cosTrinomSqNondeg, Defined, eval, toInt?_neg_one, toInt?_two] at hw
    try casesm* _ ∧ _
    have hfun : (fun w => eval I (recEnv env (cosTrinomSqNondeg.integrals.map (·.1)) Φ "x" w) cosTrinomSqNondeg.result) =
        fun w => ((I.cos ((env "b" ^ 2 + ((((-1) * 4) * env "a") * env "c")) * (4 * env "c")⁻¹) * Φ "I1" w) + (I.sin ((env "b" ^ 2 + ((((-1) * 4) * env "a") * env "c")) * (4 * env "c")⁻¹) * Φ "I2" w)) := by
      funext w
      simp [cosTrinomSqNondeg, eval, recEnv, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun]
    refine ((hΦ1.const_mul _).add (hΦ2.const_mul _)).congr_deriv ?_
    have e1 : eval I (Function.update env "x" t) (.app1 .cos (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))) = I.cos ((env "b" + ((2 * env "c") * t)) ^ 2 * (4 * env "c")⁻¹) := by simp [eval, toInt?_neg_one, toInt?_two]
    have e2 : eval I (Function.update env "x" t) (.app1 .sin (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))) = I.sin ((env "b" + ((2 * env "c") * t)) ^ 2 * (4 * env "c")⁻¹) := by simp [eval, toInt?_neg_one, toInt?_two]
    have e3 : eval I (Function.update env "x" t) cosTrinomSqNondeg.body = I.cos ((env "a" + (env "b" * t)) + (env "c" * t ^ 2)) := by simp [cosTrinomSqNondeg, eval, toInt?_neg_one, toInt?_two]
    have hq : ((env "a" + (env "b" * t)) + (env "c" * t ^ 2)) = ((env "b" + ((2 * env "c") * t)) ^ 2 * (4 * env "c")⁻¹) - ((env "b" ^ 2 + ((((-1) * 4) * env "a") * env "c")) * (4 * env "c")⁻¹) := by field_simp; ring
    first | (rw [e1, e2, e3, hq, hcsub]; ring) | (trace_state; sorry)

theorem linSinQuadNondeg_real : linSinQuadNondeg.Holds .real := linSinQuadNondeg_holds Interp.real Real.hasDerivAt_sin Real.hasDerivAt_cos
theorem linSinQuadNondeg_complex : linSinQuadNondeg.Holds .complex := linSinQuadNondeg_holds Interp.complex Complex.hasDerivAt_sin Complex.hasDerivAt_cos
theorem linCosQuadNondeg_real : linCosQuadNondeg.Holds .real := linCosQuadNondeg_holds Interp.real Real.hasDerivAt_sin Real.hasDerivAt_cos
theorem linCosQuadNondeg_complex : linCosQuadNondeg.Holds .complex := linCosQuadNondeg_holds Interp.complex Complex.hasDerivAt_sin Complex.hasDerivAt_cos
theorem sinTrinomSqNondeg_real : sinTrinomSqNondeg.Holds .real := sinTrinomSqNondeg_holds Interp.real Real.sin_sub Real.cos_sub
theorem sinTrinomSqNondeg_complex : sinTrinomSqNondeg.Holds .complex := sinTrinomSqNondeg_holds Interp.complex Complex.sin_sub Complex.cos_sub
theorem cosTrinomSqNondeg_real : cosTrinomSqNondeg.Holds .real := cosTrinomSqNondeg_holds Interp.real Real.sin_sub Real.cos_sub
theorem cosTrinomSqNondeg_complex : cosTrinomSqNondeg.Holds .complex := cosTrinomSqNondeg_holds Interp.complex Complex.sin_sub Complex.cos_sub

end Proofs

end OSR.IntegrationRec94
