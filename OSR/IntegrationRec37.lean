import OSR.IntegrationRec36

/-!
# Integration (RUBI): corrected variants (non-degeneracy)

The RUBI rules 1.1.1.1 #4, 9.1 #9, 4.1.13 #11 and #12 are refuted as stated: at a
degenerate coefficient the integrand is defined but the result divides by zero.
These *strengthened* variants keep the converted RUBI conditions and append the
non-degeneracy condition (`b (m + 1) ≠ 0` or `2 c ≠ 0`).  Proved over ℝ and ℂ;
the refutations of the original rules are kept.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec37

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- ∫ (a + b x)^m = (a + b x)^(m+1)/(b (m+1)), when b (m+1) ≠ 0 -/
def linearPowerNondeg : CRule where
  id := "integration.linear_power_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.1 (a+b x)^m:4"
  shape := .antideriv; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m"))
  result := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "m"]
  conditions := [.ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.int 0)]
  priority := 7000
  description := "∫ (a + b x)^m = (a + b x)^(m+1)/(b (m+1)), when b (m+1) ≠ 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.1 (a+b x)^m:4" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.1 (a+b x)^m.m#4"
/-- RUBI 9.1 #9 when 2 c ≠ 0 -/
def constTimesLinearNondeg : CRule where
  id := "integration.constant_times_linear_nondegenerate"; legacyId := some "rubi:9 Miscellaneous/9.1 Integrand simplification rules:9"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.var "a") (.app2 .add (.var "b") (.app2 .mul (.var "c") (.var "x"))))
  result := (.app2 .mul (.app2 .mul (.var "a") (.pow (.app2 .add (.var "b") (.app2 .mul (.var "c") (.var "x"))) (.int 2))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1))))
  independent := ["a", "b", "c"]
  conditions := [.ne (.app2 .mul (.int 2) (.var "c")) (.int 0)]
  priority := 7010
  description := "RUBI 9.1 #9 when 2 c ≠ 0"
  provenance := migrated "rubi:9 Miscellaneous/9.1 Integrand simplification rules:9" "9 Miscellaneous/9.1 Integrand simplification rules.m#9"
/-- RUBI 4.1.13 #11 when 2 c ≠ 0 -/
def rubi41_13r11Nondeg : CRule where
  id := "integration.rubi_4_1_13_r11_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:11"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1))))
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .ne (.app2 .mul (.int 2) (.var "c")) (.int 0)]
  priority := 7020
  description := "RUBI 4.1.13 #11 when 2 c ≠ 0"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:11" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#11"
/-- RUBI 4.1.13 #12 when 2 c ≠ 0 -/
def rubi41_13r12Nondeg : CRule where
  id := "integration.rubi_4_1_13_r12_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:12"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .mul (.app2 .mul (.var "e") (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1))))
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .ne (.app2 .mul (.int 2) (.var "c")) (.int 0)]
  priority := 7030
  description := "RUBI 4.1.13 #12 when 2 c ≠ 0"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:12" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#12"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

/-- **1.1.1.1 #4** with `b (m + 1) ≠ 0`. -/
theorem linearPowerNondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" linearPowerNondeg.conditions linearPowerNondeg.body
      linearPowerNondeg.result := by
  intro env hc t hF
  have hbm : env "b" * (env "m" + 1) ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.int 0))
      (by simp [linearPowerNondeg])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [linearPowerNondeg, Defined, eval, hk] at h
  have hmk : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk
  have hk1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hmk]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) linearPowerNondeg.body ↔
      (k < 0 → env "a" + env "b" * w ≠ 0) := by
    intro w
    simp [linearPowerNondeg, Defined, eval, hk]
  have hDG : ∀ w, Defined I (Function.update env "x" w) linearPowerNondeg.result ↔
      (k + 1 < 0 → env "a" + env "b" * w ≠ 0) := by
    intro w
    simp [linearPowerNondeg, Defined, eval, hk1, toInt?_neg_one, hbm]
  have hE : ∀ w, eval I (Function.update env "x" w) linearPowerNondeg.result =
      (env "a" + env "b" * w) ^ (k + 1) * (env "b" * (env "m" + 1))⁻¹ := by
    intro w
    simp [linearPowerNondeg, eval, hk1, toInt?_neg_one]
  have hEF : eval I (Function.update env "x" t) linearPowerNondeg.body =
      (env "a" + env "b" * t) ^ k := by
    simp [linearPowerNondeg, eval, hk]
  have ht := (hD t).1 hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact (hDG w).2 fun h => (hD w).1 hw (by omega)
  · have hne : env "a" + env "b" * t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hfun : (fun w => eval I (Function.update env "x" w) linearPowerNondeg.result) =
        fun w => (env "a" + env "b" * w) ^ (k + 1) * (env "b" * (env "m" + 1))⁻¹ := funext hE
    rw [hEF, hfun]
    refine ((HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hne)
      (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a"))).mul_const _).congr_deriv ?_
    rw [add_sub_cancel_right]
    rw [hmk] at hbm ⊢
    have hb0 : env "b" ≠ 0 := left_ne_zero_of_mul hbm
    have hk0 : (k : 𝕜) + 1 ≠ 0 := right_ne_zero_of_mul hbm
    push_cast
    field_simp

theorem linearPowerNondeg_real : linearPowerNondeg.Holds .real :=
  linearPowerNondeg_holds Interp.real

theorem linearPowerNondeg_complex : linearPowerNondeg.Holds .complex :=
  linearPowerNondeg_holds Interp.complex

/-- **9.1 #9** with `2 c ≠ 0`. -/
theorem constTimesLinearNondeg_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" constTimesLinearNondeg.conditions constTimesLinearNondeg.body
      constTimesLinearNondeg.result := by
  intro env hc t hF
  have hc2 : (2 : 𝕜) * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [constTimesLinearNondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hE : ∀ w, eval I (Function.update env "x" w) constTimesLinearNondeg.result =
      env "a" * (env "b" + env "c" * w) ^ 2 * (2 * env "c")⁻¹ := by
    intro w
    simp [constTimesLinearNondeg, eval, toInt?_two, toInt?_neg_one]
  refine ⟨Eventually.of_forall fun w => ?_, ?_⟩
  · simp [constTimesLinearNondeg, Defined, eval, toInt?_two, toInt?_neg_one, hc2]
  · rw [show (fun w => eval I (Function.update env "x" w) constTimesLinearNondeg.result) =
        fun w => env "a" * (env "b" + env "c" * w) ^ 2 * (2 * env "c")⁻¹ from funext hE]
    refine ((((((hasDerivAt_id' t).const_mul (env "c")).const_add (env "b")).pow 2).const_mul
      (env "a")).mul_const _).congr_deriv ?_
    have hc0 : env "c" ≠ 0 := right_ne_zero_of_mul hc2
    have h20 : (2 : 𝕜) ≠ 0 := left_ne_zero_of_mul hc2
    simp [constTimesLinearNondeg, eval]
    field_simp

theorem constTimesLinearNondeg_real : constTimesLinearNondeg.Holds .real :=
  constTimesLinearNondeg_holds Interp.real

theorem constTimesLinearNondeg_complex : constTimesLinearNondeg.Holds .complex :=
  constTimesLinearNondeg_holds Interp.complex

/-- **4.1.13 #11** with `2 c ≠ 0`. -/
theorem rubi41_13r11Nondeg_holds (I : Interp 𝕜)
    (hcd : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivHoldsUnder I "x" rubi41_13r11Nondeg.conditions rubi41_13r11Nondeg.body
      rubi41_13r11Nondeg.result := by
  intro env hc t hF
  have hc2 : (2 : 𝕜) * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [rubi41_13r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : 2 * env "c" * env "d" + -1 * env "b" * env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d"))
      (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0))
      (by simp [rubi41_13r11Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hE : ∀ w, eval I (Function.update env "x" w) rubi41_13r11Nondeg.result =
      -1 * env "e" * I.cos (env "a" + env "b" * w + env "c" * w ^ 2) * (2 * env "c")⁻¹ := by
    intro w
    simp [rubi41_13r11Nondeg, eval, toInt?_two, toInt?_neg_one]
  refine ⟨Eventually.of_forall fun w => ?_, ?_⟩
  · simp [rubi41_13r11Nondeg, Defined, eval, toInt?_two, toInt?_neg_one, hc2]
  · rw [show (fun w => eval I (Function.update env "x" w) rubi41_13r11Nondeg.result) =
        fun w => -1 * env "e" * I.cos (env "a" + env "b" * w + env "c" * w ^ 2) *
          (2 * env "c")⁻¹ from funext hE]
    have hq : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2)
        (env "b" * 1 + env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
        (((hasDerivAt_id' t).pow 2).const_mul (env "c"))
    refine ((((hcd _).comp t hq).const_mul (-1 * env "e")).mul_const _).congr_deriv ?_
    have hB : eval I (Function.update env "x" t) rubi41_13r11Nondeg.body =
        (env "d" + env "e" * t) * I.sin (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi41_13r11Nondeg, eval, toInt?_two]
    rw [hB, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    have hc0 : env "c" ≠ 0 := right_ne_zero_of_mul hc2
    have h20 : (2 : 𝕜) ≠ 0 := left_ne_zero_of_mul hc2
    generalize I.sin (env "a" + env "b" * t + env "c" * t ^ 2) = S
    field_simp
    linear_combination (-S) * heq

theorem rubi41_13r11Nondeg_real : rubi41_13r11Nondeg.Holds .real :=
  rubi41_13r11Nondeg_holds Interp.real Real.hasDerivAt_cos

theorem rubi41_13r11Nondeg_complex : rubi41_13r11Nondeg.Holds .complex :=
  rubi41_13r11Nondeg_holds Interp.complex Complex.hasDerivAt_cos

/-- **4.1.13 #12** with `2 c ≠ 0`. -/
theorem rubi41_13r12Nondeg_holds (I : Interp 𝕜)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) :
    AntiderivHoldsUnder I "x" rubi41_13r12Nondeg.conditions rubi41_13r12Nondeg.body
      rubi41_13r12Nondeg.result := by
  intro env hc t hF
  have hc2 : (2 : 𝕜) * env "c" ≠ 0 := by
    have h := hc (.ne (.app2 .mul (.int 2) (.var "c")) (.int 0))
      (by simp [rubi41_13r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have heq : 2 * env "c" * env "d" + -1 * env "b" * env "e" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d"))
      (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0))
      (by simp [rubi41_13r12Nondeg])
    simpa [Cond.Holds, Defined, eval] using h
  have hE : ∀ w, eval I (Function.update env "x" w) rubi41_13r12Nondeg.result =
      env "e" * I.sin (env "a" + env "b" * w + env "c" * w ^ 2) * (2 * env "c")⁻¹ := by
    intro w
    simp [rubi41_13r12Nondeg, eval, toInt?_two, toInt?_neg_one]
  refine ⟨Eventually.of_forall fun w => ?_, ?_⟩
  · simp [rubi41_13r12Nondeg, Defined, eval, toInt?_two, toInt?_neg_one, hc2]
  · rw [show (fun w => eval I (Function.update env "x" w) rubi41_13r12Nondeg.result) =
        fun w => env "e" * I.sin (env "a" + env "b" * w + env "c" * w ^ 2) *
          (2 * env "c")⁻¹ from funext hE]
    have hq : HasDerivAt (fun w => env "a" + env "b" * w + env "c" * w ^ 2)
        (env "b" * 1 + env "c" * (↑2 * t ^ (2 - 1) * 1)) t :=
      (((hasDerivAt_id' t).const_mul (env "b")).const_add (env "a")).add
        (((hasDerivAt_id' t).pow 2).const_mul (env "c"))
    refine ((((hs _).comp t hq).const_mul (env "e")).mul_const _).congr_deriv ?_
    have hB : eval I (Function.update env "x" t) rubi41_13r12Nondeg.body =
        (env "d" + env "e" * t) * I.cos (env "a" + env "b" * t + env "c" * t ^ 2) := by
      simp [rubi41_13r12Nondeg, eval, toInt?_two]
    rw [hB, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    have hc0 : env "c" ≠ 0 := right_ne_zero_of_mul hc2
    have h20 : (2 : 𝕜) ≠ 0 := left_ne_zero_of_mul hc2
    generalize I.cos (env "a" + env "b" * t + env "c" * t ^ 2) = S
    field_simp
    linear_combination (-S) * heq

theorem rubi41_13r12Nondeg_real : rubi41_13r12Nondeg.Holds .real :=
  rubi41_13r12Nondeg_holds Interp.real Real.hasDerivAt_sin

theorem rubi41_13r12Nondeg_complex : rubi41_13r12Nondeg.Holds .complex :=
  rubi41_13r12Nondeg_holds Interp.complex Complex.hasDerivAt_sin

end Proofs

end OSR.IntegrationRec37
