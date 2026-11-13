import OSR.IntegrationRec3

/-!
# Integration (RUBI): proofs of rules the numerical search could not refute

`handoff/refute_search.py` also checks, numerically, that a rule's result
differentiates to its integrand where everything is defined.  The rules of
this module passed that check and are proved here in Lean.  Declarations are
transcribed by a tool and checked against the v0.1 corpus by the Integration
repository's `scripts/v1_faithfulness.py`.
-/

namespace OSR.IntegrationRec4

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- (a + b x^n)^p = x^(n p) (b + a x^(-n))^p under the integral, for n < 0 -/
def binomNegPow : CRule where
  id := "integration.binomial_negative_power"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.1 (a+b x^n)^p:5"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .mul (.var "n") (.var "p"))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "p"))))]
  independent := ["a", "b", "n", "p"]
  conditions := [.gt (.int 0) (.var "n"),
    .int (.var "p")]
  priority := 1400
  description := "(a + b x^n)^p = x^(n p) (b + a x^(-n))^p under the integral, for n < 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.1 (a+b x^n)^p:5" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.1 (a+b x^n)^p.m#5"

/-- (a + b x^n)^p sin(c + d x), rewritten for n, p < 0 -/
def binomPowSin : CRule where
  id := "integration.binomial_power_sin"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .mul (.var "n") (.var "p"))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "p"))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.int 0) (.var "p"),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 1410
  description := "(a + b x^n)^p sin(c + d x), rewritten for n, p < 0"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin:7" "4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin.m#7"

/-- (a + b x^n)^p cos(c + d x), rewritten for n, p < 0 -/
def binomPowCos : CRule where
  id := "integration.binomial_power_cos"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .mul (.var "n") (.var "p"))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "p"))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.int 0) (.var "p"),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 1420
  description := "(a + b x^n)^p cos(c + d x), rewritten for n, p < 0"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin:8" "4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin.m#8"

/-- x^m (a + b x^n)^p sin(c + d x), rewritten for n, p < 0 -/
def monoBinomPowSin : CRule where
  id := "integration.monomial_binomial_power_sin"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.var "n") (.var "p")))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "p"))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.int 0) (.var "p"),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 1430
  description := "x^m (a + b x^n)^p sin(c + d x), rewritten for n, p < 0"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin:19" "4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin.m#19"

/-- x^m (a + b x^n)^p cos(c + d x), rewritten for n, p < 0 -/
def monoBinomPowCos : CRule where
  id := "integration.monomial_binomial_power_cos"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.var "n") (.var "p")))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "p"))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.int 0) (.var "p"),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 1440
  description := "x^m (a + b x^n)^p cos(c + d x), rewritten for n, p < 0"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin:20" "4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin.m#20"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- `x^(n p) (b + a x^(-n))^p = (a + b x^n)^p` for `x ≠ 0`. -/
theorem binom_core (w a b : 𝕜) (n p : ℤ) (hw : w ≠ 0) :
    w ^ (n * p) * (b + a * w ^ (-n)) ^ p = (a + b * w ^ n) ^ p := by
  have hn : w ^ n ≠ 0 := zpow_ne_zero n hw
  have h1 : b + a * w ^ (-n) = (a + b * w ^ n) * (w ^ n)⁻¹ := by
    rw [zpow_neg]; field_simp; ring
  have hz : w ^ (n * p) ≠ 0 := zpow_ne_zero _ hw
  rw [h1, mul_zpow, inv_zpow, ← zpow_mul]
  field_simp

/-- `binom_core` with `x^(-n)` written `(x^n)⁻¹`, as `simp` leaves it. -/
theorem binom_core_inv (w a b : 𝕜) (n p : ℤ) (hw : w ≠ 0) :
    w ^ (n * p) * (b + a * (w ^ n)⁻¹) ^ p = (a + b * w ^ n) ^ p := by
  simpa using binom_core w a b n p hw

/-- The integer an assignment gives to a metavariable whose `toInt?` is `k`. -/
private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

theorem binomNegPow_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" binomNegPow.conditions binomNegPow.body binomNegPow.result
      binomNegPow.integrals := by
  intro env hc t hF
  have hgt := hc (.gt (.int 0) (.var "n")) (by simp [binomNegPow])
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [binomNegPow, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [binomNegPow, Defined, eval, hkp] at h
  have hn := toInt?_val hkn
  have hp := toInt?_val hkp
  have hneg : n < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgt
    rw [hn] at hgt
    have h' : I.lt ((n : ℚ) : 𝕜) ((0 : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgt
    exact_mod_cast (hlt _ _).1 h'
  have hnp : I.toInt? (env "n" * env "p") = some (n * p) :=
    (I.toInt?_eq _ _).2 (by rw [hn, hp]; push_cast; ring)
  have hmn : I.toInt? (-env "n") = some (-n) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) binomNegPow.body →
      w ≠ 0 ∧ (p < 0 → env "a" + env "b" * w ^ n ≠ 0) := by
    intro w h
    simp [binomNegPow, Defined, eval, hkn, hkp] at h
    exact ⟨h.1 hneg, h.2⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [binomNegPow, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hw0, hpz⟩ := hD w hw
    simp [Defined, eval, hnp, hmn, hkp, hw0]
    intro hp0 h0
    apply hpz hp0
    have hwn : w ^ n ≠ 0 := zpow_ne_zero n hw0
    have := congrArg (· * w ^ n) h0
    simp only [zero_mul, add_mul, mul_assoc, inv_mul_cancel₀ hwn, mul_one] at this
    linear_combination this
  · exact Eventually.of_forall fun _ => by simp [binomNegPow, Defined]
  · simp only [binomNegPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (binomNegPow.integrals.map (·.1)) Φ "x" w)
        binomNegPow.result) = Φ "I1" := by
      funext w
      simp [binomNegPow, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    obtain ⟨ht0, -⟩ := hD t hF.self_of_nhds
    simp [binomNegPow, eval, hnp, hmn, hkn, hkp]
    simpa using binom_core t (env "a") (env "b") n p ht0

theorem binomNegPow_real : binomNegPow.Holds .real :=
  binomNegPow_holds Interp.real Interp.real_lt_rat

theorem binomNegPow_complex : binomNegPow.Holds .complex :=
  binomNegPow_holds Interp.complex Interp.complex_lt_rat

theorem binomPowSin_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" binomPowSin.conditions binomPowSin.body binomPowSin.result binomPowSin.integrals := by
  intro env hc t hF
  have hgt := hc (.gt (.int 0) (.var "n")) (by simp [binomPowSin])
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [binomPowSin, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [binomPowSin, Defined, eval, hkp] at h
  have hn := toInt?_val hkn
  have hp := toInt?_val hkp
  have hneg : n < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgt
    rw [hn] at hgt
    have h' : I.lt ((n : ℚ) : 𝕜) ((0 : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgt
    exact_mod_cast (hlt _ _).1 h'
  have hnp : I.toInt? (env "n" * env "p") = some (n * p) :=
    (I.toInt?_eq _ _).2 (by rw [hn, hp]; push_cast; ring)
  have hmn : I.toInt? (-env "n") = some (-n) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) binomPowSin.body →
      w ≠ 0 ∧ (p < 0 → env "a" + env "b" * w ^ n ≠ 0) := by
    intro w h
    simp [binomPowSin, Defined, eval, hkn, hkp] at h
    exact ⟨by tauto, by tauto⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [binomPowSin, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hw0, hpz⟩ := hD w hw
    simp [Defined, eval, hnp, hmn, hkp, hw0]
    intro hp0 h0
    apply hpz hp0
    have hwn : w ^ n ≠ 0 := zpow_ne_zero n hw0
    have := congrArg (· * w ^ n) h0
    simp only [zero_mul, add_mul, mul_assoc, inv_mul_cancel₀ hwn, mul_one] at this
    linear_combination this
  · exact Eventually.of_forall fun _ => by simp [binomPowSin, Defined]
  · simp only [binomPowSin, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (binomPowSin.integrals.map (·.1)) Φ "x" w)
        binomPowSin.result) = Φ "I1" := by
      funext w
      simp [binomPowSin, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    obtain ⟨ht0, -⟩ := hD t hF.self_of_nhds
    simp [binomPowSin, eval, hnp, hmn, hkn, hkp]
    rw [binom_core_inv t _ _ n p ht0]
    exact Or.inl rfl

theorem binomPowSin_real : binomPowSin.Holds .real := binomPowSin_holds Interp.real Interp.real_lt_rat

theorem binomPowSin_complex : binomPowSin.Holds .complex := binomPowSin_holds Interp.complex Interp.complex_lt_rat

theorem binomPowCos_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" binomPowCos.conditions binomPowCos.body binomPowCos.result binomPowCos.integrals := by
  intro env hc t hF
  have hgt := hc (.gt (.int 0) (.var "n")) (by simp [binomPowCos])
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [binomPowCos, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [binomPowCos, Defined, eval, hkp] at h
  have hn := toInt?_val hkn
  have hp := toInt?_val hkp
  have hneg : n < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgt
    rw [hn] at hgt
    have h' : I.lt ((n : ℚ) : 𝕜) ((0 : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgt
    exact_mod_cast (hlt _ _).1 h'
  have hnp : I.toInt? (env "n" * env "p") = some (n * p) :=
    (I.toInt?_eq _ _).2 (by rw [hn, hp]; push_cast; ring)
  have hmn : I.toInt? (-env "n") = some (-n) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) binomPowCos.body →
      w ≠ 0 ∧ (p < 0 → env "a" + env "b" * w ^ n ≠ 0) := by
    intro w h
    simp [binomPowCos, Defined, eval, hkn, hkp] at h
    exact ⟨by tauto, by tauto⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [binomPowCos, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hw0, hpz⟩ := hD w hw
    simp [Defined, eval, hnp, hmn, hkp, hw0]
    intro hp0 h0
    apply hpz hp0
    have hwn : w ^ n ≠ 0 := zpow_ne_zero n hw0
    have := congrArg (· * w ^ n) h0
    simp only [zero_mul, add_mul, mul_assoc, inv_mul_cancel₀ hwn, mul_one] at this
    linear_combination this
  · exact Eventually.of_forall fun _ => by simp [binomPowCos, Defined]
  · simp only [binomPowCos, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (binomPowCos.integrals.map (·.1)) Φ "x" w)
        binomPowCos.result) = Φ "I1" := by
      funext w
      simp [binomPowCos, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    obtain ⟨ht0, -⟩ := hD t hF.self_of_nhds
    simp [binomPowCos, eval, hnp, hmn, hkn, hkp]
    rw [binom_core_inv t _ _ n p ht0]
    exact Or.inl rfl

theorem binomPowCos_real : binomPowCos.Holds .real := binomPowCos_holds Interp.real Interp.real_lt_rat

theorem binomPowCos_complex : binomPowCos.Holds .complex := binomPowCos_holds Interp.complex Interp.complex_lt_rat

theorem monoBinomPowSin_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" monoBinomPowSin.conditions monoBinomPowSin.body monoBinomPowSin.result monoBinomPowSin.integrals := by
  intro env hc t hF
  have hgt := hc (.gt (.int 0) (.var "n")) (by simp [monoBinomPowSin])
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomPowSin, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomPowSin, Defined, eval, hkp] at h
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomPowSin, Defined, eval, hkm] at h
  have hn := toInt?_val hkn
  have hp := toInt?_val hkp
  have hneg : n < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgt
    rw [hn] at hgt
    have h' : I.lt ((n : ℚ) : 𝕜) ((0 : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgt
    exact_mod_cast (hlt _ _).1 h'
  have hnp : I.toInt? (env "m" + env "n" * env "p") = some (m + n * p) :=
    (I.toInt?_eq _ _).2 (by rw [toInt?_val hkm, hn, hp]; push_cast; ring)
  have hmn : I.toInt? (-env "n") = some (-n) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) monoBinomPowSin.body →
      w ≠ 0 ∧ (p < 0 → env "a" + env "b" * w ^ n ≠ 0) := by
    intro w h
    simp [monoBinomPowSin, Defined, eval, hkn, hkp, hkm] at h
    exact ⟨by tauto, by tauto⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [monoBinomPowSin, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hw0, hpz⟩ := hD w hw
    simp [Defined, eval, hnp, hmn, hkp, hw0]
    intro hp0 h0
    apply hpz hp0
    have hwn : w ^ n ≠ 0 := zpow_ne_zero n hw0
    have := congrArg (· * w ^ n) h0
    simp only [zero_mul, add_mul, mul_assoc, inv_mul_cancel₀ hwn, mul_one] at this
    linear_combination this
  · exact Eventually.of_forall fun _ => by simp [monoBinomPowSin, Defined]
  · simp only [monoBinomPowSin, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (monoBinomPowSin.integrals.map (·.1)) Φ "x" w)
        monoBinomPowSin.result) = Φ "I1" := by
      funext w
      simp [monoBinomPowSin, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    obtain ⟨ht0, -⟩ := hD t hF.self_of_nhds
    simp [monoBinomPowSin, eval, hnp, hmn, hkn, hkp, hkm]
    rw [zpow_add₀ ht0, mul_assoc (t ^ m), binom_core_inv t _ _ n p ht0]
    exact Or.inl rfl

theorem monoBinomPowSin_real : monoBinomPowSin.Holds .real := monoBinomPowSin_holds Interp.real Interp.real_lt_rat

theorem monoBinomPowSin_complex : monoBinomPowSin.Holds .complex := monoBinomPowSin_holds Interp.complex Interp.complex_lt_rat

theorem monoBinomPowCos_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" monoBinomPowCos.conditions monoBinomPowCos.body monoBinomPowCos.result monoBinomPowCos.integrals := by
  intro env hc t hF
  have hgt := hc (.gt (.int 0) (.var "n")) (by simp [monoBinomPowCos])
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomPowCos, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomPowCos, Defined, eval, hkp] at h
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomPowCos, Defined, eval, hkm] at h
  have hn := toInt?_val hkn
  have hp := toInt?_val hkp
  have hneg : n < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgt
    rw [hn] at hgt
    have h' : I.lt ((n : ℚ) : 𝕜) ((0 : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgt
    exact_mod_cast (hlt _ _).1 h'
  have hnp : I.toInt? (env "m" + env "n" * env "p") = some (m + n * p) :=
    (I.toInt?_eq _ _).2 (by rw [toInt?_val hkm, hn, hp]; push_cast; ring)
  have hmn : I.toInt? (-env "n") = some (-n) :=
    (I.toInt?_eq _ _).2 (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) monoBinomPowCos.body →
      w ≠ 0 ∧ (p < 0 → env "a" + env "b" * w ^ n ≠ 0) := by
    intro w h
    simp [monoBinomPowCos, Defined, eval, hkn, hkp, hkm] at h
    exact ⟨by tauto, by tauto⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [monoBinomPowCos, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hw0, hpz⟩ := hD w hw
    simp [Defined, eval, hnp, hmn, hkp, hw0]
    intro hp0 h0
    apply hpz hp0
    have hwn : w ^ n ≠ 0 := zpow_ne_zero n hw0
    have := congrArg (· * w ^ n) h0
    simp only [zero_mul, add_mul, mul_assoc, inv_mul_cancel₀ hwn, mul_one] at this
    linear_combination this
  · exact Eventually.of_forall fun _ => by simp [monoBinomPowCos, Defined]
  · simp only [monoBinomPowCos, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (monoBinomPowCos.integrals.map (·.1)) Φ "x" w)
        monoBinomPowCos.result) = Φ "I1" := by
      funext w
      simp [monoBinomPowCos, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    obtain ⟨ht0, -⟩ := hD t hF.self_of_nhds
    simp [monoBinomPowCos, eval, hnp, hmn, hkn, hkp, hkm]
    rw [zpow_add₀ ht0, mul_assoc (t ^ m), binom_core_inv t _ _ n p ht0]
    exact Or.inl rfl

theorem monoBinomPowCos_real : monoBinomPowCos.Holds .real := monoBinomPowCos_holds Interp.real Interp.real_lt_rat

theorem monoBinomPowCos_complex : monoBinomPowCos.Holds .complex := monoBinomPowCos_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec4
