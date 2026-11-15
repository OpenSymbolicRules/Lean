import OSR.IntegrationRec17

/-!
# Integration (RUBI): rewritings into a residual integral

Rules that a numerical check found to behave as identities where they are
defined, proved here over every interpretation having the needed
trigonometric identities.  The rule declarations are transcribed by a tool
and checked by the Integration repository's `scripts/v1_faithfulness.py`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec18

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.1.1.2 #2 -/
def linLinRecip : CRule where
  id := "integration.linear_linear_reciprocal"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0)]
  priority := 3700
  description := "RUBI 1.1.1.2 #2"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:2" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.m#2"

/-- RUBI 1.1.1.3 #50 -/
def linLinMonoPow : CRule where
  id := "integration.linear_linear_monomial_power"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:50"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .mul (.var "f") (.var "x")) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.var "x") (.int 2)))) (.var "m")) (.pow (.app2 .mul (.var "f") (.var "x")) (.var "p"))))]
  independent := ["a", "b", "c", "d", "f", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0),
    .eq (.var "n") (.var "m"),
    .gt (.var "a") (.int 0),
    .gt (.var "c") (.int 0)]
  priority := 3710
  description := "RUBI 1.1.1.3 #50"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:50" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#50"

/-- RUBI 1.1.3.7 #11 -/
def polyBinomSplit : CRule where
  id := "integration.polynomial_binomial_split"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.pow (.var "x") (.var "m")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.var "A") (.var "I1")) (.app2 .mul (.var "B") (.var "I2")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))),
    ("I2", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))))]
  independent := ["a", "b", "A", "B", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.int 0)]
  priority := 3750
  description := "RUBI 1.1.3.7 #11"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p:11" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p.m#11"

/-- RUBI 1.1.3.7 #18 -/
def polyBinomBinomSplit : CRule where
  id := "integration.polynomial_binomial_binomial_split"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.pow (.var "x") (.var "m")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q")))
  result := (.app2 .add (.app2 .mul (.var "A") (.var "I1")) (.app2 .mul (.var "B") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))))]
  independent := ["a", "b", "c", "d", "A", "B", "m", "n", "p", "q"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.int 0)]
  priority := 3760
  description := "RUBI 1.1.3.7 #18"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p:18" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p.m#18"


/-- RUBI 3.1.4 #1 -/
def powInvLinLog : CRule where
  id := "integration.power_inverse_linear_log"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int (-1))))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "d") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p", "q"]
  conditions := [.eq (.var "m") (.var "q"),
    .int (.var "q")]
  priority := 3720
  description := "RUBI 3.1.4 #1"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:1" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#1"

/-- RUBI 3.1.5 #2 -/
def powInvLinLog2 : CRule where
  id := "integration.power_inverse_linear_log_u"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int (-1))))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "d") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p", "q"]
  conditions := [.eq (.var "m") (.var "q"),
    .int (.var "q")]
  priority := 3730
  description := "RUBI 3.1.5 #2"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:2" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#2"

/-- RUBI 3.3 #21 -/
def powInvLinLogLin : CRule where
  id := "integration.power_inverse_linear_log_linear"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:21"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int (-1))))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "f") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "p", "q"]
  conditions := [.eq (.var "m") (.var "q"),
    .int (.var "q")]
  priority := 3740
  description := "RUBI 3.3 #21"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:21" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#21"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

private theorem toInt?_m1 (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_2 (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

theorem linLinRecip_holds [CharZero 𝕜] (I : Interp 𝕜) :
    AntiderivRecHolds I "x" linLinRecip.conditions linLinRecip.body linLinRecip.result linLinRecip.integrals := by
  intro env hc t hF
  have hE := (hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d")))
    (.int 0)) (by simp [linLinRecip])).2.2
  simp [eval] at hE
  have key : ∀ w : 𝕜, env "a" * env "c" + env "b" * env "d" * w ^ 2 =
      (env "a" + env "b" * w) * (env "c" + env "d" * w) := fun w => by
    linear_combination (-w) * hE
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linLinRecip, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [linLinRecip, Defined, eval, toInt?_m1 I, toInt?_2 I] at hw ⊢
    rw [key w]; simpa [not_or] using hw
  · exact Eventually.of_forall fun _ => by simp [linLinRecip, Defined, recEnv]
  · simp only [linLinRecip, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (linLinRecip.integrals.map (·.1)) Φ "x" w)
        linLinRecip.result) = Φ "I1" := by
      funext w; simp [linLinRecip, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [linLinRecip, eval, toInt?_m1 I, toInt?_2 I]
    rw [key t, mul_inv, mul_comm]

theorem linLinRecip_real : linLinRecip.Holds .real := linLinRecip_holds Interp.real

theorem linLinRecip_complex : linLinRecip.Holds .complex := linLinRecip_holds Interp.complex

theorem linLinMonoPow_holds [CharZero 𝕜] (I : Interp 𝕜) :
    AntiderivRecHolds I "x" linLinMonoPow.conditions linLinMonoPow.body linLinMonoPow.result linLinMonoPow.integrals := by
  intro env hc t hF
  have hE := (hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d")))
    (.int 0)) (by simp [linLinMonoPow])).2.2
  simp [eval] at hE
  have hnm := (hc (.eq (.var "n") (.var "m")) (by simp [linLinMonoPow])).2.2
  simp [eval] at hnm
  have key : ∀ w : 𝕜, env "a" * env "c" + env "b" * env "d" * w ^ 2 =
      (env "a" + env "b" * w) * (env "c" + env "d" * w) := fun w => by
    linear_combination (-w) * hE
  rcases hkm : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [linLinMonoPow, Defined, eval, hkm, hnm] at h
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [linLinMonoPow, Defined, eval, hkp] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linLinMonoPow, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [linLinMonoPow, Defined, eval, toInt?_m1 I, toInt?_2 I, hnm, key w, not_or, hkm, hkp] at hw ⊢
    tauto
  · exact Eventually.of_forall fun _ => by simp [linLinMonoPow, Defined, recEnv]
  · simp only [linLinMonoPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (linLinMonoPow.integrals.map (·.1)) Φ "x" w)
        linLinMonoPow.result) = Φ "I1" := by
      funext w; simp [linLinMonoPow, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [linLinMonoPow, eval, toInt?_m1 I, toInt?_2 I, hnm, key t, hkm, mul_zpow]

theorem linLinMonoPow_real : linLinMonoPow.Holds .real := linLinMonoPow_holds Interp.real

theorem linLinMonoPow_complex : linLinMonoPow.Holds .complex := linLinMonoPow_holds Interp.complex

theorem polyBinomSplit_holds [CharZero 𝕜] (I : Interp 𝕜) :
    AntiderivRecHolds I "x" polyBinomSplit.conditions polyBinomSplit.body polyBinomSplit.result polyBinomSplit.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [polyBinomSplit, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      simp [polyBinomSplit, Defined, eval] at hw ⊢
      tauto
  · exact Eventually.of_forall fun _ => by simp [polyBinomSplit, Defined, recEnv]
  · simp only [polyBinomSplit, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (polyBinomSplit.integrals.map (·.1)) Φ "x" w)
        polyBinomSplit.result) = fun w => env "A" * Φ "I1" w + env "B" * Φ "I2" w := by
      funext w; simp [polyBinomSplit, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [polyBinomSplit, eval]
    ring

theorem polyBinomSplit_real : polyBinomSplit.Holds .real := polyBinomSplit_holds Interp.real

theorem polyBinomSplit_complex : polyBinomSplit.Holds .complex := polyBinomSplit_holds Interp.complex

theorem polyBinomBinomSplit_holds [CharZero 𝕜] (I : Interp 𝕜) :
    AntiderivRecHolds I "x" polyBinomBinomSplit.conditions polyBinomBinomSplit.body polyBinomBinomSplit.result polyBinomBinomSplit.integrals := by
  intro env hc t hF
  rcases hkm : I.toInt? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [polyBinomBinomSplit, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [polyBinomBinomSplit, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [polyBinomBinomSplit, Defined, eval, hkp] at h
  rcases hkq : I.toInt? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [polyBinomBinomSplit, Defined, eval, hkq] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [polyBinomBinomSplit, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      filter_upwards [hF] with w hw
      simp [polyBinomBinomSplit, Defined, eval, hkm, hkn, hkp, hkq] at hw ⊢
      tauto
  · exact Eventually.of_forall fun _ => by simp [polyBinomBinomSplit, Defined, recEnv]
  · simp only [polyBinomBinomSplit, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (polyBinomBinomSplit.integrals.map (·.1)) Φ "x" w)
        polyBinomBinomSplit.result) = fun w => env "A" * Φ "I1" w + env "B" * Φ "I2" w := by
      funext w; simp [polyBinomBinomSplit, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [polyBinomBinomSplit, eval]
    ring

theorem polyBinomBinomSplit_real : polyBinomBinomSplit.Holds .real := polyBinomBinomSplit_holds Interp.real

theorem polyBinomBinomSplit_complex : polyBinomBinomSplit.Holds .complex := polyBinomBinomSplit_holds Interp.complex


theorem powInvLinLog_holds [CharZero 𝕜] (I : Interp 𝕜) :
    AntiderivRecHolds I "x" powInvLinLog.conditions powInvLinLog.body powInvLinLog.result powInvLinLog.integrals := by
  intro env hc t hF
  have hmq := (hc (.eq (.var "m") (.var "q")) (by simp [powInvLinLog])).2.2
  simp [eval] at hmq
  rcases hkq : I.toInt? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [powInvLinLog, Defined, eval, hkq] at h
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [powInvLinLog, Defined, eval, hkp] at h
  have key : ∀ w : 𝕜, w ≠ 0 → w ^ kq * (env "d" + env "e" * w⁻¹) ^ kq = (env "e" + env "d" * w) ^ kq :=
    fun w hw => by rw [← mul_zpow]; congr 1; field_simp; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powInvLinLog, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [powInvLinLog, Defined, eval, toInt?_m1 I, hmq, hkq, hkp] at hw ⊢
    have hw0 : w ≠ 0 := by tauto
    refine ⟨fun hk h0 => ?_, by tauto⟩
    have h1 : env "d" + env "e" * w⁻¹ = 0 := by
      rw [show env "d" + env "e" * w⁻¹ = (env "e" + env "d" * w) * w⁻¹ by field_simp; ring,
        h0, zero_mul]
    tauto
  · exact Eventually.of_forall fun _ => by simp [powInvLinLog, Defined, recEnv]
  · simp only [powInvLinLog, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (powInvLinLog.integrals.map (·.1)) Φ "x" w)
        powInvLinLog.result) = Φ "I1" := by
      funext w; simp [powInvLinLog, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have ht0 : t ≠ 0 := by
      have h := hF.self_of_nhds
      simp [powInvLinLog, Defined, eval, toInt?_m1 I] at h
      tauto
    simp [powInvLinLog, eval, toInt?_m1 I, hmq, hkq, hkp]
    exact Or.inl (key t ht0).symm

theorem powInvLinLog_real : powInvLinLog.Holds .real := powInvLinLog_holds Interp.real

theorem powInvLinLog_complex : powInvLinLog.Holds .complex := powInvLinLog_holds Interp.complex

theorem powInvLinLog2_holds [CharZero 𝕜] (I : Interp 𝕜) :
    AntiderivRecHolds I "x" powInvLinLog2.conditions powInvLinLog2.body powInvLinLog2.result powInvLinLog2.integrals := by
  intro env hc t hF
  have hmq := (hc (.eq (.var "m") (.var "q")) (by simp [powInvLinLog2])).2.2
  simp [eval] at hmq
  rcases hkq : I.toInt? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [powInvLinLog2, Defined, eval, hkq] at h
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [powInvLinLog2, Defined, eval, hkp] at h
  have key : ∀ w : 𝕜, w ≠ 0 → w ^ kq * (env "d" + env "e" * w⁻¹) ^ kq = (env "e" + env "d" * w) ^ kq :=
    fun w hw => by rw [← mul_zpow]; congr 1; field_simp; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powInvLinLog2, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [powInvLinLog2, Defined, eval, toInt?_m1 I, hmq, hkq, hkp] at hw ⊢
    have hw0 : w ≠ 0 := by tauto
    refine ⟨fun hk h0 => ?_, by tauto⟩
    have h1 : env "d" + env "e" * w⁻¹ = 0 := by
      rw [show env "d" + env "e" * w⁻¹ = (env "e" + env "d" * w) * w⁻¹ by field_simp; ring,
        h0, zero_mul]
    tauto
  · exact Eventually.of_forall fun _ => by simp [powInvLinLog2, Defined, recEnv]
  · simp only [powInvLinLog2, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (powInvLinLog2.integrals.map (·.1)) Φ "x" w)
        powInvLinLog2.result) = Φ "I1" := by
      funext w; simp [powInvLinLog2, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have ht0 : t ≠ 0 := by
      have h := hF.self_of_nhds
      simp [powInvLinLog2, Defined, eval, toInt?_m1 I] at h
      tauto
    simp [powInvLinLog2, eval, toInt?_m1 I, hmq, hkq, hkp]
    exact Or.inl (key t ht0).symm

theorem powInvLinLog2_real : powInvLinLog2.Holds .real := powInvLinLog2_holds Interp.real

theorem powInvLinLog2_complex : powInvLinLog2.Holds .complex := powInvLinLog2_holds Interp.complex

theorem powInvLinLogLin_holds [CharZero 𝕜] (I : Interp 𝕜) :
    AntiderivRecHolds I "x" powInvLinLogLin.conditions powInvLinLogLin.body powInvLinLogLin.result powInvLinLogLin.integrals := by
  intro env hc t hF
  have hmq := (hc (.eq (.var "m") (.var "q")) (by simp [powInvLinLogLin])).2.2
  simp [eval] at hmq
  rcases hkq : I.toInt? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [powInvLinLogLin, Defined, eval, hkq] at h
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [powInvLinLogLin, Defined, eval, hkp] at h
  have key : ∀ w : 𝕜, w ≠ 0 → w ^ kq * (env "f" + env "g" * w⁻¹) ^ kq = (env "g" + env "f" * w) ^ kq :=
    fun w hw => by rw [← mul_zpow]; congr 1; field_simp; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powInvLinLogLin, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [powInvLinLogLin, Defined, eval, toInt?_m1 I, hmq, hkq, hkp] at hw ⊢
    have hw0 : w ≠ 0 := by tauto
    refine ⟨fun hk h0 => ?_, by tauto⟩
    have h1 : env "f" + env "g" * w⁻¹ = 0 := by
      rw [show env "f" + env "g" * w⁻¹ = (env "g" + env "f" * w) * w⁻¹ by field_simp; ring,
        h0, zero_mul]
    tauto
  · exact Eventually.of_forall fun _ => by simp [powInvLinLogLin, Defined, recEnv]
  · simp only [powInvLinLogLin, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (powInvLinLogLin.integrals.map (·.1)) Φ "x" w)
        powInvLinLogLin.result) = Φ "I1" := by
      funext w; simp [powInvLinLogLin, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have ht0 : t ≠ 0 := by
      have h := hF.self_of_nhds
      simp [powInvLinLogLin, Defined, eval, toInt?_m1 I] at h
      tauto
    simp [powInvLinLogLin, eval, toInt?_m1 I, hmq, hkq, hkp]
    exact Or.inl (key t ht0).symm

theorem powInvLinLogLin_real : powInvLinLogLin.Holds .real := powInvLinLogLin_holds Interp.real

theorem powInvLinLogLin_complex : powInvLinLogLin.Holds .complex := powInvLinLogLin_holds Interp.complex

end Proofs

end OSR.IntegrationRec18
