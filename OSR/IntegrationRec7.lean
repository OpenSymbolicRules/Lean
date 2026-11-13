import OSR.IntegrationRec6

/-!
# Integration (RUBI): proofs from the numerical backlog

Rules that a numerical check found to behave as identities where they are
defined, proved here over every interpretation having the needed
trigonometric identities.  The rule declarations are transcribed by a tool
and checked by the Integration repository's `scripts/v1_faithfulness.py`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec7

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- Split (d + e x)^q (a + b log(c x^n))^p / x -/
def powLinLogOverX : CRule where
  id := "integration.split_power_linear_log_over_x"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "d") (.var "I1")) (.app2 .mul (.var "e") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "p", "q"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .gt (.var "q") (.int 0),
    .int (.app2 .mul (.int 2) (.var "q"))]
  priority := 2400
  description := "Split (d + e x)^q (a + b log(c x^n))^p / x"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:15" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#15"

/-- Rewrite a + b cos^2 + c sin^2 by the double angle -/
def powOverTrigSq : CRule where
  id := "integration.power_over_trig_squares"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:71"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.app2 .mul (.var "c") (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.int (-1))))
  result := (.app2 .mul (.int 2) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.var "c")) (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.int (-1)) (.var "c"))) (.app1 .cos (.app2 .add (.app2 .mul (.int 2) (.var "d")) (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .add (.var "a") (.var "b")) (.int 0),
    .ne (.app2 .add (.var "a") (.var "c")) (.int 0)]
  priority := 2410
  description := "Rewrite a + b cos^2 + c sin^2 by the double angle"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:71" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#71"

/-- (e x)^m sin(c + d x^n) by parts for m < -1 -/
def powSinPowBack : CRule where
  id := "integration.power_sin_power_by_parts"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:35"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "n")) (.pow (.app2 .mul (.pow (.var "e") (.var "n")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 2420
  description := "(e x)^m sin(c + d x^n) by parts for m < -1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:35" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#35"

/-- (e x)^m cos(c + d x^n) by parts for m < -1 -/
def powCosPowBack : CRule where
  id := "integration.power_cos_power_by_parts"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:36"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "n")) (.pow (.app2 .mul (.pow (.var "e") (.var "n")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 2430
  description := "(e x)^m cos(c + d x^n) by parts for m < -1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:36" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#36"

/-- Integrate (a + b log(c x^n))^p (d + e log(f x^r))^q by parts -/
def logPowLogPow : CRule where
  id := "integration.power_log_times_power_log"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "r")))))) (.var "q")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "r")))))) (.var "q"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "q")) (.var "r")) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "r")))))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "r")))))) (.var "q"))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "r", "p", "q"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .int (.var "q"),
    .gt (.var "q") (.int 0)]
  priority := 2440
  description := "Integrate (a + b log(c x^n))^p (d + e log(f x^r))^q by parts"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:24" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#24"

/-- Integrate (d + e x^2)^q (a + b log(c x^n)) by parts -/
def quadPowLog : CRule where
  id := "integration.quadratic_power_log_by_parts"; legacyId := some "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.pow (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "q")) (.pow (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))]
  independent := ["a", "b", "c", "d", "e", "n", "q"]
  conditions := [.gt (.var "q") (.int 0)]
  priority := 2450
  description := "Integrate (d + e x^2)^q (a + b log(c x^n)) by parts"
  provenance := migrated "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:8" "3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p.m#8"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

private theorem toInt?_m1 (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_2 (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

/-- `(d + e x)^q = d (d + e x)^(q-1) + e x (d + e x)^(q-1)` for `q ≥ 1`. -/
theorem powLinLogOverX_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" powLinLogOverX.conditions powLinLogOverX.body powLinLogOverX.result
      powLinLogOverX.integrals := by
  intro env hc t hF
  have hgt := hc (.gt (.var "q") (.int 0)) (by simp [powLinLogOverX])
  rcases hkq : I.toInt? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [powLinLogOverX, Defined, eval, hkq] at h
  have hq := toInt?_val hkq
  have hpos : 0 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgt
    rw [hq] at hgt
    have h' : I.lt ((0 : ℚ) : 𝕜) ((q : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgt
    exact_mod_cast (hlt _ _).1 h'
  have hq1 : I.toInt? (env "q" + -1) = some (q - 1) :=
    (I.toInt?_eq _ _).2 (by rw [hq]; push_cast; ring)
  have hq1n : ¬ q - 1 < 0 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powLinLogOverX, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp [powLinLogOverX, Defined, eval, hkq, hq1, hq1n] at hw ⊢
      exact ⟨hw.1.2, hw.2⟩
    · filter_upwards [hF] with w hw
      simp [powLinLogOverX, Defined, eval, hkq, hq1, hq1n] at hw ⊢
      exact hw.1.2
  · exact Eventually.of_forall fun _ => by simp [powLinLogOverX, Defined]
  · simp only [powLinLogOverX, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have ht := hF.self_of_nhds
    have hfun : (fun w => eval I (recEnv env (powLinLogOverX.integrals.map (·.1)) Φ "x" w)
        powLinLogOverX.result) = fun w => env "d" * Φ "I1" w + env "e" * Φ "I2" w := by
      funext w
      simp [powLinLogOverX, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    have ht0 : t ≠ 0 := by
      simp [powLinLogOverX, Defined, eval, toInt?_m1 I] at ht
      exact ht.2
    simp [powLinLogOverX, eval, hkq, hq1, toInt?_m1 I]
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, q = (j : ℤ) + 1 := ⟨(q - 1).toNat, by omega⟩
    generalize (match I.toInt? (env "p") with
      | some n => (env "a" + env "b" * I.ln (env "c" * match I.toInt? (env "n") with
          | some n => t ^ n
          | none => 0)) ^ n
      | none => 0) = P
    rw [add_sub_cancel_right, show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, zpow_natCast, pow_succ]
    field_simp

theorem powLinLogOverX_real : powLinLogOverX.Holds .real :=
  powLinLogOverX_holds Interp.real Interp.real_lt_rat

theorem powLinLogOverX_complex : powLinLogOverX.Holds .complex :=
  powLinLogOverX_holds Interp.complex Interp.complex_lt_rat

/-- Integration by parts: `∫ (e x)^m sin(c + d xⁿ)`, for `m < -1` and `n > 0`. -/
theorem powSinPowBack_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) :
    AntiderivRecHolds I "x" powSinPowBack.conditions powSinPowBack.body powSinPowBack.result
      powSinPowBack.integrals := by
  intro env hc t hF
  have hgm := hc (.gt (.int (-1)) (.var "m")) (by simp [powSinPowBack])
  have hgn := hc (.gt (.var "n") (.int 0)) (by simp [powSinPowBack])
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [powSinPowBack, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [powSinPowBack, Defined, eval, hkn] at h
  have hm := toInt?_val hkm
  have hn := toInt?_val hkn
  have hmlt : m < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgm
    rw [hm] at hgm
    have h' : I.lt ((m : ℚ) : 𝕜) ((-1 : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast]; push_cast; simpa using hgm
    exact_mod_cast (hlt _ _).1 h'
  have hnpos : 0 < n := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgn
    rw [hn] at hgn
    have h' : I.lt ((0 : ℚ) : 𝕜) ((n : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgn
    exact_mod_cast (hlt _ _).1 h'
  have hm1 : I.toInt? (env "m" + 1) = some (m + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hmn : I.toInt? (env "m" + env "n") = some (m + n) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hn]; push_cast; ring)
  have hm1c : I.toInt? ((m : 𝕜) + 1) = some (m + 1) := (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hnc : I.toInt? (n : 𝕜) = some n := I.toInt?_cast n
  have hmc : I.toInt? (m : 𝕜) = some m := I.toInt?_cast m
  have hmnc : I.toInt? ((m : 𝕜) + (n : 𝕜)) = some (m + n) := (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) powSinPowBack.body →
      env "e" ≠ 0 ∧ w ≠ 0 := by
    intro w h
    simp [powSinPowBack, Defined, eval, hkm, hkn] at h
    exact h.1 (by omega)
  obtain ⟨he, ht0⟩ := hD t hF.self_of_nhds
  have hm1' : (m : 𝕜) + 1 ≠ 0 := by
    have : (m : 𝕜) + 1 = ((m + 1 : ℤ) : 𝕜) := by push_cast; ring
    rw [this]; exact_mod_cast (show m + 1 ≠ 0 by omega)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powSinPowBack, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨he', hw0⟩ := hD w hw
    simp [Defined, eval, hm, hn, hmnc, hnc, he', hw0]
  · filter_upwards [hF] with w hw
    obtain ⟨he', hw0⟩ := hD w hw
    simp [powSinPowBack, Defined, eval, recEnv, toInt?_m1 I, he', hw0, hm, hn, hm1c, hnc, hm1',
      zpow_ne_zero]
  · simp only [powSinPowBack, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (powSinPowBack.integrals.map (·.1)) Φ "x" w)
        powSinPowBack.result) = fun w =>
          (env "e" * w) ^ (m + 1) * I.sin (env "c" + env "d" * w ^ n) * (env "e" * ((m : 𝕜) + 1))⁻¹ +
          -1 * env "d" * (n : 𝕜) * (env "e" ^ n * ((m : 𝕜) + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [powSinPowBack, eval, recEnv, toInt?_m1 I, hm, hn, hm1c, hnc]
    rw [hfun]
    have hew : env "e" * t ≠ 0 := mul_ne_zero he ht0
    have hA : HasDerivAt (fun w => (env "e" * w) ^ (m + 1))
        (((m : 𝕜) + 1) * (env "e" * t) ^ m * env "e") t := by
      have := (hasDerivAt_zpow (m + 1) (env "e" * t) (Or.inl hew)).comp t
        ((hasDerivAt_id t).const_mul (env "e"))
      simp only [mul_one, add_sub_cancel_right] at this
      convert this using 1 <;> first | rfl | (push_cast; ring)
    have hB : HasDerivAt (fun w => I.sin (env "c" + env "d" * w ^ n))
        (I.cos (env "c" + env "d" * t ^ n) * (env "d" * ((n : 𝕜) * t ^ (n - 1)))) t := by
      have := (hs (env "c" + env "d" * t ^ n)).comp t
        (((hasDerivAt_zpow n t (Or.inl ht0)).const_mul (env "d")).const_add (env "c"))
      convert this using 1 <;> first | rfl | (push_cast; ring)
    refine (((hA.mul hB).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp [powSinPowBack, eval, hm, hn, hmnc, hnc, hmc]
    simp only [zpow_add₀ hew, mul_zpow, zpow_sub_one₀ ht0, zpow_one]
    field_simp
    ring

theorem powSinPowBack_real : powSinPowBack.Holds .real :=
  powSinPowBack_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin

theorem powSinPowBack_complex : powSinPowBack.Holds .complex :=
  powSinPowBack_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin

/-- Integration by parts: `∫ (e x)^m cos(c + d xⁿ)`, for `m < -1` and `n > 0`. -/
theorem powCosPowBack_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u) :
    AntiderivRecHolds I "x" powCosPowBack.conditions powCosPowBack.body powCosPowBack.result
      powCosPowBack.integrals := by
  intro env hc t hF
  have hgm := hc (.gt (.int (-1)) (.var "m")) (by simp [powCosPowBack])
  have hgn := hc (.gt (.var "n") (.int 0)) (by simp [powCosPowBack])
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [powCosPowBack, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [powCosPowBack, Defined, eval, hkn] at h
  have hm := toInt?_val hkm
  have hn := toInt?_val hkn
  have hmlt : m < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgm
    rw [hm] at hgm
    have h' : I.lt ((m : ℚ) : 𝕜) ((-1 : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast]; push_cast; simpa using hgm
    exact_mod_cast (hlt _ _).1 h'
  have hnpos : 0 < n := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgn
    rw [hn] at hgn
    have h' : I.lt ((0 : ℚ) : 𝕜) ((n : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgn
    exact_mod_cast (hlt _ _).1 h'
  have hm1 : I.toInt? (env "m" + 1) = some (m + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hm]; push_cast; ring)
  have hmn : I.toInt? (env "m" + env "n") = some (m + n) :=
    (I.toInt?_eq _ _).2 (by rw [hm, hn]; push_cast; ring)
  have hm1c : I.toInt? ((m : 𝕜) + 1) = some (m + 1) := (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hnc : I.toInt? (n : 𝕜) = some n := I.toInt?_cast n
  have hmc : I.toInt? (m : 𝕜) = some m := I.toInt?_cast m
  have hmnc : I.toInt? ((m : 𝕜) + (n : 𝕜)) = some (m + n) := (I.toInt?_eq _ _).2 (by push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) powCosPowBack.body →
      env "e" ≠ 0 ∧ w ≠ 0 := by
    intro w h
    simp [powCosPowBack, Defined, eval, hkm, hkn] at h
    exact h.1 (by omega)
  obtain ⟨he, ht0⟩ := hD t hF.self_of_nhds
  have hm1' : (m : 𝕜) + 1 ≠ 0 := by
    have : (m : 𝕜) + 1 = ((m + 1 : ℤ) : 𝕜) := by push_cast; ring
    rw [this]; exact_mod_cast (show m + 1 ≠ 0 by omega)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powCosPowBack, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨he', hw0⟩ := hD w hw
    simp [Defined, eval, hm, hn, hmnc, hnc, he', hw0]
  · filter_upwards [hF] with w hw
    obtain ⟨he', hw0⟩ := hD w hw
    simp [powCosPowBack, Defined, eval, recEnv, toInt?_m1 I, he', hw0, hm, hn, hm1c, hnc, hm1',
      zpow_ne_zero]
  · simp only [powCosPowBack, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (powCosPowBack.integrals.map (·.1)) Φ "x" w)
        powCosPowBack.result) = fun w =>
          (env "e" * w) ^ (m + 1) * I.cos (env "c" + env "d" * w ^ n) * (env "e" * ((m : 𝕜) + 1))⁻¹ +
          env "d" * (n : 𝕜) * (env "e" ^ n * ((m : 𝕜) + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [powCosPowBack, eval, recEnv, toInt?_m1 I, hm, hn, hm1c, hnc]
    rw [hfun]
    have hew : env "e" * t ≠ 0 := mul_ne_zero he ht0
    have hA : HasDerivAt (fun w => (env "e" * w) ^ (m + 1))
        (((m : 𝕜) + 1) * (env "e" * t) ^ m * env "e") t := by
      have := (hasDerivAt_zpow (m + 1) (env "e" * t) (Or.inl hew)).comp t
        ((hasDerivAt_id t).const_mul (env "e"))
      simp only [mul_one, add_sub_cancel_right] at this
      convert this using 1 <;> first | rfl | (push_cast; ring)
    have hB : HasDerivAt (fun w => I.cos (env "c" + env "d" * w ^ n))
        (-I.sin (env "c" + env "d" * t ^ n) * (env "d" * ((n : 𝕜) * t ^ (n - 1)))) t := by
      have := (hs (env "c" + env "d" * t ^ n)).comp t
        (((hasDerivAt_zpow n t (Or.inl ht0)).const_mul (env "d")).const_add (env "c"))
      convert this using 1 <;> first | rfl | (push_cast; ring)
    refine (((hA.mul hB).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp [powCosPowBack, eval, hm, hn, hmnc, hnc, hmc]
    simp only [zpow_add₀ hew, mul_zpow, zpow_sub_one₀ ht0, zpow_one]
    field_simp
    ring

theorem powCosPowBack_real : powCosPowBack.Holds .real :=
  powCosPowBack_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_cos

theorem powCosPowBack_complex : powCosPowBack.Holds .complex :=
  powCosPowBack_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_cos

/-- `2 (a + b cos² u + c sin² u) = 2a + b + c + (b - c) cos 2u`. -/
theorem powOverTrigSq_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hpy : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1)
    (hc2 : ∀ u : 𝕜, I.cos (2 * u) = 2 * I.cos u ^ 2 - 1) :
    AntiderivRecHolds I "x" powOverTrigSq.conditions powOverTrigSq.body powOverTrigSq.result
      powOverTrigSq.integrals := by
  intro env _ t hF
  have h2 : (2 : 𝕜) ≠ 0 := two_ne_zero
  have key : ∀ w : 𝕜, 2 * env "a" + env "b" + env "c" +
      (env "b" + -env "c") * I.cos (2 * env "d" + 2 * env "e" * w) =
      2 * (env "a" + env "b" * I.cos (env "d" + env "e" * w) ^ 2 +
        env "c" * I.sin (env "d" + env "e" * w) ^ 2) := by
    intro w
    have h := hc2 (env "d" + env "e" * w)
    have hp := hpy (env "d" + env "e" * w)
    rw [show 2 * env "d" + 2 * env "e" * w = 2 * (env "d" + env "e" * w) by ring, h]
    linear_combination (-2 * env "c") * hp
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powOverTrigSq, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [powOverTrigSq, Defined, eval, toInt?_m1 I, toInt?_2 I] at hw ⊢
    exact ⟨hw.1, by rw [key]; exact mul_ne_zero h2 hw.2⟩
  · exact Eventually.of_forall fun _ => by simp [powOverTrigSq, Defined]
  · simp only [powOverTrigSq, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (powOverTrigSq.integrals.map (·.1)) Φ "x" w)
        powOverTrigSq.result) = fun w => 2 * Φ "I1" w := by
      funext w
      simp [powOverTrigSq, eval, recEnv]
    rw [hfun]
    refine (hΦ.const_mul _).congr_deriv ?_
    have ht := hF.self_of_nhds
    simp [powOverTrigSq, eval, toInt?_m1 I, toInt?_2 I]
    rw [key]
    generalize (match I.toInt? (env "m") with
      | some n => (env "f" + env "g" * t) ^ n
      | none => 0) = M
    rw [mul_inv]
    linear_combination (M * (env "a" + env "b" * I.cos (env "d" + env "e" * t) ^ 2 +
      env "c" * I.sin (env "d" + env "e" * t) ^ 2)⁻¹) * mul_inv_cancel₀ h2

theorem powOverTrigSq_real : powOverTrigSq.Holds .real :=
  powOverTrigSq_holds Interp.real (fun u => Real.sin_sq_add_cos_sq u) (fun u => Real.cos_two_mul u)

theorem powOverTrigSq_complex : powOverTrigSq.Holds .complex :=
  powOverTrigSq_holds Interp.complex (fun u => Complex.sin_sq_add_cos_sq u)
    (fun u => Complex.cos_two_mul u)

end Proofs

section Real

/-- `d/dw log(c wⁿ) = n/t` where `c tⁿ > 0` (at `t = 0` this forces `n = 0`). -/
theorem hasDerivAt_log_monomial (c t : ℝ) (n : ℤ) (h : 0 < c * t ^ n) :
    HasDerivAt (fun w => Real.log (c * w ^ n)) ((n : ℝ) / t) t := by
  rcases eq_or_ne t 0 with rfl | ht
  · have hn : n = 0 := by
      by_contra hn
      rw [zero_zpow n hn, mul_zero] at h
      exact lt_irrefl 0 h
    subst hn
    simpa using hasDerivAt_const (0 : ℝ) (Real.log c)
  · have hc : c ≠ 0 := by rintro rfl; simp at h
    have := ((hasDerivAt_zpow n t (Or.inl ht)).const_mul c).log h.ne'
    convert this using 1
    rw [zpow_sub_one₀ ht]
    field_simp

/-- `t (n/t) = n` where `c tⁿ > 0`. -/
theorem mul_div_of_log_monomial (c t : ℝ) (n : ℤ) (h : 0 < c * t ^ n) :
    t * ((n : ℝ) / t) = n := by
  rcases eq_or_ne t 0 with rfl | ht
  · have hn : n = 0 := by
      by_contra hn
      rw [zero_zpow n hn, mul_zero] at h
      exact lt_irrefl 0 h
    simp [hn]
  · field_simp

private theorem iv_val {v : ℝ} {k : ℤ} (h : intValue? v = some k) : v = (k : ℝ) :=
  (intValue?_eq _ _).1 h

/-- Integration by parts for a product of two powers of logarithms, over ℝ. -/
theorem logPowLogPow_real : logPowLogPow.Holds .real := by
  show AntiderivRecHolds Interp.real "x" logPowLogPow.conditions logPowLogPow.body
    logPowLogPow.result logPowLogPow.integrals
  intro env hc t hF
  have hgp := hc (.gt (.var "p") (.int 0)) (by simp [logPowLogPow])
  have hgq := hc (.gt (.var "q") (.int 0)) (by simp [logPowLogPow])
  have hip := hc (.int (.var "p")) (by simp [logPowLogPow])
  have hiq := hc (.int (.var "q")) (by simp [logPowLogPow])
  obtain ⟨-, p, hkp⟩ := hip
  obtain ⟨-, q, hkq⟩ := hiq
  simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgp hgq hkp hkq
  have hp : 0 < p := by rw [iv_val hkp] at hgp; exact_mod_cast hgp
  have hq : 0 < q := by rw [iv_val hkq] at hgq; exact_mod_cast hgq
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [logPowLogPow, Defined, eval, Interp.real, hkn] at h
  rcases hkr : intValue? (env "r") with _ | r
  · exfalso
    have h := hF.self_of_nhds
    simp [logPowLogPow, Defined, eval, Interp.real, hkr] at h
  have hp1 : intValue? (env "p" + -1) = some (p - 1) :=
    (intValue?_eq _ _).2 (by rw [iv_val hkp]; push_cast; ring)
  have hq1 : intValue? (env "q" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [iv_val hkq]; push_cast; ring)
  have hp1n : ¬ p - 1 < 0 := by omega
  have hq1n : ¬ q - 1 < 0 := by omega
  have hpn : ¬ p < 0 := by omega
  have hqn : ¬ q < 0 := by omega
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) logPowLogPow.body →
      (n < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ n ∧ (r < 0 → w ≠ 0) ∧ 0 < env "f" * w ^ r := by
    intro w h
    simp [logPowLogPow, Defined, eval, Interp.real, hkn, hkr, hkp, hkq, hpn, hqn] at h
    exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [logPowLogPow, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨h1, h2, h3, h4⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkn, hkr, hkp, hkq, hp1, hq1, hpn, hqn, hp1n, hq1n]
      exact ⟨⟨h1, h2⟩, h3, h4⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hD w hw
    simp [logPowLogPow, Defined, eval, Interp.real, recEnv, hkn, hkr, hkp, hkq, hpn, hqn]
    exact ⟨⟨h1, h2⟩, h3, h4⟩
  · simp only [logPowLogPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨-, hc0, -, hf0⟩ := hD t hF.self_of_nhds
    set L1 : ℝ → ℝ := fun w => env "a" + env "b" * Real.log (env "c" * w ^ n) with hL1
    set L2 : ℝ → ℝ := fun w => env "d" + env "e" * Real.log (env "f" * w ^ r) with hL2
    have hd1 : HasDerivAt L1 (env "b" * ((n : ℝ) / t)) t :=
      ((hasDerivAt_log_monomial _ t n hc0).const_mul _).const_add _
    have hd2 : HasDerivAt L2 (env "e" * ((r : ℝ) / t)) t :=
      ((hasDerivAt_log_monomial _ t r hf0).const_mul _).const_add _
    have hP : HasDerivAt (fun w => L1 w ^ p) ((p : ℝ) * L1 t ^ (p - 1) * (env "b" * ((n : ℝ) / t))) t :=
      (hasDerivAt_zpow p (L1 t) (Or.inr hp.le)).comp t hd1
    have hQ : HasDerivAt (fun w => L2 w ^ q) ((q : ℝ) * L2 t ^ (q - 1) * (env "e" * ((r : ℝ) / t))) t :=
      (hasDerivAt_zpow q (L2 t) (Or.inr hq.le)).comp t hd2
    have key := ((((hasDerivAt_id t).mul hP).mul hQ).add (hΦ1.const_mul
      (-1 * env "e" * env "q" * env "r"))).add (hΦ2.const_mul (-1 * env "b" * env "n" * env "p"))
    convert key using 1
    · funext w
      simp [logPowLogPow, eval, recEnv, Interp.real, hkn, hkr, hkp, hkq, hL1, hL2]
    · simp [logPowLogPow, eval, Interp.real, hkn, hkr, hkp, hkq, hp1, hq1, hL1, hL2]
      have e1 := mul_div_of_log_monomial _ t n hc0
      have e2 := mul_div_of_log_monomial _ t r hf0
      rw [iv_val hkn, iv_val hkr, iv_val hkp, iv_val hkq]
      generalize env "a" + env "b" * Real.log (env "c" * t ^ n) = A
      generalize env "d" + env "e" * Real.log (env "f" * t ^ r) = B
      linear_combination (-(p : ℝ) * env "b" * A ^ (p - 1) * B ^ q) * e1 +
        (-(q : ℝ) * env "e" * A ^ p * B ^ (q - 1)) * e2

/-- Integration by parts for `(d + e x²)^q (a + b log(c xⁿ))`, `q ≥ 1`, over ℝ. -/
theorem quadPowLog_real : quadPowLog.Holds .real := by
  show AntiderivRecHolds Interp.real "x" quadPowLog.conditions quadPowLog.body
    quadPowLog.result quadPowLog.integrals
  intro env hc t hF
  have hgq := hc (.gt (.var "q") (.int 0)) (by simp [quadPowLog])
  simp only [Cond.Holds, Defined, eval, Interp.real, true_and] at hgq
  rcases hkq : intValue? (env "q") with _ | q
  · exfalso
    have h := hF.self_of_nhds
    simp [quadPowLog, Defined, eval, Interp.real, hkq] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [quadPowLog, Defined, eval, Interp.real, hkn] at h
  have hq : 0 < q := by rw [iv_val hkq] at hgq; exact_mod_cast hgq
  have hq1 : intValue? (env "q" + -1) = some (q - 1) :=
    (intValue?_eq _ _).2 (by rw [iv_val hkq]; push_cast; ring)
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hq1n : ¬ q - 1 < 0 := by omega
  have hqn : ¬ q < 0 := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h2q : (2 : ℝ) * q + 1 ≠ 0 := (by linarith : (0 : ℝ) < 2 * q + 1).ne'
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) quadPowLog.body →
      (n < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ n := by
    intro w h
    simp [quadPowLog, Defined, eval, Interp.real, hkn, hkq, hqn, h2] at h
    exact h
  have h2q' : 2 * env "q" + 1 ≠ 0 := by rw [iv_val hkq]; exact h2q
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [quadPowLog, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      obtain ⟨h1, h1'⟩ := hD w hw
      simp [Defined, eval, Interp.real, hkn, hkq, hq1, hqn, hq1n, h2]
      try exact ⟨h1, h1'⟩
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h1'⟩ := hD w hw
    simp [quadPowLog, Defined, eval, Interp.real, recEnv, hkn, hkq, hqn, h2, hm1, h2q']
    try exact ⟨h1, h1'⟩
  · simp only [quadPowLog, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨-, hc0⟩ := hD t hF.self_of_nhds
    set Q : ℝ → ℝ := fun w => env "d" + env "e" * w ^ 2 with hQdef
    set L : ℝ → ℝ := fun w => env "a" + env "b" * Real.log (env "c" * w ^ n) with hLdef
    have hQ : HasDerivAt Q (env "e" * ((2 : ℕ) * t ^ (2 - 1))) t :=
      ((hasDerivAt_pow 2 t).const_mul _).const_add _
    have hQq : HasDerivAt (fun w => Q w ^ q) ((q : ℝ) * Q t ^ (q - 1) *
        (env "e" * ((2 : ℕ) * t ^ (2 - 1)))) t :=
      (hasDerivAt_zpow q (Q t) (Or.inr hq.le)).comp t hQ
    have hL : HasDerivAt L (env "b" * ((n : ℝ) / t)) t :=
      ((hasDerivAt_log_monomial _ t n hc0).const_mul _).const_add _
    have key := (((((hasDerivAt_id t).mul hQq).mul hL).mul_const (2 * env "q" + 1)⁻¹).add
      (hΦ1.const_mul (-1 * env "b" * env "n" * (2 * env "q" + 1)⁻¹))).add
      (hΦ2.const_mul (2 * env "d" * env "q" * (2 * env "q" + 1)⁻¹))
    convert key using 1
    · funext w
      simp [quadPowLog, eval, recEnv, Interp.real, hkn, hkq, h2, hm1, hQdef, hLdef]
    · simp [quadPowLog, eval, Interp.real, hkn, hkq, hq1, h2, hm1, hQdef, hLdef]
      have e1 := mul_div_of_log_monomial _ t n hc0
      have hI := mul_inv_cancel₀ h2q
      simp only [iv_val hkn, iv_val hkq]
      generalize (2 * (q : ℝ) + 1)⁻¹ = J at hI ⊢
      generalize env "a" + env "b" * Real.log (env "c" * t ^ n) = B
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, q = (j : ℤ) + 1 := ⟨(q - 1).toNat, by omega⟩
      rw [add_sub_cancel_right, show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, zpow_natCast] at *
      push_cast at hI ⊢
      linear_combination (-((env "d" + env "e" * t ^ 2) ^ (j + 1) * B)) * hI +
        (-(env "b" * (env "d" + env "e" * t ^ 2) ^ (j + 1) * J)) * e1

end Real

end OSR.IntegrationRec7
