import OSR.IntegrationRec31

/-!
# Integration (RUBI): a trinomial with a negative exponent

RUBI 4.16.1 1.2.3.1 #1 rewrites `(a + b xⁿ + c x²ⁿ)^p` as
`x^(2 n p) (c + b x^(-n) + a x^(-2n))^p` when `n < 0` (`trinom_core`, valid for
`x ≠ 0`, which the integrand requires).  Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec32

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- (a + b x^n + c x^(2n))^p = x^(2 n p) (c + b x^(-n) + a x^(-2n))^p under the integral, for n < 0 -/
def trinomNegPow : CRule where
  id := "integration.trinomial_negative_power"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p"))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.pow (.app2 .add (.app2 .add (.var "c") (.app2 .mul (.var "b") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-2)) (.var "n"))))) (.var "p"))))]
  independent := ["a", "b", "c", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .gt (.int 0) (.var "n"),
    .int (.var "p")]
  priority := 6100
  description := "(a + b x^n + c x^(2n))^p = x^(2 n p) (c + b x^(-n) + a x^(-2n))^p under the integral, for n < 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p:1" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p.m#1"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

/-- `x^(2 n p) (c + b x^(-n) + a x^(-2n))^p = (a + b xⁿ + c x²ⁿ)^p` for `x ≠ 0`. -/
theorem trinom_core (w a b c : 𝕜) (n p : ℤ) (hw : w ≠ 0) :
    w ^ (2 * n * p) * (c + b * w ^ (-n) + a * w ^ (-(2 * n))) ^ p =
      (a + b * w ^ n + c * w ^ (2 * n)) ^ p := by
  have hn : w ^ n ≠ 0 := zpow_ne_zero n hw
  have h2 : w ^ (2 * n) = w ^ n * w ^ n := by rw [two_mul, zpow_add₀ hw]
  have h1 : c + b * w ^ (-n) + a * w ^ (-(2 * n)) =
      (a + b * w ^ n + c * w ^ (2 * n)) * (w ^ (2 * n))⁻¹ := by
    rw [zpow_neg, zpow_neg, h2]; field_simp; ring
  have hz : w ^ (2 * n * p) ≠ 0 := zpow_ne_zero _ hw
  rw [h1, mul_zpow, inv_zpow, ← zpow_mul]
  field_simp

theorem trinomNegPow_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" trinomNegPow.conditions trinomNegPow.body trinomNegPow.result
      trinomNegPow.integrals := by
  intro env hc t hF
  have hgt := hc (.gt (.int 0) (.var "n")) (by simp [trinomNegPow])
  have heq := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [trinomNegPow])
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [trinomNegPow, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [trinomNegPow, Defined, eval, hkp] at h
  have hn := toInt?_val hkn
  have hp := toInt?_val hkp
  have hn2 : env "n2" = 2 * env "n" := by simpa [Cond.Holds, Defined, eval] using heq.2.2
  have hneg : n < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgt
    rw [hn] at hgt
    have h' : I.lt ((n : ℚ) : 𝕜) ((0 : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgt
    exact_mod_cast (hlt _ _).1 h'
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have k1 : I.toInt? (2 * env "n" * env "p") = some (2 * n * p) := T _ _ (by rw [hn, hp]; push_cast; ring)
  have k2 : I.toInt? (-env "n") = some (-n) := T _ _ (by rw [hn]; push_cast; ring)
  have k3 : I.toInt? (-(2 * env "n")) = some (-(2 * n)) := T _ _ (by rw [hn]; push_cast; ring)
  have k4 : I.toInt? (2 * env "n") = some (2 * n) := T _ _ (by rw [hn]; push_cast; ring)
  have hD : ∀ w, Defined I (Function.update env "x" w) trinomNegPow.body →
      w ≠ 0 ∧ (p < 0 → env "a" + env "b" * w ^ n + env "c" * w ^ (2 * n) ≠ 0) := by
    intro w h
    simp [trinomNegPow, Defined, eval, hkn, hkp, hn2, k4] at h
    exact ⟨h.1.1 hneg, h.2⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [trinomNegPow, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hw0, hpz⟩ := hD w hw
    simp [Defined, eval, k1, k2, k3, hkp, hw0]
    intro hp0 h0
    apply hpz hp0
    have hn' : w ^ n ≠ 0 := zpow_ne_zero n hw0
    rw [show w ^ (2 * n) = w ^ n * w ^ n by rw [two_mul, zpow_add₀ hw0]] at h0 ⊢
    field_simp at h0
    linear_combination h0
  · exact Eventually.of_forall fun _ => by simp [trinomNegPow, Defined]
  · simp only [trinomNegPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (trinomNegPow.integrals.map (·.1)) Φ "x" w)
        trinomNegPow.result) = Φ "I1" := by
      funext w
      simp [trinomNegPow, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    obtain ⟨ht0, -⟩ := hD t hF.self_of_nhds
    simp [trinomNegPow, eval, k1, k2, k3, k4, hkn, hkp, hn2]
    simpa [zpow_neg] using trinom_core t (env "a") (env "b") (env "c") n p ht0

theorem trinomNegPow_real : trinomNegPow.Holds .real :=
  trinomNegPow_holds Interp.real Interp.real_lt_rat

theorem trinomNegPow_complex : trinomNegPow.Holds .complex :=
  trinomNegPow_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec32
