import OSR.IntegrationRec21

/-!
# Integration (RUBI): a scaling rule under a logarithm

RUBI 4.16.1 3.1.2 #8 rewrites `∫ (d x)^m / log(c xⁿ)` as
`(d x)^m / x^m · ∫ x^m / log(c xⁿ)` when `m = n - 1`.  The factor
`(d x)^m / x^m` equals `d^m` wherever `x ≠ 0` (`mul_zpow`), and the integrand
is never defined at `x = 0`: either `(d x)^m` has a negative exponent there,
or `n = m + 1 ≥ 1` and `log(c · 0ⁿ) = log 0` is undefined.  The rule holds
over ℝ and ℂ; its residual integrand shares the logarithm of the integrand,
so no property of the complex logarithm is needed.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec22

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- (d x)^m = d^m x^m under the integral of (d x)^m/log(c x^n) -/
def monoOverLogScale : CRule where
  id := "integration.monomial_over_log_scale"; legacyId := some "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.pow (.var "x") (.var "m")) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.int (-1)))))]
  independent := ["c", "d", "m", "n"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))]
  priority := 4200
  description := "(d x)^m = d^m x^m under the integral of (d x)^m/log(c x^n)"
  provenance := migrated "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:8" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#8"

/-- ∫ sin² u/(c sin u + d x cos u)² in closed form when a c + d = 0 -/
def sinSqOverQuotSq : CRule where
  id := "integration.sin_square_over_sin_x_cos_square"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:80"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app1 .sin (.app2 .mul (.var "a") (.var "x"))) (.int 2)) (.pow (.pow (.app2 .add (.app2 .mul (.var "c") (.app1 .sin (.app2 .mul (.var "a") (.var "x")))) (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app1 .cos (.app2 .mul (.var "a") (.var "x"))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.var "d") (.int 2)) (.var "x")) (.int (-1)))) (.app2 .mul (.app1 .sin (.app2 .mul (.var "a") (.var "x"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "x")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app1 .cos (.app2 .mul (.var "a") (.var "x")))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .mul (.var "a") (.var "x")))))) (.int (-1)))))
  independent := ["a", "c", "d"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.var "d")) (.int 0)]
  priority := 4210
  description := "∫ sin² u/(c sin u + d x cos u)² in closed form when a c + d = 0"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:80" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#80"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

/-- **3.1.2 #8.** -/
theorem monoOverLogScale_holds [CharZero 𝕜] (I : Interp 𝕜) (hln : ¬ I.lnDefined 0) :
    AntiderivRecHolds I "x" monoOverLogScale.conditions monoOverLogScale.body
      monoOverLogScale.result monoOverLogScale.integrals := by
  intro env hc t hF
  have heq := hc (.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))
    (by simp [monoOverLogScale])
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [monoOverLogScale, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [monoOverLogScale, Defined, eval, hkn] at h
  have hmn : m = n - 1 := by
    have h := heq.2.2
    simp [eval] at h
    rw [toInt?_val hkm, toInt?_val hkn] at h
    have h' : ((m : ℤ) : 𝕜) = ((n - 1 : ℤ) : 𝕜) := by push_cast; linear_combination h
    exact_mod_cast h'
  have hw0 : ∀ w, Defined I (Function.update env "x" w) monoOverLogScale.body → w ≠ 0 := by
    intro w h hw
    subst hw
    simp [monoOverLogScale, Defined, eval, hkm, hkn] at h
    obtain ⟨hm, ⟨-, hl⟩, -⟩ := h
    have hn : n ≠ 0 := by omega
    rw [zero_zpow n hn, mul_zero] at hl
    exact hln hl
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [monoOverLogScale, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h0 := hw0 w hw
    refine ⟨?_, hw.2⟩
    simp [Defined, eval, hkm, h0]
  · filter_upwards [hF] with w hw
    have h0 := hw0 w hw
    have h1 := hw.1
    simp [monoOverLogScale, Defined, eval, recEnv, hkm, h0, toInt?_neg_one] at h1 ⊢
    refine ⟨fun hm hd => ?_, zpow_ne_zero m h0⟩
    simp [hd] at h1
    omega
  · simp only [monoOverLogScale, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun v => eval I (recEnv env (monoOverLogScale.integrals.map (·.1)) Φ "x" v)
        monoOverLogScale.result) =ᶠ[𝓝 t] fun v => env "d" ^ m * Φ "I1" v := by
      filter_upwards [hF] with w hw
      have h0 := hw0 w hw
      simp [monoOverLogScale, eval, recEnv, hkm, toInt?_neg_one]
      rw [mul_zpow]
      field_simp [zpow_ne_zero m h0]
      try simp
    refine ((hΦ.const_mul _).congr_deriv ?_).congr_of_eventuallyEq hfun
    simp [monoOverLogScale, eval, hkm, toInt?_neg_one]
    rw [mul_zpow]
    ring

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

/-- **4.7.9 #80**, a closed-form antiderivative. -/
theorem sinSqOverQuotSq_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u)
    (hcd : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hP : ∀ u, I.sin u ^ 2 + I.cos u ^ 2 = 1) (hsin0 : I.sin 0 = 0) :
    AntiderivHoldsUnder I "x" sinSqOverQuotSq.conditions sinSqOverQuotSq.body
      sinSqOverQuotSq.result := by
  intro env hc t hF
  have heq := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.var "d")) (.int 0))
    (by simp [sinSqOverQuotSq])
  have hac : env "a" * env "c" + env "d" = 0 := by
    simpa [Cond.Holds, Defined, eval] using heq.2.2
  have hQ : ∀ w, Defined I (Function.update env "x" w) sinSqOverQuotSq.body →
      env "c" * I.sin (env "a" * w) + env "d" * w * I.cos (env "a" * w) ≠ 0 := by
    intro w h
    simp [sinSqOverQuotSq, Defined, eval, toInt?_two, toInt?_neg_one] at h
    exact h
  have ht0 : t ≠ 0 := by
    intro h0
    have hq := hQ t hF.self_of_nhds
    rw [h0] at hq
    simp [hsin0] at hq
  have hd0 : env "d" ≠ 0 := by
    intro hd
    have hq := hQ t hF.self_of_nhds
    rw [hd] at hac hq
    have : env "a" = 0 ∨ env "c" = 0 := by simpa using hac
    rcases this with ha | hc0
    · rw [ha] at hq; simp [hsin0] at hq
    · rw [hc0] at hq; simp at hq
  have ha0 : env "a" ≠ 0 := by
    intro ha
    apply hd0
    rw [ha] at hac
    simpa using hac
  refine ⟨?_, ?_⟩
  · filter_upwards [hF, eventually_ne_nhds ht0] with w hw hw0
    have hq := hQ w hw
    simp [sinSqOverQuotSq, Defined, eval, toInt?_two, toInt?_neg_one, hd0, ha0, hw0]
    rwa [add_comm] at hq
  · have hfun : (fun w => eval I (Function.update env "x" w) sinSqOverQuotSq.result) = fun w =>
        (env "d" ^ 2 * w)⁻¹ + I.sin (env "a" * w) * (env "a" * env "d" * w *
          (env "d" * w * I.cos (env "a" * w) + env "c" * I.sin (env "a" * w)))⁻¹ := by
      funext w
      simp [sinSqOverQuotSq, eval, toInt?_two, toInt?_neg_one]
    rw [hfun]
    have hSd : ∀ w, HasDerivAt (fun w => I.sin (env "a" * w)) (I.cos (env "a" * w) * env "a") w :=
      fun w => by
        have h := (hs (env "a" * w)).comp w ((hasDerivAt_id' w).const_mul (env "a"))
        simp only [mul_one] at h
        exact h
    have hCd : ∀ w, HasDerivAt (fun w => I.cos (env "a" * w)) (-I.sin (env "a" * w) * env "a") w :=
      fun w => by
        have h := (hcd (env "a" * w)).comp w ((hasDerivAt_id' w).const_mul (env "a"))
        simp only [mul_one] at h
        exact h
    have hq := hQ t hF.self_of_nhds
    have hR : env "d" * t * I.cos (env "a" * t) + env "c" * I.sin (env "a" * t) ≠ 0 := by
      rwa [add_comm] at hq
    have hden1 : env "d" ^ 2 * t ≠ 0 := mul_ne_zero (pow_ne_zero 2 hd0) ht0
    have hden2 : env "a" * env "d" * t *
        (env "d" * t * I.cos (env "a" * t) + env "c" * I.sin (env "a" * t)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 hd0) ht0) hR
    have hA := ((hasDerivAt_id t).const_mul (env "d" ^ 2)).inv hden1
    have hRd := (((hasDerivAt_id t).const_mul (env "d")).mul (hCd t)).add
      ((hSd t).const_mul (env "c"))
    have hB := (((hasDerivAt_id t).const_mul (env "a" * env "d")).mul hRd).inv hden2
    have key := hA.add ((hSd t).mul hB)
    convert key using 1
    · funext w
      simp [Pi.mul_apply]
    · simp [sinSqOverQuotSq, eval, toInt?_two, toInt?_neg_one, Pi.mul_apply]
      have hR1 : I.sin (env "a" * t) * env "c" + t * env "d" * I.cos (env "a" * t) ≠ 0 := by
        intro h; apply hq; linear_combination h
      have hR2 : t * env "d" * I.cos (env "a" * t) + I.sin (env "a" * t) * env "c" ≠ 0 := by
        intro h; apply hq; linear_combination h
      field_simp
      set sS := I.sin (env "a" * t)
      set cC := I.cos (env "a" * t)
      set a := env "a"
      set c := env "c"
      set d := env "d"
      have hPt : sS ^ 2 + cC ^ 2 = 1 := hP _
      linear_combination (c*(a*c + d)*(-cC^2*c^2 + 5*cC^2*d^2*t^2 + 4*cC*sS*c*d*t + sS^2*c^2 + c^2)) * hPt + (cC^4*c^3 - 5*cC^4*c*d^2*t^2 - 4*cC^3*sS*c^2*d*t + 2*cC^3*sS*d^3*t^3 - 2*cC^2*c^3 + 5*cC^2*c*d^2*t^2 + 4*cC*sS*c^2*d*t + c^3) * hac

theorem monoOverLogScale_real : monoOverLogScale.Holds .real :=
  monoOverLogScale_holds Interp.real (by simp [Interp.real])

theorem monoOverLogScale_complex : monoOverLogScale.Holds .complex :=
  monoOverLogScale_holds Interp.complex (by simp [Interp.complex])


theorem sinSqOverQuotSq_real : sinSqOverQuotSq.Holds .real :=
  sinSqOverQuotSq_holds Interp.real Real.hasDerivAt_sin Real.hasDerivAt_cos
    Real.sin_sq_add_cos_sq Real.sin_zero

theorem sinSqOverQuotSq_complex : sinSqOverQuotSq.Holds .complex :=
  sinSqOverQuotSq_holds Interp.complex Complex.hasDerivAt_sin Complex.hasDerivAt_cos
    Complex.sin_sq_add_cos_sq Complex.sin_zero

end Proofs

end OSR.IntegrationRec22
