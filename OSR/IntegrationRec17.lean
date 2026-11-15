import OSR.IntegrationRec16

/-!
# Integration (RUBI): integration by parts of `x^m (a + b xⁿ)ᵖ`

Rules that a numerical check found to behave as identities where they are
defined, proved here over every interpretation having the needed
trigonometric identities.  The rule declarations are transcribed by a tool
and checked by the Integration repository's `scripts/v1_faithfulness.py`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec17

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- x^m (a + b x^n)^p by parts, for (m + 1)/n + p = 0 and p > 0 -/
def monoBinomByParts : CRule where
  id := "integration.monomial_binomial_power_by_parts"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:68"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.var "n") (.int (-1)))) (.var "p")) (.int 0),
    .gt (.var "p") (.int 0)]
  priority := 3610
  description := "x^m (a + b x^n)^p by parts, for (m + 1)/n + p = 0 and p > 0"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:68" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.m#68"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

private theorem toInt?_m1 (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

/-- `w^a w^b = w^(a+b)` when `w ≠ 0` or both exponents are nonnegative. -/
private theorem zpow_add_of (w : 𝕜) (a b : ℤ) (h : w ≠ 0 ∨ (0 ≤ a ∧ 0 ≤ b)) :
    w ^ a * w ^ b = w ^ (a + b) := by
  rcases h with h | ⟨ha, hb⟩
  · exact (zpow_add₀ h a b).symm
  · lift a to ℕ using ha
    lift b to ℕ using hb
    rw [zpow_natCast, zpow_natCast, ← Int.natCast_add, zpow_natCast, pow_add]

/-- Integration by parts: `∫ x^m Qᵖ = x^(m+1) Qᵖ/(m+1) - b n p/(m+1) ∫ x^(m+n) Qᵖ⁻¹`, for
`Q = a + b xⁿ` and an integer `p ≥ 1`; the condition `(m + 1)/n + p = 0` gives `m + 1 ≠ 0`. -/
theorem monoBinomByParts_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" monoBinomByParts.conditions monoBinomByParts.body
      monoBinomByParts.result monoBinomByParts.integrals := by
  intro env hcond t hF
  have hgp := hcond (.gt (.var "p") (.int 0)) (by simp [monoBinomByParts])
  have hE := hcond (.eq (.app2 .add (.app2 .mul (.app2 .add (.var "m") (.int 1))
    (.pow (.var "n") (.int (-1)))) (.var "p")) (.int 0)) (by simp [monoBinomByParts])
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomByParts, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomByParts, Defined, eval, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [monoBinomByParts, Defined, eval, hkp] at h
  have hm := toInt?_val hkm
  have hn := toInt?_val hkn
  have hp := toInt?_val hkp
  have hppos : 0 < p := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((0 : ℚ) : 𝕜) ((p : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  have hn0 : (n : 𝕜) ≠ 0 := by
    have := hE.1
    simp [Defined, eval, hn, toInt?_m1 I] at this
    exact_mod_cast this
  have hm1 : (m : 𝕜) + 1 ≠ 0 := by
    intro h0
    have := hE.2.2
    simp [eval, hm, hn, hp, toInt?_m1 I, h0] at this
    exact_mod_cast (show p ≠ 0 by omega) this
  have hn0' : n ≠ 0 := by exact_mod_cast hn0
  have hm1' : m + 1 ≠ 0 := by
    intro h; apply hm1; exact_mod_cast (show ((m + 1 : ℤ) : 𝕜) = 0 by rw [h]; simp)
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k + 1 := ⟨(p - 1).toNat, by omega⟩
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have e1 : I.toInt? ((m : 𝕜) + 1) = some (m + 1) := T _ _ (by push_cast; ring)
  have e2 : I.toInt? ((m : 𝕜) + n) = some (m + n) := T _ _ (by push_cast; ring)
  have e3 : I.toInt? ((k : 𝕜) + 1 + -1) = some k := T _ _ (by push_cast; ring)
  have e4 : I.toInt? ((k : 𝕜) + 1) = some (k + 1) := T _ _ (by push_cast; ring)
  have e5 : I.toInt? (k : 𝕜) = some k := T _ _ (by push_cast; ring)
  have z1 : ∀ x : 𝕜, x ^ ((k : ℤ) + 1) = x ^ (k + 1) := fun x => by
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hk0 : ¬ ((k : ℤ) < 0) := by omega
  have hk1 : ¬ ((k : ℤ) + 1 < 0) := by omega
  have hD : ∀ w, Defined I (Function.update env "x" w) monoBinomByParts.body →
      (m < 0 → w ≠ 0) ∧ (n < 0 → w ≠ 0) := by
    intro w h
    simp [monoBinomByParts, Defined, eval, hm, hn, hp, I.toInt?_cast, e4, e5, hk0, hk1] at h
    exact h
  have ht := hD t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [monoBinomByParts, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hw' := hD w hw
    simp [Defined, eval, hm, hn, hp, I.toInt?_cast, e2, e3, e4, e5, hk0, hk1, toInt?_m1 I]
    exact ⟨fun h => if hm0 : m < 0 then hw'.1 hm0 else hw'.2 (by omega),
      fun h => hw'.2 h⟩
  · filter_upwards [hF] with w hw
    have hw' := hD w hw
    simp [monoBinomByParts, Defined, eval, recEnv, hm, hn, hp, I.toInt?_cast, e1, e2, e3, e4, e5,
      hk0, hk1, toInt?_m1 I, hm1]
    exact ⟨fun h => hw'.1 (by omega), hw'.2⟩
  · simp only [monoBinomByParts, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (monoBinomByParts.integrals.map (·.1)) Φ "x" w)
        monoBinomByParts.result) = fun w =>
          w ^ (m + 1) * (env "a" + env "b" * w ^ n) ^ (k + 1) * ((m : 𝕜) + 1)⁻¹ +
          -1 * env "b" * (n : 𝕜) * ((k : 𝕜) + 1) * ((m : 𝕜) + 1)⁻¹ * Φ "I1" w := by
      funext w
      simp [monoBinomByParts, eval, recEnv, hm, hn, hp, I.toInt?_cast, e1, e2, e3, e4, e5, z1,
        toInt?_m1 I]
      try ring_nf
      try simp
    rw [hfun]
    have htm : t ≠ 0 ∨ 0 ≤ m + 1 := by
      by_cases h : m < 0
      · exact Or.inl (ht.1 h)
      · exact Or.inr (by omega)
    have htn : t ≠ 0 ∨ 0 ≤ n := by
      by_cases h : n < 0
      · exact Or.inl (ht.2 h)
      · exact Or.inr (by omega)
    have hX := hasDerivAt_zpow (m + 1) t htm
    have hQd : HasDerivAt (fun w : 𝕜 => env "a" + env "b" * w ^ n)
        (env "b" * ((n : 𝕜) * t ^ (n - 1))) t :=
      ((hasDerivAt_zpow n t htn).const_mul (env "b")).const_add (env "a")
    have hQp := hQd.pow (k + 1)
    simp only [Nat.add_sub_cancel] at hQp
    refine (((hX.mul hQp).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp [monoBinomByParts, eval, hm, hn, hp, I.toInt?_cast, e2, e3, e4, e5, z1]
    have hmn : t ^ (m + 1) * t ^ (n - 1) = t ^ (m + n) := by
      rw [zpow_add_of t (m + 1) (n - 1) (by
        by_cases h : t = 0
        · right
          have hm0 : ¬ m < 0 := fun hm0 => ht.1 hm0 h
          have hn0'' : ¬ n < 0 := fun hn0'' => ht.2 hn0'' h
          omega
        · exact Or.inl h)]
      congr 1; ring
    have hPi := mul_inv_cancel₀ hm1
    linear_combination (t ^ m * (env "a" + env "b" * t ^ n) ^ (k + 1)) * hPi +
      (((k : 𝕜) + 1) * (env "a" + env "b" * t ^ n) ^ k * env "b" * (n : 𝕜) * ((m : 𝕜) + 1)⁻¹) * hmn

theorem monoBinomByParts_real : monoBinomByParts.Holds .real :=
  monoBinomByParts_holds Interp.real Interp.real_lt_rat

theorem monoBinomByParts_complex : monoBinomByParts.Holds .complex :=
  monoBinomByParts_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec17
