import OSR.IntegrationRec11

/-!
# Integration (RUBI): reduction of quartic powers

Rules that a numerical check found to behave as identities where they are
defined, proved here over every interpretation having the needed
trigonometric identities.  The rule declarations are transcribed by a tool
and checked by the Integration repository's `scripts/v1_faithfulness.py`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec12

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- (a + b x^2 + c x^4)^p reduced to p - 1, for p > 0 -/
def quartPowReduce : CRule where
  id := "integration.quartic_power_reduction"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.1 (a+b x^2+c x^4)^p:4"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.int 4) (.var "p")) (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "p")) (.pow (.app2 .add (.app2 .mul (.int 4) (.var "p")) (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.var "p") (.int 0),
    .int (.app2 .mul (.int 2) (.var "p"))]
  priority := 2780
  description := "(a + b x^2 + c x^4)^p reduced to p - 1, for p > 0"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.1 (a+b x^2+c x^4)^p:4" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.1 (a+b x^2+c x^4)^p.m#4"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_val {I : Interp 𝕜} {v : 𝕜} {k : ℤ} (h : I.toInt? v = some k) :
    v = (k : 𝕜) := (I.toInt?_eq _ _).1 h

private theorem toInt?_m1 (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_2 (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_4 (I : Interp 𝕜) : I.toInt? (4 : 𝕜) = some 4 :=
  (I.toInt?_eq _ _).2 (by simp)

/-- `(x Qᵖ)' + 2 p (2 a + b x²) Qᵖ⁻¹ = (4 p + 1) Qᵖ` for `Q = a + b x² + c x⁴`,
so `∫ Qᵖ` reduces to `∫ (2 a + b x²) Qᵖ⁻¹` for an integer `p ≥ 1`. -/
theorem quartPowReduce_holds [CharZero 𝕜] (I : Interp 𝕜)
    (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" quartPowReduce.conditions quartPowReduce.body
      quartPowReduce.result quartPowReduce.integrals := by
  intro env hcond t hF
  have hgp := hcond (.gt (.var "p") (.int 0)) (by simp [quartPowReduce])
  rcases hkp : I.toInt? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [quartPowReduce, Defined, eval, hkp] at h
  have hp := toInt?_val hkp
  have hppos : 0 < p := by
    simp only [Cond.Holds, Defined, eval, true_and] at hgp
    rw [hp] at hgp
    have h' : I.lt ((0 : ℚ) : 𝕜) ((p : ℚ) : 𝕜) := by
      rw [Rat.cast_intCast, Rat.cast_zero]; simpa using hgp
    exact_mod_cast (hlt _ _).1 h'
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k + 1 := ⟨(p - 1).toNat, by omega⟩
  have T : ∀ (v : 𝕜) (z : ℤ), v = (z : 𝕜) → I.toInt? v = some z :=
    fun v z h => (I.toInt?_eq _ _).2 h
  have e1 : I.toInt? ((k : 𝕜) + 1 + -1) = some k := T _ _ (by push_cast; ring)
  have e2 : I.toInt? ((k : 𝕜) + 1 - 1) = some k := T _ _ (by push_cast; ring)
  have e3 : I.toInt? ((k : 𝕜) + 1) = some (k + 1) := T _ _ (by push_cast; ring)
  have e4 : I.toInt? (k : 𝕜) = some k := T _ _ (by push_cast; ring)
  have z1 : ∀ x : 𝕜, x ^ ((k : ℤ) + 1) = x ^ (k + 1) := fun x => by
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hk1 : ¬ ((k : ℤ) + 1 < 0) := by omega
  have hk0 : ¬ ((k : ℤ) < 0) := by omega
  have h4 : (4 * ((k : 𝕜) + 1) + 1) ≠ 0 := by
    have : (4 * ((k : 𝕜) + 1) + 1) = ((4 * k + 5 : ℕ) : 𝕜) := by push_cast; ring
    rw [this]; exact_mod_cast (show 4 * k + 5 ≠ 0 by omega)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [quartPowReduce, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact Eventually.of_forall fun w => by
      simp [Defined, eval, hp, e1, e2, e3, e4, toInt?_2 I, toInt?_4 I, toInt?_m1 I,
        I.toInt?_cast, hk0, hk1]
  · exact Eventually.of_forall fun w => by
      simp [quartPowReduce, Defined, eval, recEnv, toInt?_m1 I, toInt?_2 I, toInt?_4 I, hp,
        e1, e2, e3, e4, I.toInt?_cast, hk0, hk1]
      exact h4
  · simp only [quartPowReduce, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (quartPowReduce.integrals.map (·.1)) Φ "x" w)
        quartPowReduce.result) = fun w =>
          w * (env "a" + env "b" * w ^ 2 + env "c" * w ^ 4) ^ (k + 1) *
            (4 * ((k : 𝕜) + 1) + 1)⁻¹ +
          2 * ((k : 𝕜) + 1) * (4 * ((k : 𝕜) + 1) + 1)⁻¹ * Φ "I1" w := by
      funext w
      simp [quartPowReduce, eval, recEnv, toInt?_m1 I, toInt?_2 I, toInt?_4 I, hp, e1, e2, e3, e4,
        I.toInt?_cast, z1]
      try ring_nf
      try simp
    rw [hfun]
    have hQd : HasDerivAt (fun w : 𝕜 => env "a" + env "b" * w ^ 2 + env "c" * w ^ 4)
        (env "b" * (2 * t) + env "c" * (4 * t ^ 3)) t := by
      have := (((hasDerivAt_pow 2 t).const_mul (env "b")).const_add (env "a")).add
        ((hasDerivAt_pow 4 t).const_mul (env "c"))
      convert this using 1 <;> first | rfl | (simp; ring) | ring
    have hP := hQd.pow (k + 1)
    simp only [Nat.add_sub_cancel] at hP
    refine ((((hasDerivAt_id' t).mul hP).mul_const _).add (hΦ.const_mul _)).congr_deriv ?_
    simp [quartPowReduce, eval, toInt?_2 I, toInt?_4 I, hp, e1, e2, e3, e4, I.toInt?_cast, z1]
    have hI := mul_inv_cancel₀ h4
    linear_combination (env "a" + env "b" * t ^ 2 + env "c" * t ^ 4) ^ (k + 1) * hI

theorem quartPowReduce_real : quartPowReduce.Holds .real :=
  quartPowReduce_holds Interp.real Interp.real_lt_rat

theorem quartPowReduce_complex : quartPowReduce.Holds .complex :=
  quartPowReduce_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec12
