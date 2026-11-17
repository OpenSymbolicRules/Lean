import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, fifteenth batch

RUBI 1.1.3.7 #5 is refuted as stated; with `b ≠ 0` and `B ≠ 0` the condition
`a B³ = b A³` makes `B³ (a + b x³) = b (A + B x)(A² - A B x + B² x²)`, and the
rule is proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec110

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_1_1_3_7_r5 with NeQ[b, 0]; NeQ[B, 0] -/
def rubi1137r5Nondeg : CRule where
  id := "integration.rubi_1_1_3_7_r5_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.pow (.var "B") (.int 3)) (.pow (.var "b") (.int (-1)))) (.var "I1"))
  integrals := [("I1", .app2 .mul (.int 1) (.pow (.app2 .add (.app2 .add (.pow (.var "A") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "B")) (.var "x"))) (.app2 .mul (.pow (.var "B") (.int 2)) (.pow (.var "x") (.int 2)))) (.int (-1))))]
  independent := ["a", "b", "A", "B"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.pow (.var "B") (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "A") (.int 3)))) (.int 0),
    .ne (.var "b") (.int 0),
    .ne (.var "B") (.int 0)]
  priority := 9281
  description := "rubi_1_1_3_7_r5 with NeQ[b, 0]; NeQ[B, 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p:5" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p.m#5"


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

theorem rubi1137r5Nondeg_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi1137r5Nondeg.conditions rubi1137r5Nondeg.body rubi1137r5Nondeg.result rubi1137r5Nondeg.integrals := by
  intro env hc t hF
  have heq := hc (.eq (.app2 .add (.app2 .mul (.var "a") (.pow (.var "B") (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "A") (.int 3)))) (.int 0)) (by simp [rubi1137r5Nondeg])
  have h3 : I.toInt? (3 : 𝕜) = some 3 := (I.toInt?_eq _ _).2 (by simp)
  simp [Cond.Holds, Defined, eval, h3] at heq
  have hb : env "b" ≠ 0 := by have h := hc (.ne (.var "b") (.int 0)) (by simp [rubi1137r5Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hB : env "B" ≠ 0 := by have h := hc (.ne (.var "B") (.int 0)) (by simp [rubi1137r5Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hid : ∀ w : 𝕜, env "B" ^ 3 * (env "a" + env "b" * w ^ 3) = env "b" * (env "A" + env "B" * w) * (env "A" ^ 2 + -1 * env "A" * env "B" * w + env "B" ^ 2 * w ^ 2) := by
    intro w; linear_combination heq
  have hPne : ∀ w : 𝕜, (env "a" + env "b" * w ^ 3) ≠ 0 → (env "A" ^ 2 + -1 * env "A" * env "B" * w + env "B" ^ 2 * w ^ 2) ≠ 0 := by
    intro w h hP
    apply h
    have : env "B" ^ 3 * (env "a" + env "b" * w ^ 3) = 0 := by rw [hid w, hP, mul_zero]
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h1) hB
    · exact h1
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1137r5Nondeg.body → (env "a" + env "b" * w ^ 3) ≠ 0 := by
    intro w h
    simp [rubi1137r5Nondeg, Defined, eval, h3, toInt?_neg_one] at h
    first | exact h | exact h.2 | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1137r5Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hP := hPne w (hBody w hw)
    simp [Defined, eval, toInt?_two, toInt?_neg_one]
    intro h; apply hP; linear_combination h
  · exact Eventually.of_forall fun w => by simp [rubi1137r5Nondeg, Defined, eval, recEnv, h3, toInt?_neg_one, hb]
  · simp only [rubi1137r5Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hQ0 := hBody t hF.self_of_nhds
    have hP0 := hPne t hQ0
    have hΦ' : HasDerivAt (Φ "I1") (1 * (env "A" ^ 2 + -1 * env "A" * env "B" * t + env "B" ^ 2 * t ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, toInt?_two, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1137r5Nondeg.body = (env "A" + env "B" * t) * (env "a" + env "b" * t ^ 3)⁻¹ := by
      simp [rubi1137r5Nondeg, eval, h3, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1137r5Nondeg.integrals.map (·.1)) Φ "x" w) rubi1137r5Nondeg.result) =
        fun w => env "B" ^ 3 * (env "b")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1137r5Nondeg, eval, recEnv, h3, toInt?_neg_one]
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have k := hid t
    generalize (env "A" ^ 2 + -1 * env "A" * env "B" * t + env "B" ^ 2 * t ^ 2) = Pv at hP0 k ⊢
    generalize (env "a" + env "b" * t ^ 3) = Qv at hQ0 k ⊢
    field_simp
    first | linear_combination k | linear_combination -k | linear_combination (-1) * k

theorem rubi1137r5Nondeg_real : rubi1137r5Nondeg.Holds .real := rubi1137r5Nondeg_holds Interp.real
theorem rubi1137r5Nondeg_complex : rubi1137r5Nondeg.Holds .complex := rubi1137r5Nondeg_holds Interp.complex

end Proofs

end OSR.IntegrationRec110
