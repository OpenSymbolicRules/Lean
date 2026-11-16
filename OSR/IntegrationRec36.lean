import OSR.IntegrationRec35

/-!
# Integration (RUBI): linearity in a polynomial factor

RUBI 4.16.1 1.2.3.3 #56 and #57 split `(A + B x^m) F` into `A F + B x^m F` under
the integral (with `n2 = 2 n`).  Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec36

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- (A + B x^m) F = A F + B x^m F under the integral -/
def linTrinomSplit : CRule where
  id := "integration.linear_split_binomial_trinomial"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:56"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.pow (.var "x") (.var "m")))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.var "A") (.var "I1")) (.app2 .mul (.var "B") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "m", "n", "p", "q", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.int 0)]
  priority := 6500
  description := "(A + B x^m) F = A F + B x^m F under the integral"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:56" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#56"
/-- (A + B x^m) F = A F + B x^m F under the integral -/
def linBinomSplit : CRule where
  id := "integration.linear_split_binomial_binomial"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:57"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.pow (.var "x") (.var "m")))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.var "A") (.var "I1")) (.app2 .mul (.var "B") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "A", "B", "m", "n", "p", "q", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.int 0)]
  priority := 6510
  description := "(A + B x^m) F = A F + B x^m F under the integral"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:57" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#57"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

theorem linTrinomSplit_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" linTrinomSplit.conditions linTrinomSplit.body linTrinomSplit.result linTrinomSplit.integrals := by
  intro env hc t hF
  have heq := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [linTrinomSplit])
  have hn2 : env "n2" = 2 * env "n" := by simpa [Cond.Holds, Defined, eval] using heq.2.2
  rcases hkm : I.toInt? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [linTrinomSplit, Defined, eval, hn2, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [linTrinomSplit, Defined, eval, hn2, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [linTrinomSplit, Defined, eval, hn2, hkp] at h
  rcases hkq : I.toInt? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [linTrinomSplit, Defined, eval, hn2, hkq] at h
  have k2 : I.toInt? (2 * env "n") = some (2 * kn) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linTrinomSplit, List.mem_cons, List.not_mem_nil, or_false] at hi
    filter_upwards [hF] with w hw
    simp [linTrinomSplit, Defined, eval, hn2, hkm, hkn, hkp, hkq, k2] at hw
    rcases hi with rfl | rfl <;> simp [Defined, eval, hn2, hkm, hkn, hkp, hkq, k2]
    · exact ⟨⟨hw.1.2.1, hw.1.2.2⟩, hw.2⟩
    · exact hw
  · exact Eventually.of_forall fun _ => by simp [linTrinomSplit, Defined]
  · simp only [linTrinomSplit, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (linTrinomSplit.integrals.map (·.1)) Φ "x" w)
        linTrinomSplit.result) = fun w => env "A" * Φ "I1" w + env "B" * Φ "I2" w := by
      funext w
      simp [linTrinomSplit, eval, recEnv]
    rw [hfun]
    refine ((hΦ.1.const_mul _).add (hΦ.2.const_mul _)).congr_deriv ?_
    simp [linTrinomSplit, eval, hn2, hkm, hkn, hkp, hkq, k2]
    ring

theorem linTrinomSplit_real : linTrinomSplit.Holds .real := linTrinomSplit_holds Interp.real

theorem linTrinomSplit_complex : linTrinomSplit.Holds .complex := linTrinomSplit_holds Interp.complex

theorem linBinomSplit_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" linBinomSplit.conditions linBinomSplit.body linBinomSplit.result linBinomSplit.integrals := by
  intro env hc t hF
  have heq := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [linBinomSplit])
  have hn2 : env "n2" = 2 * env "n" := by simpa [Cond.Holds, Defined, eval] using heq.2.2
  rcases hkm : I.toInt? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [linBinomSplit, Defined, eval, hn2, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [linBinomSplit, Defined, eval, hn2, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [linBinomSplit, Defined, eval, hn2, hkp] at h
  rcases hkq : I.toInt? (env "q") with _ | kq
  · exfalso
    have h := hF.self_of_nhds
    simp [linBinomSplit, Defined, eval, hn2, hkq] at h
  have k2 : I.toInt? (2 * env "n") = some (2 * kn) :=
    (I.toInt?_eq _ _).2 (by rw [(I.toInt?_eq _ _).1 hkn]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [linBinomSplit, List.mem_cons, List.not_mem_nil, or_false] at hi
    filter_upwards [hF] with w hw
    simp [linBinomSplit, Defined, eval, hn2, hkm, hkn, hkp, hkq, k2] at hw
    rcases hi with rfl | rfl <;> simp [Defined, eval, hn2, hkm, hkn, hkp, hkq, k2]
    · exact ⟨⟨hw.1.2.1, hw.1.2.2⟩, hw.2⟩
    · exact hw
  · exact Eventually.of_forall fun _ => by simp [linBinomSplit, Defined]
  · simp only [linBinomSplit, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (linBinomSplit.integrals.map (·.1)) Φ "x" w)
        linBinomSplit.result) = fun w => env "A" * Φ "I1" w + env "B" * Φ "I2" w := by
      funext w
      simp [linBinomSplit, eval, recEnv]
    rw [hfun]
    refine ((hΦ.1.const_mul _).add (hΦ.2.const_mul _)).congr_deriv ?_
    simp [linBinomSplit, eval, hn2, hkm, hkn, hkp, hkq, k2]
    ring

theorem linBinomSplit_real : linBinomSplit.Holds .real := linBinomSplit_holds Interp.real

theorem linBinomSplit_complex : linBinomSplit.Holds .complex := linBinomSplit_holds Interp.complex

end Proofs

end OSR.IntegrationRec36
