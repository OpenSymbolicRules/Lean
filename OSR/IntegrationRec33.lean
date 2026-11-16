import OSR.IntegrationRec32

/-!
# Integration (RUBI): partial fractions of a pair of binomials

RUBI 4.16.1 1.1.3.4 #45 splits `(e x)^m/((a + b xⁿ)(c + d xⁿ))` as
`b/(b c - a d) (e x)^m/(a + b xⁿ) - d/(b c - a d) (e x)^m/(c + d xⁿ)` when
`b c - a d ≠ 0`.  Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec33

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- x^m/((a + b x^n)(c + d x^n)) in partial fractions -/
def pfMonoBinomPair : CRule where
  id := "integration.partial_fractions_monomial_binomial_pair"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:45"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 6200
  description := "x^m/((a + b x^n)(c + d x^n)) in partial fractions"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:45" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#45"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

theorem pfMonoBinomPair_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" pfMonoBinomPair.conditions pfMonoBinomPair.body
      pfMonoBinomPair.result pfMonoBinomPair.integrals := by
  intro env hc t hF
  have hK := hc (.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul
    (.int (-1)) (.var "a")) (.var "d"))) (.int 0)) (by simp [pfMonoBinomPair])
  have hKv : env "b" * env "c" + -(env "a" * env "d") ≠ 0 := by simpa [eval] using hK.2.2
  rcases hkm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [pfMonoBinomPair, Defined, eval, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [pfMonoBinomPair, Defined, eval, hkn] at h
  have hD : ∀ w, Defined I (Function.update env "x" w) pfMonoBinomPair.body →
      (m < 0 → env "e" ≠ 0 ∧ w ≠ 0) ∧ (n < 0 → w ≠ 0) ∧ env "a" + env "b" * w ^ n ≠ 0 ∧
        env "c" + env "d" * w ^ n ≠ 0 := by
    intro w h
    simp [pfMonoBinomPair, Defined, eval, hkm, hkn, toInt?_neg_one] at h
    exact h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [pfMonoBinomPair, List.mem_cons, List.not_mem_nil, or_false] at hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2, h3, h4⟩ := hD w hw
    rcases hi with rfl | rfl <;> simp [Defined, eval, hkm, hkn, toInt?_neg_one]
    · exact ⟨h1, h2, h3⟩
    · exact ⟨h1, h2, h4⟩
  · exact Eventually.of_forall fun _ => by
      simp [pfMonoBinomPair, Defined, eval, recEnv, toInt?_neg_one, hKv]
  · simp only [pfMonoBinomPair, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (pfMonoBinomPair.integrals.map (·.1)) Φ "x" w)
        pfMonoBinomPair.result) = fun w =>
          env "b" * (env "b" * env "c" + -(env "a" * env "d"))⁻¹ * Φ "I1" w +
            -env "d" * (env "b" * env "c" + -(env "a" * env "d"))⁻¹ * Φ "I2" w := by
      funext w
      simp [pfMonoBinomPair, eval, recEnv, toInt?_neg_one]
    rw [hfun]
    refine ((hΦ.1.const_mul _).add (hΦ.2.const_mul _)).congr_deriv ?_
    obtain ⟨-, -, h3, h4⟩ := hD t hF.self_of_nhds
    simp [pfMonoBinomPair, eval, hkm, hkn, toInt?_neg_one]
    field_simp
    ring

theorem pfMonoBinomPair_real : pfMonoBinomPair.Holds .real := pfMonoBinomPair_holds Interp.real

theorem pfMonoBinomPair_complex : pfMonoBinomPair.Holds .complex :=
  pfMonoBinomPair_holds Interp.complex

end Proofs

end OSR.IntegrationRec33
