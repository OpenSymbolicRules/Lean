import OSR.IntegrationRec30

/-!
# Integration (RUBI): improper trinomials with equal powers

RUBI 4.16.1 1.2.4.1 #1 and 1.2.4.2 #1 collect `a x^q + b x^n + c x^r` into
`(a + b + c) x^n` when `q = n` and `r = n`.  Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec31

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- a x^n + b x^n + c x^n = (a + b + c) x^n under the integral -/
def improperTrinomEq : CRule where
  id := "integration.improper_trinomial_equal_powers"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.4 Improper/1.2.4.1 (a x^q+b x^n+c x^(2 n-q))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "q"))) (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "r")))) (.var "p"))
  result := (.var "I1")
  integrals := [("I1", (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "a") (.var "b")) (.var "c")) (.pow (.var "x") (.var "n"))) (.var "p")))]
  independent := ["a", "b", "c", "n", "p", "q", "r"]
  conditions := [.eq (.var "n") (.var "q"),
    .eq (.var "r") (.var "n")]
  priority := 6000
  description := "a x^n + b x^n + c x^n = (a + b + c) x^n under the integral"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.4 Improper/1.2.4.1 (a x^q+b x^n+c x^(2 n-q))^p:1" "1 Algebraic functions/1.2 Trinomial products/1.2.4 Improper/1.2.4.1 (a x^q+b x^n+c x^(2 n-q))^p.m#1"
/-- x^m (a x^n + b x^n + c x^n)^p = x^m ((a + b + c) x^n)^p under the integral -/
def monoImproperTrinomEq : CRule where
  id := "integration.monomial_improper_trinomial_equal_powers"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.4 Improper/1.2.4.2 (d x)^m (a x^q+b x^n+c x^(2 n-q))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "q"))) (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "r")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "a") (.var "b")) (.var "c")) (.pow (.var "x") (.var "n"))) (.var "p"))))]
  independent := ["a", "b", "c", "m", "n", "p", "q", "r"]
  conditions := [.eq (.var "q") (.var "n"),
    .eq (.var "r") (.var "n")]
  priority := 6010
  description := "x^m (a x^n + b x^n + c x^n)^p = x^m ((a + b + c) x^n)^p under the integral"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.4 Improper/1.2.4.2 (d x)^m (a x^q+b x^n+c x^(2 n-q))^p:1" "1 Algebraic functions/1.2 Trinomial products/1.2.4 Improper/1.2.4.2 (d x)^m (a x^q+b x^n+c x^(2 n-q))^p.m#1"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

theorem improperTrinomEq_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" improperTrinomEq.conditions improperTrinomEq.body improperTrinomEq.result improperTrinomEq.integrals := by
  intro env hc t hF
  have hq : env "q" = env "n" := by
    have h := (hc (.eq (.var "n") (.var "q")) (by simp [improperTrinomEq])).2.2
    simp only [eval] at h
    exact h.symm
  have hr : env "r" = env "n" := by
    have h := (hc (.eq (.var "r") (.var "n")) (by simp [improperTrinomEq])).2.2
    simpa only [eval] using h
  have hsum : ∀ w : 𝕜, ∀ k : ℤ, env "a" * w ^ k + env "b" * w ^ k + env "c" * w ^ k =
      (env "a" + env "b" + env "c") * w ^ k := fun w k => by ring
  rcases hkn : I.toInt? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [improperTrinomEq, Defined, eval, hq, hr, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [improperTrinomEq, Defined, eval, hq, hr, hkp] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [improperTrinomEq, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [improperTrinomEq, Defined, eval, hq, hr, hkn, hkp, hsum] at hw ⊢
    exact hw
  · exact Eventually.of_forall fun _ => by simp [improperTrinomEq, Defined]
  · simp only [improperTrinomEq, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (improperTrinomEq.integrals.map (·.1)) Φ "x" w)
        improperTrinomEq.result) = Φ "I1" := by
      funext w
      simp [improperTrinomEq, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [improperTrinomEq, eval, hq, hr, hkn, hkp, hsum]

theorem improperTrinomEq_real : improperTrinomEq.Holds .real := improperTrinomEq_holds Interp.real

theorem improperTrinomEq_complex : improperTrinomEq.Holds .complex := improperTrinomEq_holds Interp.complex

theorem monoImproperTrinomEq_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" monoImproperTrinomEq.conditions monoImproperTrinomEq.body monoImproperTrinomEq.result monoImproperTrinomEq.integrals := by
  intro env hc t hF
  have hq : env "q" = env "n" := by
    have h := (hc (.eq (.var "q") (.var "n")) (by simp [monoImproperTrinomEq])).2.2
    simp only [eval] at h
    exact h
  have hr : env "r" = env "n" := by
    have h := (hc (.eq (.var "r") (.var "n")) (by simp [monoImproperTrinomEq])).2.2
    simpa only [eval] using h
  have hsum : ∀ w : 𝕜, ∀ k : ℤ, env "a" * w ^ k + env "b" * w ^ k + env "c" * w ^ k =
      (env "a" + env "b" + env "c") * w ^ k := fun w k => by ring
  rcases hkm : I.toInt? (env "m") with _ | km
  · exfalso
    have h := hF.self_of_nhds
    simp [monoImproperTrinomEq, Defined, eval, hq, hr, hkm] at h
  rcases hkn : I.toInt? (env "n") with _ | kn
  · exfalso
    have h := hF.self_of_nhds
    simp [monoImproperTrinomEq, Defined, eval, hq, hr, hkn] at h
  rcases hkp : I.toInt? (env "p") with _ | kp
  · exfalso
    have h := hF.self_of_nhds
    simp [monoImproperTrinomEq, Defined, eval, hq, hr, hkp] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [monoImproperTrinomEq, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [monoImproperTrinomEq, Defined, eval, hq, hr, hkm, hkn, hkp, hsum] at hw ⊢
    exact hw
  · exact Eventually.of_forall fun _ => by simp [monoImproperTrinomEq, Defined]
  · simp only [monoImproperTrinomEq, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (monoImproperTrinomEq.integrals.map (·.1)) Φ "x" w)
        monoImproperTrinomEq.result) = Φ "I1" := by
      funext w
      simp [monoImproperTrinomEq, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [monoImproperTrinomEq, eval, hq, hr, hkm, hkn, hkp, hsum]

theorem monoImproperTrinomEq_real : monoImproperTrinomEq.Holds .real := monoImproperTrinomEq_holds Interp.real

theorem monoImproperTrinomEq_complex : monoImproperTrinomEq.Holds .complex := monoImproperTrinomEq_holds Interp.complex

end Proofs

end OSR.IntegrationRec31
