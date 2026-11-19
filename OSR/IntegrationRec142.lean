import OSR.IntegrationRec91

/-!
# Integration (RUBI): `(d1 + e1 x)^p (d2 + e2 x)^p = (d1 d2 + e1 e2 x²)^p`

With `d2 e1 + d1 e2 = 0` the two linear factors multiply to `d1 d2 + e1 e2 x²`,
so for an integer `p` the integrand is the residual integrand.  Proved over ℝ
(arccosh has no complex interpretation in the fragment).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec142

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.2.3 #1 -/
def rubi723r1 : CRule where
  id := "integration.rubi_7_2_3_r1"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.var "p")) (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "d1") (.var "d2")) (.app2 .mul (.app2 .mul (.var "e1") (.var "e2")) (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))))]
  independent := ["a", "b", "c", "d1", "e1", "d2", "e2", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "d2") (.var "e1")) (.app2 .mul (.var "d1") (.var "e2"))) (.int 0),
    .int (.var "p")]
  priority := 11801
  description := "RUBI 7.2.3 #1"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n:1" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n.m#1"

/-- RUBI 7.2.4 #1 -/
def rubi724r1 : CRule where
  id := "integration.rubi_7_2_4_r1"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .mul (.var "d1") (.var "d2")) (.app2 .mul (.app2 .mul (.var "e1") (.var "e2")) (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))))]
  independent := ["a", "b", "c", "d1", "e1", "d2", "e2", "f", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "d2") (.var "e1")) (.app2 .mul (.var "d1") (.var "e2"))) (.int 0),
    .int (.var "p")]
  priority := 11802
  description := "RUBI 7.2.4 #1"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:1" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m#1"

/-! ## Proofs -/

theorem rubi723r1_real : rubi723r1.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi723r1.conditions rubi723r1.body rubi723r1.result rubi723r1.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi723r1, Defined, eval, Interp.real, hk_p] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi723r1, Defined, eval, Interp.real, hk_p, hk_n] at h
  have heq : env "d2" * env "e1" + env "d1" * env "e2" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "d2") (.var "e1")) (.app2 .mul (.var "d1") (.var "e2"))) (.int 0)) (by simp [rubi723r1])
    simpa [Cond.Holds, Defined, eval] using h
  have hprod : ∀ w : ℝ, (env "d1" + env "e1" * w) * (env "d2" + env "e2" * w) = env "d1" * env "d2" + env "e1" * env "e2" * w ^ 2 := by
    intro w; linear_combination w * heq
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi723r1, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi723r1, Defined, eval, Interp.real, i2, hk_p, hk_n] at hw ⊢
    have hp := hprod w
    have key : ∀ k : ℤ, (k < 0 → ¬env "d1" + env "e1" * w = 0) → (k < 0 → ¬env "d2" + env "e2" * w = 0) →
        (k < 0 → ¬env "d1" * env "d2" + env "e1" * env "e2" * w ^ 2 = 0) := by
      intro k h1 h2 hk h0; rw [← hp] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact h1 hk h
      · exact h2 hk h
    have := key kp
    tauto
  · exact Eventually.of_forall fun w => by simp [rubi723r1, Defined, eval, recEnv]
  · simp only [rubi723r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi723r1.integrals.map (·.1)) Φ "x" w) rubi723r1.result) = Φ "I1" := by
      funext w; simp [rubi723r1, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi723r1, eval, Interp.real, i2, hk_p, hk_n]
    first
      | exact Or.inl trivial
      | (left; rw [mul_assoc ((env "f" * t) ^ km), ← mul_zpow, hprod t])
      | (left; rw [← mul_zpow, hprod t])
      | (left; congr 1; linear_combination (-t) * heq)
      | (left; congr 1; linear_combination t * heq)

theorem rubi724r1_real : rubi724r1.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi724r1.conditions rubi724r1.body rubi724r1.result rubi724r1.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi724r1, Defined, eval, Interp.real, hk_p] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi724r1, Defined, eval, Interp.real, hk_p, hk_n] at h
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi724r1, Defined, eval, Interp.real, hk_p, hk_n, hk_m] at h
  have heq : env "d2" * env "e1" + env "d1" * env "e2" = 0 := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "d2") (.var "e1")) (.app2 .mul (.var "d1") (.var "e2"))) (.int 0)) (by simp [rubi724r1])
    simpa [Cond.Holds, Defined, eval] using h
  have hprod : ∀ w : ℝ, (env "d1" + env "e1" * w) * (env "d2" + env "e2" * w) = env "d1" * env "d2" + env "e1" * env "e2" * w ^ 2 := by
    intro w; linear_combination w * heq
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi724r1, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi724r1, Defined, eval, Interp.real, i2, hk_p, hk_n, hk_m] at hw ⊢
    have hp := hprod w
    have key : ∀ k : ℤ, (k < 0 → ¬env "d1" + env "e1" * w = 0) → (k < 0 → ¬env "d2" + env "e2" * w = 0) →
        (k < 0 → ¬env "d1" * env "d2" + env "e1" * env "e2" * w ^ 2 = 0) := by
      intro k h1 h2 hk h0; rw [← hp] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact h1 hk h
      · exact h2 hk h
    have := key kp
    tauto
  · exact Eventually.of_forall fun w => by simp [rubi724r1, Defined, eval, recEnv]
  · simp only [rubi724r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi724r1.integrals.map (·.1)) Φ "x" w) rubi724r1.result) = Φ "I1" := by
      funext w; simp [rubi724r1, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi724r1, eval, Interp.real, i2, hk_p, hk_n, hk_m]
    first
      | exact Or.inl trivial
      | (left; rw [mul_assoc ((env "f" * t) ^ km), ← mul_zpow, hprod t])
      | (left; rw [← mul_zpow, hprod t])
      | (left; congr 1; linear_combination (-t) * heq)
      | (left; congr 1; linear_combination t * heq)


end OSR.IntegrationRec142
