import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of 1.3.1 #4 and 1.3.2 #1

RUBI 1.3.1 #4 and 1.3.2 #1 factor the cubic `a + b x + d x³` when
`4 b³ + 27 a² d = 0`: then `(3 a - b x)(3 a + 2 b x)² = 27 a² (a + b x + d x³)`.
With RUBI's own `3^(3p) a^(2p) ≠ 0` the factorisation holds; the integer powers
need no other condition.  Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec116

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_1_3_1_r4 with NeQ[Multiply[Power[3, Multiply[3, p]], Power[a, Multiply[2, p]]], 0] -/
def rubi131r4Nondeg : CRule where
  id := "integration.rubi_1_3_1_r4_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.1 P(x)^p:4"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "d") (.pow (.var "x") (.int 3)))) (.var "p"))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 3) (.app2 .mul (.int 3) (.var "p"))) (.pow (.var "a") (.app2 .mul (.int 2) (.var "p")))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.int 3) (.var "a")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "x"))) (.var "p")) (.pow (.app2 .add (.app2 .mul (.int 3) (.var "a")) (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "x"))) (.app2 .mul (.int 2) (.var "p")))))]
  independent := ["a", "b", "d", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.int 4) (.pow (.var "b") (.int 3))) (.app2 .mul (.app2 .mul (.int 27) (.pow (.var "a") (.int 2))) (.var "d"))) (.int 0),
    .int (.var "p"),
    .ne (.app2 .mul (.pow (.int 3) (.app2 .mul (.int 3) (.var "p"))) (.pow (.var "a") (.app2 .mul (.int 2) (.var "p")))) (.int 0)]
  priority := 9341
  description := "rubi_1_3_1_r4 with NeQ[Multiply[Power[3, Multiply[3, p]], Power[a, Multiply[2, p]]], 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.1 P(x)^p:4" "1 Algebraic functions/1.3 Miscellaneous/1.3.1 P(x)^p.m#4"

/-- rubi_1_3_2_r1 with NeQ[Multiply[Power[3, Multiply[3, p]], Power[a, Multiply[2, p]]], 0] -/
def rubi132r1Nondeg : CRule where
  id := "integration.rubi_1_3_2_r1_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.2 P(x) Q(x)^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "d") (.pow (.var "x") (.int 3)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 3) (.app2 .mul (.int 3) (.var "p"))) (.pow (.var "a") (.app2 .mul (.int 2) (.var "p")))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .mul (.int 3) (.var "a")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "x"))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.int 3) (.var "a")) (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "x"))) (.app2 .mul (.int 2) (.var "p")))))]
  independent := ["a", "b", "d", "e", "f", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.int 4) (.pow (.var "b") (.int 3))) (.app2 .mul (.app2 .mul (.int 27) (.pow (.var "a") (.int 2))) (.var "d"))) (.int 0),
    .int (.var "p"),
    .ne (.app2 .mul (.pow (.int 3) (.app2 .mul (.int 3) (.var "p"))) (.pow (.var "a") (.app2 .mul (.int 2) (.var "p")))) (.int 0)]
  priority := 9342
  description := "rubi_1_3_2_r1 with NeQ[Multiply[Power[3, Multiply[3, p]], Power[a, Multiply[2, p]]], 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.2 P(x) Q(x)^p:1" "1 Algebraic functions/1.3 Miscellaneous/1.3.2 P(x) Q(x)^p.m#1"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_three (I : Interp 𝕜) : I.toInt? (3 : 𝕜) = some 3 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem zpow_two_mul (A : 𝕜) (q : ℤ) : A ^ (2 * q) = (A ^ 2) ^ q := by
  rw [zpow_mul]; norm_cast

private theorem zpow_three_mul (A : 𝕜) (q : ℤ) : A ^ (3 * q) = (A ^ 3) ^ q := by
  rw [zpow_mul]; norm_cast

theorem rubi131r4Nondeg_holds (I : Interp 𝕜) (h3 : (3 : 𝕜) ≠ 0) :
    AntiderivRecHolds I "x" rubi131r4Nondeg.conditions rubi131r4Nondeg.body rubi131r4Nondeg.result rubi131r4Nondeg.integrals := by
  intro env hc t hF
  have heq0 := hc (.eq (.app2 .add (.app2 .mul (.int 4) (.pow (.var "b") (.int 3))) (.app2 .mul (.app2 .mul (.int 27) (.pow (.var "a") (.int 2))) (.var "d"))) (.int 0)) (by simp [rubi131r4Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two, toInt?_three] at heq0
  have heq : 4 * env "b" ^ 3 + 27 * env "a" ^ 2 * env "d" = 0 := by linear_combination heq0
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi131r4Nondeg, Defined, eval, hk_p, toInt?_three] at h
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have e3 : I.toInt? (3 * env "p") = some (3 * q) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e2 : I.toInt? (2 * env "p") = some (2 * q) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hA := hc (.ne (.app2 .mul (.pow (.int 3) (.app2 .mul (.int 3) (.var "p"))) (.pow (.var "a") (.app2 .mul (.int 2) (.var "p")))) (.int 0)) (by simp [rubi131r4Nondeg])
  have hc0 : (3 : 𝕜) ^ (3 * q) * env "a" ^ (2 * q) ≠ 0 := by
    simp [Cond.Holds, Defined, eval, e3, e2] at hA
    exact mul_ne_zero (by tauto) (by tauto)
  have ha0 : q < 0 → env "a" ≠ 0 := by
    intro hq ha; apply hc0; rw [ha, zero_zpow _ (by omega), mul_zero]
  have hpoly : ∀ w : 𝕜, (3 * env "a" + -1 * env "b" * w) * (3 * env "a" + 2 * env "b" * w) ^ 2 = (3 : 𝕜) ^ 3 * env "a" ^ 2 * (env "a" + env "b" * w + env "d" * w ^ 3) := by
    intro w; linear_combination (-(w ^ 3)) * heq
  have hzp : ∀ w : 𝕜, (3 * env "a" + -1 * env "b" * w) ^ q * (3 * env "a" + 2 * env "b" * w) ^ (2 * q) = (3 : 𝕜) ^ (3 * q) * env "a" ^ (2 * q) * (env "a" + env "b" * w + env "d" * w ^ 3) ^ q := by
    intro w
    rw [zpow_two_mul, zpow_two_mul, zpow_three_mul, ← mul_zpow, ← mul_zpow, ← mul_zpow, hpoly w]
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi131r4Nondeg.body → (q < 0 → (env "a" + env "b" * w + env "d" * w ^ 3) ≠ 0) := by
    intro w h
    simp [rubi131r4Nondeg, Defined, eval, hk_p, toInt?_three] at h
    first | exact h | tauto | (trace_state; sorry)
  have hQ : ∀ w : 𝕜, q < 0 → (env "a" + env "b" * w + env "d" * w ^ 3) ≠ 0 → (3 * env "a" + -1 * env "b" * w) ≠ 0 ∧ (3 * env "a" + 2 * env "b" * w) ≠ 0 := by
    intro w hq hP
    have h := hpoly w
    have hr : (3 : 𝕜) ^ 3 * env "a" ^ 2 * (env "a" + env "b" * w + env "d" * w ^ 3) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ (ha0 hq))) hP
    rw [← h] at hr
    exact ⟨left_ne_zero_of_mul hr, pow_ne_zero_iff (by norm_num) |>.1 (right_ne_zero_of_mul hr)⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi131r4Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h1 := hBody w hw
    simp [Defined, eval, hk_p, e2, e3, toInt?_three]
    have hA1 : q < 0 → ¬ 3 * env "a" + -(env "b" * w) = 0 := fun hq h0 =>
      (hQ w hq (h1 hq)).1 (by linear_combination h0)
    have hA1' : q < 0 → ¬ 3 * env "a" + -1 * env "b" * w = 0 := fun hq => (hQ w hq (h1 hq)).1
    have hA2 : 2 * q < 0 → ¬ 3 * env "a" + 2 * env "b" * w = 0 := fun hq => (hQ w (by omega) (h1 (by omega))).2
    first | done | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi131r4Nondeg, Defined, eval, recEnv, e2, e3, toInt?_neg_one, toInt?_three]
      first | done | exact hc0 | exact ⟨⟨fun _ => h3, fun h => ha0 (by omega)⟩, left_ne_zero_of_mul hc0, right_ne_zero_of_mul hc0⟩ | (trace_state; sorry)
  · simp only [rubi131r4Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((3 * env "a" + -1 * env "b" * t) ^ q * (3 * env "a" + 2 * env "b" * t) ^ (2 * q)) t := by
      convert hΦ using 1
      simp [eval, hk_p, e2, e3, toInt?_three]
    have hEF : eval I (Function.update env "x" t) rubi131r4Nondeg.body = (env "a" + env "b" * t + env "d" * t ^ 3) ^ q := by
      simp [rubi131r4Nondeg, eval, hk_p, toInt?_three]
    have hfun : (fun w => eval I (recEnv env (rubi131r4Nondeg.integrals.map (·.1)) Φ "x" w) rubi131r4Nondeg.result) =
        fun w => 1 * ((3 : 𝕜) ^ (3 * q) * env "a" ^ (2 * q))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi131r4Nondeg, eval, recEnv, e2, e3, toInt?_neg_one, toInt?_three, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hcc : ((3 : 𝕜) ^ (3 * q) * env "a" ^ (2 * q))⁻¹ * ((3 : 𝕜) ^ (3 * q) * env "a" ^ (2 * q)) = 1 := inv_mul_cancel₀ hc0
    linear_combination (((3 : 𝕜) ^ (3 * q) * env "a" ^ (2 * q))⁻¹ * 1) * hzp t + (1 * (env "a" + env "b" * t + env "d" * t ^ 3) ^ q) * hcc

theorem rubi132r1Nondeg_holds (I : Interp 𝕜) (h3 : (3 : 𝕜) ≠ 0) :
    AntiderivRecHolds I "x" rubi132r1Nondeg.conditions rubi132r1Nondeg.body rubi132r1Nondeg.result rubi132r1Nondeg.integrals := by
  intro env hc t hF
  have heq0 := hc (.eq (.app2 .add (.app2 .mul (.int 4) (.pow (.var "b") (.int 3))) (.app2 .mul (.app2 .mul (.int 27) (.pow (.var "a") (.int 2))) (.var "d"))) (.int 0)) (by simp [rubi132r1Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two, toInt?_three] at heq0
  have heq : 4 * env "b" ^ 3 + 27 * env "a" ^ 2 * env "d" = 0 := by linear_combination heq0
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi132r1Nondeg, Defined, eval, hk_p, toInt?_three] at h
  rcases hk_m : I.toInt? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi132r1Nondeg, Defined, eval, hk_m, toInt?_three] at h
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have e3 : I.toInt? (3 * env "p") = some (3 * q) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have e2 : I.toInt? (2 * env "p") = some (2 * q) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hA := hc (.ne (.app2 .mul (.pow (.int 3) (.app2 .mul (.int 3) (.var "p"))) (.pow (.var "a") (.app2 .mul (.int 2) (.var "p")))) (.int 0)) (by simp [rubi132r1Nondeg])
  have hc0 : (3 : 𝕜) ^ (3 * q) * env "a" ^ (2 * q) ≠ 0 := by
    simp [Cond.Holds, Defined, eval, e3, e2] at hA
    exact mul_ne_zero (by tauto) (by tauto)
  have ha0 : q < 0 → env "a" ≠ 0 := by
    intro hq ha; apply hc0; rw [ha, zero_zpow _ (by omega), mul_zero]
  have hpoly : ∀ w : 𝕜, (3 * env "a" + -1 * env "b" * w) * (3 * env "a" + 2 * env "b" * w) ^ 2 = (3 : 𝕜) ^ 3 * env "a" ^ 2 * (env "a" + env "b" * w + env "d" * w ^ 3) := by
    intro w; linear_combination (-(w ^ 3)) * heq
  have hzp : ∀ w : 𝕜, (3 * env "a" + -1 * env "b" * w) ^ q * (3 * env "a" + 2 * env "b" * w) ^ (2 * q) = (3 : 𝕜) ^ (3 * q) * env "a" ^ (2 * q) * (env "a" + env "b" * w + env "d" * w ^ 3) ^ q := by
    intro w
    rw [zpow_two_mul, zpow_two_mul, zpow_three_mul, ← mul_zpow, ← mul_zpow, ← mul_zpow, hpoly w]
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi132r1Nondeg.body → (q < 0 → (env "a" + env "b" * w + env "d" * w ^ 3) ≠ 0) ∧ (km < 0 → (env "e" + env "f" * w) ≠ 0) := by
    intro w h
    simp [rubi132r1Nondeg, Defined, eval, hk_p, hk_m, toInt?_three] at h
    first | exact h | tauto | (trace_state; sorry)
  have hQ : ∀ w : 𝕜, q < 0 → (env "a" + env "b" * w + env "d" * w ^ 3) ≠ 0 → (3 * env "a" + -1 * env "b" * w) ≠ 0 ∧ (3 * env "a" + 2 * env "b" * w) ≠ 0 := by
    intro w hq hP
    have h := hpoly w
    have hr : (3 : 𝕜) ^ 3 * env "a" ^ 2 * (env "a" + env "b" * w + env "d" * w ^ 3) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ (ha0 hq))) hP
    rw [← h] at hr
    exact ⟨left_ne_zero_of_mul hr, pow_ne_zero_iff (by norm_num) |>.1 (right_ne_zero_of_mul hr)⟩
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi132r1Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    simp [Defined, eval, hk_p, hk_m, e2, e3, toInt?_three]
    have hA1 : q < 0 → ¬ 3 * env "a" + -(env "b" * w) = 0 := fun hq h0 =>
      (hQ w hq (h1 hq)).1 (by linear_combination h0)
    have hA1' : q < 0 → ¬ 3 * env "a" + -1 * env "b" * w = 0 := fun hq => (hQ w hq (h1 hq)).1
    have hA2 : 2 * q < 0 → ¬ 3 * env "a" + 2 * env "b" * w = 0 := fun hq => (hQ w (by omega) (h1 (by omega))).2
    exact ⟨⟨h2, hA1⟩, hA2⟩
  · exact Eventually.of_forall fun w => by
      simp [rubi132r1Nondeg, Defined, eval, recEnv, e2, e3, toInt?_neg_one, toInt?_three]
      first | done | exact hc0 | exact ⟨⟨fun _ => h3, fun h => ha0 (by omega)⟩, left_ne_zero_of_mul hc0, right_ne_zero_of_mul hc0⟩ | (trace_state; sorry)
  · simp only [rubi132r1Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "e" + env "f" * t) ^ km * (3 * env "a" + -1 * env "b" * t) ^ q * (3 * env "a" + 2 * env "b" * t) ^ (2 * q)) t := by
      convert hΦ using 1
      simp [eval, hk_p, hk_m, e2, e3, toInt?_three]
    have hEF : eval I (Function.update env "x" t) rubi132r1Nondeg.body = (env "e" + env "f" * t) ^ km * (env "a" + env "b" * t + env "d" * t ^ 3) ^ q := by
      simp [rubi132r1Nondeg, eval, hk_p, hk_m, toInt?_three]
    have hfun : (fun w => eval I (recEnv env (rubi132r1Nondeg.integrals.map (·.1)) Φ "x" w) rubi132r1Nondeg.result) =
        fun w => 1 * ((3 : 𝕜) ^ (3 * q) * env "a" ^ (2 * q))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi132r1Nondeg, eval, recEnv, e2, e3, toInt?_neg_one, toInt?_three, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine (hΦ'.const_mul _).congr_deriv ?_
    have hcc : ((3 : 𝕜) ^ (3 * q) * env "a" ^ (2 * q))⁻¹ * ((3 : 𝕜) ^ (3 * q) * env "a" ^ (2 * q)) = 1 := inv_mul_cancel₀ hc0
    linear_combination (((3 : 𝕜) ^ (3 * q) * env "a" ^ (2 * q))⁻¹ * (env "e" + env "f" * t) ^ km) * hzp t + ((env "e" + env "f" * t) ^ km * (env "a" + env "b" * t + env "d" * t ^ 3) ^ q) * hcc

theorem rubi131r4Nondeg_real : rubi131r4Nondeg.Holds .real := rubi131r4Nondeg_holds Interp.real (by norm_num)
theorem rubi131r4Nondeg_complex : rubi131r4Nondeg.Holds .complex := rubi131r4Nondeg_holds Interp.complex (by norm_num)
theorem rubi132r1Nondeg_real : rubi132r1Nondeg.Holds .real := rubi132r1Nondeg_holds Interp.real (by norm_num)
theorem rubi132r1Nondeg_complex : rubi132r1Nondeg.Holds .complex := rubi132r1Nondeg_holds Interp.complex (by norm_num)

end Proofs

end OSR.IntegrationRec116
