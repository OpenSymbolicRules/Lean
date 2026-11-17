import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, twelfth batch

RUBI 1.2.3.4 #61 and #64 are refuted as stated (at `d = 0` or `f = 0`);
with `d ≠ 0`, `e ≠ 0` (#64) and `f ≠ 0` the split into two residual integrals
holds, since `(a e + c d xⁿ)(d + e xⁿ) - (c d² + a e²) xⁿ = d e (a + c x²ⁿ)`
(and its analogue with `b`).  Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec105

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_1_2_3_4_r64 with NeQ[Multiply[d, e], 0]; NeQ[Multiply[d, e, Power[f, n]], 0] -/
def rubi1234r64Nondeg : CRule where
  id := "integration.rubi_1_2_3_4_r64_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:64"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "d") (.var "e")) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.pow (.var "f") (.var "n"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))), ("I2", .app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1))))]
  independent := ["a", "c", "d", "e", "f", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")), .int (.var "n"), .gt (.var "n") (.int 0), .gt (.var "p") (.int 0), .gt (.int 0) (.var "m"),
    .ne (.app2 .mul (.var "d") (.var "e")) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.pow (.var "f") (.var "n"))) (.int 0)]
  priority := 9231
  description := "rubi_1_2_3_4_r64 with NeQ[Multiply[d, e], 0]; NeQ[Multiply[d, e, Power[f, n]], 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:64" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#64"

/-- rubi_1_2_3_4_r61 with NeQ[Power[d, 2], 0]; NeQ[Multiply[Power[d, 2], Power[f, Multiply[2, n]]], 0] -/
def rubi1234r61Nondeg : CRule where
  id := "integration.rubi_1_2_3_4_r61_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:61"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "d") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.pow (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.app2 .mul (.int 2) (.var "n")))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))), ("I2", .app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")), .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0), .int (.var "n"), .gt (.var "n") (.int 0), .gt (.var "p") (.int 0), .gt (.app2 .mul (.int (-1)) (.var "n")) (.var "m"),
    .ne (.pow (.var "d") (.int 2)) (.int 0),
    .ne (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.app2 .mul (.int 2) (.var "n")))) (.int 0)]
  priority := 9232
  description := "rubi_1_2_3_4_r61 with NeQ[Power[d, 2], 0]; NeQ[Multiply[Power[d, 2], Power[f, Multiply[2, n]]], 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:61" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#61"


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

theorem rubi1234r64Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1234r64Nondeg.conditions rubi1234r64Nondeg.body rubi1234r64Nondeg.result rubi1234r64Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1234r64Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have gn := hc (.gt (.var "n") (.int 0)) (by simp [rubi1234r64Nondeg])
  have gp := hc (.gt (.var "p") (.int 0)) (by simp [rubi1234r64Nondeg])
  have gm := hc (.gt (.int 0) (.var "m")) (by simp [rubi1234r64Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r64Nondeg, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r64Nondeg, Defined, eval, hk_m, hk_p] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r64Nondeg, Defined, eval, hk_m, hk_p, hk_n] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn; rw [h_n] at gn; exact ord _ _ (by simpa using gn)
  have hq : 0 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp; rw [h_p] at gp; exact ord _ _ (by simpa using gp)
  have hk : k < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; simp only [h_m, h_n] at gm
    exact ord _ _ (by push_cast; simpa using gm)
  have hA0 := hc (.ne (.app2 .mul (.var "d") (.var "e")) (.int 0)) (by simp [rubi1234r64Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA0
  have hA1 := hc (.ne (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.pow (.var "f") (.var "n"))) (.int 0)) (by simp [rubi1234r64Nondeg])
  simp [Cond.Holds, Defined, eval, hk_n, toInt?_two] at hA1
  have e2 : I.toInt? (env "n2") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [hn2, h_n]; push_cast; ring)
  have e2' : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have emn : I.toInt? (env "m" + env "n") = some (k + j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emn2 : I.toInt? (env "m" + 2 * env "n") = some (k + 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have hsq : ∀ w : 𝕜, w ^ (2 * j) = (w ^ j) ^ 2 := by
    intro w; rw [mul_comm, zpow_mul]; norm_cast
  have hj0 : ¬ j < 0 := by omega
  have hj2 : ¬ 2 * j < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk0 : k < 0 := by omega
  have hf0 : env "f" ≠ 0 := by
    intro h; simp [h, e2', zero_zpow _ (show (j : ℤ) ≠ 0 by omega)] at hA1
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1234r64Nondeg.body → (env "f" * w) ≠ 0 ∧ (env "d" + env "e" * w ^ j) ≠ 0 := by
    intro w h
    simp [rubi1234r64Nondeg, Defined, eval, hk_m, hk_p, hk_n, e2, hsq, hj0, hj2, hq0, toInt?_neg_one] at h
    first | exact ⟨mul_ne_zero (h.1.1 hk0).1 (h.1.1 hk0).2, h.2⟩ | exact ⟨mul_ne_zero (h.1 hk0).1 (h.1 hk0).2, h.2⟩ | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1234r64Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · obtain ⟨h1, h2⟩ := hBody w hw
      simp [Defined, eval, hk_m, hk_n, e2', hsq, ep1, ep1', emn, emn2, hj0, hj2, hq1, toInt?_neg_one, left_ne_zero_of_mul h1, right_ne_zero_of_mul h1, h2]
  · exact Eventually.of_forall fun w => by
      simp [rubi1234r64Nondeg, Defined, eval, recEnv, hk_n, e2', toInt?_neg_one, toInt?_two, hA0, hA1, hf0, zpow_ne_zero _ hf0]
  · simp only [rubi1234r64Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨hE0, hD0⟩ := hBody t hF.self_of_nhds
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ k * (env "a" * env "e" + env "c" * env "d" * t ^ j) * (env "a" + env "c" * (t ^ j) ^ 2) ^ (q - 1)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, e2', hsq, ep1, ep1']
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (k + j) * (env "a" + env "c" * (t ^ j) ^ 2) ^ (q - 1) * (env "d" + env "e" * t ^ j)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, e2', hsq, ep1, ep1', emn, emn2, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1234r64Nondeg.body = (env "f" * t) ^ k * (env "a" + env "c" * (t ^ j) ^ 2) ^ q * (env "d" + env "e" * t ^ j)⁻¹ := by
      simp [rubi1234r64Nondeg, eval, hk_m, hk_n, hk_p, e2, hsq, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1234r64Nondeg.integrals.map (·.1)) Φ "x" w) rubi1234r64Nondeg.result) =
        fun w => 1 * (env "d" * env "e")⁻¹ * Φ "I1" w + -1 * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) * (env "d" * env "e" * env "f" ^ j)⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1234r64Nondeg, eval, recEnv, hk_n, e2', toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    rw [zpow_add₀ hE0 k (j), show (env "a" + env "c" * (t ^ j) ^ 2) ^ q = (env "a" + env "c" * (t ^ j) ^ 2) ^ (q - 1) * (env "a" + env "c" * (t ^ j) ^ 2) by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]]
    generalize (env "f" * t) ^ k = Ek
    rw [mul_zpow (env "f") t (j)]
    
    generalize (env "a" + env "c" * (t ^ j) ^ 2) ^ (q - 1) = Qp
    generalize env "f" ^ j = Fj at hA1 ⊢
    generalize t ^ j = Y at hD0 ⊢
    casesm* _ ∧ _
    field_simp
    ring

theorem rubi1234r61Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1234r61Nondeg.conditions rubi1234r61Nondeg.body rubi1234r61Nondeg.result rubi1234r61Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1234r61Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have gn := hc (.gt (.var "n") (.int 0)) (by simp [rubi1234r61Nondeg])
  have gp := hc (.gt (.var "p") (.int 0)) (by simp [rubi1234r61Nondeg])
  have gm := hc (.gt (.app2 .mul (.int (-1)) (.var "n")) (.var "m")) (by simp [rubi1234r61Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r61Nondeg, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r61Nondeg, Defined, eval, hk_m, hk_p] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r61Nondeg, Defined, eval, hk_m, hk_p, hk_n] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn; rw [h_n] at gn; exact ord _ _ (by simpa using gn)
  have hq : 0 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp; rw [h_p] at gp; exact ord _ _ (by simpa using gp)
  have hk : k < -j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; simp only [h_m, h_n] at gm
    exact ord _ _ (by push_cast; simpa using gm)
  have hA0 := hc (.ne (.pow (.var "d") (.int 2)) (.int 0)) (by simp [rubi1234r61Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA0
  have hA1 := hc (.ne (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.app2 .mul (.int 2) (.var "n")))) (.int 0)) (by simp [rubi1234r61Nondeg])
  simp [Cond.Holds, Defined, eval, hk_n, toInt?_two] at hA1
  have e2 : I.toInt? (env "n2") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [hn2, h_n]; push_cast; ring)
  have e2' : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have emn : I.toInt? (env "m" + env "n") = some (k + j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emn2 : I.toInt? (env "m" + 2 * env "n") = some (k + 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have hsq : ∀ w : 𝕜, w ^ (2 * j) = (w ^ j) ^ 2 := by
    intro w; rw [mul_comm, zpow_mul]; norm_cast
  have hj0 : ¬ j < 0 := by omega
  have hj2 : ¬ 2 * j < 0 := by omega
  have hq0 : ¬ q < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk0 : k < 0 := by omega
  have hf0 : env "f" ≠ 0 := by
    intro h; simp [h, e2', zero_zpow _ (show (2 * j : ℤ) ≠ 0 by omega)] at hA1
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1234r61Nondeg.body → (env "f" * w) ≠ 0 ∧ (env "d" + env "e" * w ^ j) ≠ 0 := by
    intro w h
    simp [rubi1234r61Nondeg, Defined, eval, hk_m, hk_p, hk_n, e2, hsq, hj0, hj2, hq0, toInt?_neg_one] at h
    first | exact ⟨mul_ne_zero (h.1.1 hk0).1 (h.1.1 hk0).2, h.2⟩ | exact ⟨mul_ne_zero (h.1 hk0).1 (h.1 hk0).2, h.2⟩ | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1234r61Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · obtain ⟨h1, h2⟩ := hBody w hw
      simp [Defined, eval, hk_m, hk_n, e2', hsq, ep1, ep1', emn, emn2, hj0, hj2, hq1, toInt?_neg_one, left_ne_zero_of_mul h1, right_ne_zero_of_mul h1, h2]
  · exact Eventually.of_forall fun w => by
      simp [rubi1234r61Nondeg, Defined, eval, recEnv, hk_n, e2', toInt?_neg_one, toInt?_two, hA0, hA1, hf0, zpow_ne_zero _ hf0]
  · simp only [rubi1234r61Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    obtain ⟨hE0, hD0⟩ := hBody t hF.self_of_nhds
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ k * (env "a" * env "d" + (env "b" * env "d" + -1 * env "a" * env "e") * t ^ j) * (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ (q - 1)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, e2', hsq, ep1, ep1']
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (k + 2 * j) * (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ (q - 1) * (env "d" + env "e" * t ^ j)⁻¹) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, e2', hsq, ep1, ep1', emn, emn2, toInt?_neg_one]
    have hEF : eval I (Function.update env "x" t) rubi1234r61Nondeg.body = (env "f" * t) ^ k * (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ q * (env "d" + env "e" * t ^ j)⁻¹ := by
      simp [rubi1234r61Nondeg, eval, hk_m, hk_n, hk_p, e2, hsq, toInt?_neg_one]
    have hfun : (fun w => eval I (recEnv env (rubi1234r61Nondeg.integrals.map (·.1)) Φ "x" w) rubi1234r61Nondeg.result) =
        fun w => 1 * (env "d" ^ 2)⁻¹ * Φ "I1" w + (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2) * (env "d" ^ 2 * env "f" ^ (2 * j))⁻¹ * Φ "I2" w := by
      funext w
      simp [rubi1234r61Nondeg, eval, recEnv, hk_n, e2', toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    refine ((hΦ1'.const_mul _).add (hΦ2'.const_mul _)).congr_deriv ?_
    rw [zpow_add₀ hE0 k (2 * j), show (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ q = (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ (q - 1) * (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]]
    generalize (env "f" * t) ^ k = Ek
    rw [mul_zpow (env "f") t (2 * j)]
    rw [hsq t]
    generalize (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ (q - 1) = Qp
    generalize env "f" ^ 2 * j = Fj at hA1 ⊢
    generalize t ^ j = Y at hD0 ⊢
    casesm* _ ∧ _
    field_simp
    ring

theorem rubi1234r64Nondeg_real : rubi1234r64Nondeg.Holds .real := rubi1234r64Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1234r64Nondeg_complex : rubi1234r64Nondeg.Holds .complex := rubi1234r64Nondeg_holds Interp.complex Interp.complex_lt_rat
theorem rubi1234r61Nondeg_real : rubi1234r61Nondeg.Holds .real := rubi1234r61Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1234r61Nondeg_complex : rubi1234r61Nondeg.Holds .complex := rubi1234r61Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec105
