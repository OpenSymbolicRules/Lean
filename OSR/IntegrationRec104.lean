import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, eleventh batch

RUBI 1.2.3.2 #10 and #18 are refuted as stated (a coefficient the result
divides by may vanish).  With the non-degeneracy conditions of their results
they are proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec104

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_1_2_3_2_r10 with NeQ[Multiply[d, Add[m, Multiply[2, n, p], 1]], 0] -/
def rubi1232r10Nondeg : CRule where
  id := "integration.rubi_1_2_3_2_r10_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.var "d") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "n") (.var "p")) (.pow (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))]
  independent := ["a", "b", "c", "d", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")), .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0), .int (.var "n"), .gt (.var "n") (.int 0), .int (.var "p"), .gt (.var "p") (.int 0), .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1)) (.int 0),
    .ne (.app2 .mul (.var "d") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1))) (.int 0)]
  priority := 9221
  description := "rubi_1_2_3_2_r10 with NeQ[Multiply[d, Add[m, Multiply[2, n, p], 1]], 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:10" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p.m#10"

/-- rubi_1_2_3_2_r18 with NeQ[Multiply[c, Add[m, Multiply[-1, 2, n], 1]], 0]; NeQ[c, 0] -/
def rubi1232r18Nondeg : CRule where
  id := "integration.rubi_1_2_3_2_r18_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "d") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.app2 .mul (.int 2) (.var "n")))) (.pow (.var "c") (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.int (-1))))]
  independent := ["a", "b", "c", "d", "m", "n", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")), .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0), .int (.var "n"), .gt (.var "n") (.int 0), .gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.int 0),
    .ne (.var "c") (.int 0)]
  priority := 9222
  description := "rubi_1_2_3_2_r18 with NeQ[Multiply[c, Add[m, Multiply[-1, 2, n], 1]], 0]; NeQ[c, 0]"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:18" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p.m#18"


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

theorem rubi1232r10Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1232r10Nondeg.conditions rubi1232r10Nondeg.body rubi1232r10Nondeg.result rubi1232r10Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1232r10Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have gn := hc (.gt (.var "n") (.int 0)) (by simp [rubi1232r10Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1232r10Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1232r10Nondeg, Defined, eval, hk_m, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1232r10Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn; rw [h_n] at gn; exact ord _ _ (by simpa using gn)
  have e2 : I.toInt? (env "n2") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [hn2, h_n]; push_cast; ring)
  have e2' : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have em1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ej21 : I.toInt? (2 * env "n" + -1 * 1) = some (2 * j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have ej21' : I.toInt? (2 * env "n" + -1) = some (2 * j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have ek2 : I.toInt? (env "m" + -1 * 2 * env "n") = some (k - 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ek2' : I.toInt? (env "m" + -(2 * env "n")) = some (k - 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ek21 : I.toInt? (env "m" + -1 * 2 * env "n" + 1) = some (k - 2 * j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ek21' : I.toInt? (env "m" + -(2 * env "n") + 1) = some (k - 2 * j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have hsq : ∀ w : 𝕜, w ^ (2 * j) = (w ^ j) ^ 2 := by
    intro w; rw [mul_comm, zpow_mul]; norm_cast
  have hj0 : ¬ j < 0 := by omega
  have hj2 : ¬ 2 * j < 0 := by omega
  have hY := hasDerivAt_zpow j t (Or.inr (by omega))
  have hQd : HasDerivAt (fun w => (env "a" + env "b" * w ^ j + env "c" * (w ^ j) ^ 2)) (env "b" * ((j : 𝕜) * t ^ (j - 1)) + env "c" * ((2 : ℕ) * (t ^ j) ^ (2 - 1) * ((j : 𝕜) * t ^ (j - 1)))) t :=
    ((hY.const_mul (env "b")).const_add (env "a")).add ((hY.pow 2).const_mul (env "c"))
  have rtj : t ^ j = t ^ (j - 1) * t := by
    rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
  have ep1 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have gp := hc (.gt (.var "p") (.int 0)) (by simp [rubi1232r10Nondeg])
  have hq : 0 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp; rw [h_p] at gp; exact ord _ _ (by simpa using gp)
  have hq0 : ¬ q < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hA0 := hc (.ne (.app2 .mul (.var "d") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1))) (.int 0)) (by simp [rubi1232r10Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hK0 := hc (.ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1)) (.int 0)) (by simp [rubi1232r10Nondeg])
  simp [Cond.Holds, Defined, eval] at hK0
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1232r10Nondeg.body → (k < 0 → (env "d" * w) ≠ 0) := by
    intro w h
    simp [rubi1232r10Nondeg, Defined, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ej21, ej21', ek2, ek2', ek21, ek21', toInt?_neg_one, toInt?_two, ep1, ep1', hj0, hj2, hq0] at h
    first | exact fun hk => mul_ne_zero (h hk).1 (h hk).2 | exact fun hk => mul_ne_zero (h.1 hk).1 (h.1 hk).2 | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1232r10Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h1 := hBody w hw
    simp [Defined, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ej21, ej21', ek2, ek2', ek21, ek21', toInt?_neg_one, toInt?_two, ep1, ep1', hj0, hj2, hq1]
    first | done | exact fun hk => ⟨left_ne_zero_of_mul (h1 hk), right_ne_zero_of_mul (h1 hk)⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h1 := hBody w hw
    simp [rubi1232r10Nondeg, Defined, eval, recEnv, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ej21, ej21', ek2, ek2', ek21, ek21', toInt?_neg_one, toInt?_two, ep1, ep1', hj0, hj2, hq0, hA0, hK0]
    first | done | exact fun hk => right_ne_zero_of_mul (h1 (by omega)) | exact fun hk => ⟨left_ne_zero_of_mul (h1 (by omega)), right_ne_zero_of_mul (h1 (by omega))⟩ | (trace_state; sorry)
  · simp only [rubi1232r10Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hE' := hBody t hF.self_of_nhds
    have hE0 : (env "d" * t) ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hE' h)
      · exact Or.inr (by omega)
    have hE1 : (env "d" * t) ≠ 0 ∨ 0 ≤ k + 1 := by
      rcases hE0 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * t) ^ k * (2 * env "a" + env "b" * t ^ j) * (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ (q - 1)) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ej21, ej21', ek2, ek2', ek21, ek21', toInt?_neg_one, toInt?_two, ep1, ep1']
    have hEF : eval I (Function.update env "x" t) rubi1232r10Nondeg.body = (env "d" * t) ^ k * (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ q := by
      simp [rubi1232r10Nondeg, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ej21, ej21', ek2, ek2', ek21, ek21', toInt?_neg_one, toInt?_two, ep1, ep1']
    have hfun : (fun w => eval I (recEnv env (rubi1232r10Nondeg.integrals.map (·.1)) Φ "x" w) rubi1232r10Nondeg.result) =
        fun w => (env "d" * w) ^ (k + 1) * (env "a" + env "b" * w ^ j + env "c" * (w ^ j) ^ 2) ^ q * (env "d" * (env "m" + 2 * env "n" * env "p" + 1))⁻¹ +
          env "n" * env "p" * (env "m" + 2 * env "n" * env "p" + 1)⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1232r10Nondeg, eval, recEnv, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ej21, ej21', ek2, ek2', ek21, ek21', toInt?_neg_one, toInt?_two, ep1, ep1', -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hEp := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ hE1) ((hasDerivAt_id' t).const_mul (env "d"))
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow q _ (Or.inr (by omega))) hQd
    refine (((hEp.mul hQp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hE0, show (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ q = (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ (q - 1) * (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]]
    generalize (env "d" * t) ^ k = Ek
    generalize (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2) ^ (q - 1) = Qp
    rw [rtj]
    generalize t ^ (j - 1) = T1
    simp only [h_m, h_n, h_p] at *
    casesm* _ ∧ _
    generalize hKe : (k : 𝕜) + 2 * (j : 𝕜) * (q : 𝕜) + 1 = K at *
    field_simp
    rw [← hKe]
    push_cast
    ring

theorem rubi1232r18Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1232r18Nondeg.conditions rubi1232r18Nondeg.body rubi1232r18Nondeg.result rubi1232r18Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1232r18Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have gn := hc (.gt (.var "n") (.int 0)) (by simp [rubi1232r18Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1232r18Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1232r18Nondeg, Defined, eval, hk_m, hk_n] at h
  have hk_p : I.toInt? (-1 : 𝕜) = some (-1) := toInt?_neg_one I
  have h_p : True := trivial
  let q : ℤ := 0
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn; rw [h_n] at gn; exact ord _ _ (by simpa using gn)
  have e2 : I.toInt? (env "n2") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [hn2, h_n]; push_cast; ring)
  have e2' : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have em1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ej21 : I.toInt? (2 * env "n" + -1 * 1) = some (2 * j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have ej21' : I.toInt? (2 * env "n" + -1) = some (2 * j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have ek2 : I.toInt? (env "m" + -1 * 2 * env "n") = some (k - 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ek2' : I.toInt? (env "m" + -(2 * env "n")) = some (k - 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ek21 : I.toInt? (env "m" + -1 * 2 * env "n" + 1) = some (k - 2 * j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ek21' : I.toInt? (env "m" + -(2 * env "n") + 1) = some (k - 2 * j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have hsq : ∀ w : 𝕜, w ^ (2 * j) = (w ^ j) ^ 2 := by
    intro w; rw [mul_comm, zpow_mul]; norm_cast
  have hj0 : ¬ j < 0 := by omega
  have hj2 : ¬ 2 * j < 0 := by omega
  have hY := hasDerivAt_zpow j t (Or.inr (by omega))
  have hQd : HasDerivAt (fun w => (env "a" + env "b" * w ^ j + env "c" * (w ^ j) ^ 2)) (env "b" * ((j : 𝕜) * t ^ (j - 1)) + env "c" * ((2 : ℕ) * (t ^ j) ^ (2 - 1) * ((j : 𝕜) * t ^ (j - 1)))) t :=
    ((hY.const_mul (env "b")).const_add (env "a")).add ((hY.pow 2).const_mul (env "c"))
  have rtj : t ^ j = t ^ (j - 1) * t := by
    rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
  have gm := hc (.gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi1232r18Nondeg])
  have hk : 2 * j - 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m, h_n] at gm
    exact ord _ _ (by push_cast; simpa [sub_eq_add_neg] using gm)
  have hk0 : ¬ k < 0 := by omega
  have hkj : ¬ k - 2 * j < 0 := by omega
  have hkj1 : ¬ k - 2 * j + 1 < 0 := by omega
  have hj21 : ¬ 2 * j - 1 < 0 := by omega
  have hA0 := hc (.ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.int 0)) (by simp [rubi1232r18Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hc0 : env "c" ≠ 0 := by
    have h := hc (.ne (.var "c") (.int 0)) (by simp [rubi1232r18Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1232r18Nondeg.body → (env "a" + env "b" * w ^ j + env "c" * (w ^ j) ^ 2) ≠ 0 := by
    intro w h
    simp [rubi1232r18Nondeg, Defined, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ej21, ej21', ek2, ek2', ek21, ek21', toInt?_neg_one, toInt?_two, hj0, hj2, hk0] at h
    first | exact h | exact h.2 | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1232r18Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h1 := hBody w hw
    simp [Defined, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ej21, ej21', ek2, ek2', ek21, ek21', toInt?_neg_one, toInt?_two, hj0, hj2, hkj, h1]
  · filter_upwards [hF] with w hw
    simp [rubi1232r18Nondeg, Defined, eval, recEnv, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ej21, ej21', ek2, ek2', ek21, ek21', toInt?_neg_one, toInt?_two, hj0, hj2, hj21, hkj1, hA0, hc0]
  · simp only [rubi1232r18Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hQ0 := hBody t hF.self_of_nhds
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" * t) ^ (k - 2 * j) * (env "a" + env "b" * t ^ j) * (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ej21, ej21', ek2, ek2', ek21, ek21', toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1232r18Nondeg.body = (env "d" * t) ^ k * (env "a" + env "b" * t ^ j + env "c" * (t ^ j) ^ 2)⁻¹ := by
      simp [rubi1232r18Nondeg, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ej21, ej21', ek2, ek2', ek21, ek21', toInt?_neg_one, toInt?_two]
    have hfun : (fun w => eval I (recEnv env (rubi1232r18Nondeg.integrals.map (·.1)) Φ "x" w) rubi1232r18Nondeg.result) =
        fun w => env "d" ^ (2 * j - 1) * (env "d" * w) ^ (k - 2 * j + 1) * (env "c" * (env "m" + -1 * 2 * env "n" + 1))⁻¹ +
          -1 * env "d" ^ (2 * j) * (env "c")⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1232r18Nondeg, eval, recEnv, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ej21, ej21', ek2, ek2', ek21, ek21', toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hEp := HasDerivAt.comp t (hasDerivAt_zpow (k - 2 * j + 1) _ (Or.inr (by omega))) ((hasDerivAt_id' t).const_mul (env "d"))
    refine (((hEp.const_mul (env "d" ^ (2 * j - 1))).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    have za : ∀ (A : 𝕜) (x y : ℤ), 0 ≤ x → 0 ≤ y → A ^ (x + y) = A ^ x * A ^ y := by
      intro A x y hx hy
      lift x to ℕ using hx
      lift y to ℕ using hy
      rw [← Nat.cast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]
    rw [show (env "d" * t) ^ k = (env "d" * t) ^ (k - 2 * j) * (env "d" * t) ^ (2 * j) by rw [← za _ _ _ (by omega) (by omega)]; congr 1; ring,
      mul_zpow (env "d") t (2 * j), hsq t,
      show env "d" ^ (2 * j) = env "d" ^ (2 * j - 1) * env "d" by rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]]
    generalize (env "d" * t) ^ (k - 2 * j) = Ek
    generalize env "d" ^ (2 * j - 1) = D1
    generalize t ^ j = Y at hQ0 ⊢
    simp only [h_m, h_n] at *
    casesm* _ ∧ _
    field_simp
    push_cast
    ring

theorem rubi1232r10Nondeg_real : rubi1232r10Nondeg.Holds .real := rubi1232r10Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1232r10Nondeg_complex : rubi1232r10Nondeg.Holds .complex := rubi1232r10Nondeg_holds Interp.complex Interp.complex_lt_rat
theorem rubi1232r18Nondeg_real : rubi1232r18Nondeg.Holds .real := rubi1232r18Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1232r18Nondeg_complex : rubi1232r18Nondeg.Holds .complex := rubi1232r18Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec104
