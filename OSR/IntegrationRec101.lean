import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, eighth batch

RUBI 1.2.1.2 #40, #46 and #96 are refuted as stated (a coefficient the result
divides by may vanish).  With the non-degeneracy conditions of their results
they are proved over ℝ and ℂ; for #40 and #46 the condition `c d² + a e² = 0`
eliminates `a`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec101

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_1_2_1_2_r40 with the non-degeneracy conditions of its result -/
def rubi1212r40Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r40_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:40"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "c", "d", "e", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0), .gt (.int (-1)) (.var "p"), .gt (.var "m") (.int 0), .int (.app2 .mul (.int 2) (.var "p")),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9190
  description := "rubi_1_2_1_2_r40 with the non-degeneracy conditions of its result"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:40" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#40"

/-- rubi_1_2_1_2_r46 with the non-degeneracy conditions of its result -/
def rubi1212r46Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r46_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:46"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))]
  independent := ["a", "c", "d", "e", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0), .gt (.int 0) (.var "m"), .ne (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0), .int (.app2 .mul (.int 2) (.var "p")),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int 0)]
  priority := 9191
  description := "rubi_1_2_1_2_r46 with the non-degeneracy conditions of its result"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:46" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#46"

/-- rubi_1_2_1_2_r96 with the non-degeneracy conditions of its result -/
def rubi1212r96Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r96_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:96"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0), .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0), .gt (.int (-1)) (.var "p"),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9192
  description := "rubi_1_2_1_2_r96 with the non-degeneracy conditions of its result"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:96" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#96"


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

theorem rubi1212r40Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1212r40Nondeg.conditions rubi1212r40Nondeg.body rubi1212r40Nondeg.result rubi1212r40Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1212r40Nondeg, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1212r40Nondeg, Defined, eval, hk_m, hk_p, toInt?_two] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have em1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : I.toInt? (env "m" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2' : I.toInt? (env "m" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em3 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1212r40Nondeg.body → (k < 0 → (env "d" + env "e" * w) ≠ 0) ∧ (q < 0 → (env "a" + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1212r40Nondeg, Defined, eval, hk_m, hk_p, toInt?_two] at h
    first | exact h | exact ⟨h.1, h.2⟩ | tauto
  have hDd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
    simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
  have hQd : HasDerivAt (fun w => (env "a" + env "c" * w ^ 2)) (env "c" * (2 * t)) t := by
    have := ((hasDerivAt_pow 2 t).const_mul (env "c")).const_add (env "a")
    convert this using 1
    norm_num
  have heq := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r40Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at heq
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r40Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hA1 := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r40Nondeg])
  simp [Cond.Holds, Defined, eval] at hA1
  have ha0 : env "a" ≠ 0 := by intro h; simp [h] at hA0
  have he0 : env "e" ≠ 0 := by intro h; simp [h] at hA0
  have hp0 : env "p" + 1 ≠ 0 := by intro h; simp [h] at hA0
  have hc0 : env "c" ≠ 0 := by intro h; simp [h, ha0, he0] at heq
  have hd0 : env "d" ≠ 0 := by intro h; simp [h, ha0, he0] at heq
  have gp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1212r40Nondeg])
  have gm := hc (.gt (.var "m") (.int 0)) (by simp [rubi1212r40Nondeg])
  have hq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp; rw [h_p] at gp; exact ord _ _ (by simpa using gp)
  have hk : 0 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by simpa using gm)
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r40Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨-, hQ⟩ := hBody w hw
    simp [Defined, eval, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two, hk1]
    first | exact fun _ => hQ (by omega) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨-, hQ⟩ := hBody w hw
    simp [rubi1212r40Nondeg, Defined, eval, recEnv, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two, hk0, hA0, hA1]
    first | exact fun _ => hQ (by omega) | (trace_state; sorry)
  · simp only [rubi1212r40Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hQ0 : (env "a" + env "c" * t ^ 2) ≠ 0 := (hBody t hF.self_of_nhds).2 (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k - 1) * (env "a" + env "c" * t ^ 2) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1212r40Nondeg.body = (env "d" + env "e" * t) ^ k * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r40Nondeg, eval, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two]
    have hfun : (fun w => eval I (recEnv env (rubi1212r40Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r40Nondeg.result) =
        fun w => -1 * env "d" * (env "d" + env "e" * w) ^ k * (env "a" + env "c" * w ^ 2) ^ (q + 1) * (2 * env "a" * env "e" * (env "p" + 1))⁻¹ +
          env "d" * (env "m" + 2 * env "p" + 2) * (2 * env "a" * (env "p" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1212r40Nondeg, eval, recEnv, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hDp := HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inr (by omega))) hDd
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ (Or.inl hQ0)) hQd
    refine ((((hDp.const_mul (-1 * env "d")).mul hQp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [show (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 1) * (env "d" + env "e" * t) by rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel],
      zpow_add_one₀ hQ0]
    generalize (env "d" + env "e" * t) ^ (k - 1) = Dk
    generalize (env "a" + env "c" * t ^ 2) ^ q = Qp
    have ha : env "a" = -(env "c" * env "d" ^ 2) / env "e" ^ 2 := by
      field_simp; linear_combination heq
    rw [h_m, h_p] at *
    rw [ha]
    rw [h_p] at hp0
    field_simp
    push_cast
    ring

theorem rubi1212r46Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1212r46Nondeg.conditions rubi1212r46Nondeg.body rubi1212r46Nondeg.result rubi1212r46Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1212r46Nondeg, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1212r46Nondeg, Defined, eval, hk_m, hk_p, toInt?_two] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have em1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : I.toInt? (env "m" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2' : I.toInt? (env "m" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em3 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1212r46Nondeg.body → (k < 0 → (env "d" + env "e" * w) ≠ 0) ∧ (q < 0 → (env "a" + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1212r46Nondeg, Defined, eval, hk_m, hk_p, toInt?_two] at h
    first | exact h | exact ⟨h.1, h.2⟩ | tauto
  have hDd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
    simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
  have hQd : HasDerivAt (fun w => (env "a" + env "c" * w ^ 2)) (env "c" * (2 * t)) t := by
    have := ((hasDerivAt_pow 2 t).const_mul (env "c")).const_add (env "a")
    convert this using 1
    norm_num
  have heq := hc (.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r46Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at heq
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int 0)) (by simp [rubi1212r46Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hA1 := hc (.ne (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int 0)) (by simp [rubi1212r46Nondeg])
  simp [Cond.Holds, Defined, eval] at hA1
  have hc0 : env "c" ≠ 0 := by intro h; simp [h] at hA0
  have hd0 : env "d" ≠ 0 := by intro h; simp [h] at hA0
  have hmp : env "m" + env "p" + 1 ≠ 0 := by intro h; simp [h] at hA0
  have ha0 : env "a" ≠ 0 := by intro h; simp [h, hc0, hd0] at heq
  have he0 : env "e" ≠ 0 := by intro h; simp [h, hc0, hd0] at heq
  have gm := hc (.gt (.int 0) (.var "m")) (by simp [rubi1212r46Nondeg])
  have hk : k < 0 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by simpa using gm)
  have hk1 : k + 1 < 0 ∨ ¬ k + 1 < 0 := em _
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r46Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨hD, hQ⟩ := hBody w hw
    simp [Defined, eval, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two]
    first | exact ⟨fun _ => hD hk, hQ⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨hD, hQ⟩ := hBody w hw
    simp [rubi1212r46Nondeg, Defined, eval, recEnv, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two, hA0, hA1]
    first | exact ⟨fun _ => hD hk, fun h => hQ (by omega)⟩ | (trace_state; sorry)
  · simp only [rubi1212r46Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hD0', hQ0'⟩ := hBody t hF.self_of_nhds
    have hD0 : (env "d" + env "e" * t) ≠ 0 := hD0' hk
    have hQq : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (hQ0' h)
      · exact Or.inr (by omega)
    have hQq1 : (env "a" + env "c" * t ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      rcases hQq with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k + 1) * (env "a" + env "c" * t ^ 2) ^ q) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1212r46Nondeg.body = (env "d" + env "e" * t) ^ k * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r46Nondeg, eval, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two]
    have hfun : (fun w => eval I (recEnv env (rubi1212r46Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r46Nondeg.result) =
        fun w => -1 * env "e" * (env "d" + env "e" * w) ^ k * (env "a" + env "c" * w ^ 2) ^ (q + 1) * (2 * env "c" * env "d" * (env "m" + env "p" + 1))⁻¹ +
          (env "m" + 2 * env "p" + 2) * (2 * env "d" * (env "m" + env "p" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1212r46Nondeg, eval, recEnv, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hDp := HasDerivAt.comp t (hasDerivAt_zpow k _ (Or.inl hD0)) hDd
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hQq1) hQd
    refine ((((hDp.const_mul (-1 * env "e")).mul hQp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_succ_of _ _ hQq, show (env "d" + env "e" * t) ^ (k + 1) = (env "d" + env "e" * t) ^ (k - 1) * (env "d" + env "e" * t) * (env "d" + env "e" * t) by
      rw [zpow_add_one₀ hD0, ← zpow_add_one₀ hD0 (k - 1), sub_add_cancel],
      show (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 1) * (env "d" + env "e" * t) by rw [← zpow_add_one₀ hD0, sub_add_cancel]]
    generalize (env "d" + env "e" * t) ^ (k - 1) = Dk
    generalize (env "a" + env "c" * t ^ 2) ^ q = Qp
    have ha : env "a" = -(env "c" * env "d" ^ 2) / env "e" ^ 2 := by
      field_simp; linear_combination heq
    rw [ha]
    rw [h_m, h_p] at *
    field_simp
    push_cast
    ring

theorem rubi1212r96Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1212r96Nondeg.conditions rubi1212r96Nondeg.body rubi1212r96Nondeg.result rubi1212r96Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1212r96Nondeg, Defined, eval, hk_m] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1212r96Nondeg, Defined, eval, hk_m, hk_p, toInt?_two] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have em1 : I.toInt? (env "m" + -1 * 1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em1' : I.toInt? (env "m" + -1) = some (k - 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : I.toInt? (env "m" + -1 * 2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2' : I.toInt? (env "m" + -2) = some (k - 2) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em3 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1212r96Nondeg.body → (k < 0 → (env "d" + env "e" * w) ≠ 0) ∧ (q < 0 → (env "a" + env "c" * w ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1212r96Nondeg, Defined, eval, hk_m, hk_p, toInt?_two] at h
    first | exact h | exact ⟨h.1, h.2⟩ | tauto
  have hDd : HasDerivAt (fun w => (env "d" + env "e" * w)) (env "e") t := by
    simpa using ((hasDerivAt_id' t).const_mul (env "e")).const_add (env "d")
  have hQd : HasDerivAt (fun w => (env "a" + env "c" * w ^ 2)) (env "c" * (2 * t)) t := by
    have := ((hasDerivAt_pow 2 t).const_mul (env "c")).const_add (env "a")
    convert this using 1
    norm_num
  have hne := hc (.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)) (by simp [rubi1212r96Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hne
  have hmeq := hc (.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0)) (by simp [rubi1212r96Nondeg])
  simp [Cond.Holds, Defined, eval] at hmeq
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1212r96Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have ha0 : env "a" ≠ 0 := by intro h; simp [h] at hA0
  have hc0 : env "c" ≠ 0 := by intro h; simp [h] at hA0
  have hp0 : env "p" + 1 ≠ 0 := by intro h; simp [h] at hA0
  have gp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1212r96Nondeg])
  have hq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp; rw [h_p] at gp; exact ord _ _ (by simpa using gp)
  have hkq : k = -2 * q - 2 := by
    have : (k : 𝕜) = ((-2 * q - 2 : ℤ) : 𝕜) := by push_cast; rw [← h_m, ← h_p]; linear_combination hmeq
    exact_mod_cast this
  have hk0 : ¬ k < 0 := by omega
  have hk1 : ¬ k - 1 < 0 := by omega
  have hk2 : ¬ k - 2 < 0 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1212r96Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨-, hQ⟩ := hBody w hw
    simp [Defined, eval, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two, hk2]
    first | exact fun _ => hQ (by omega) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨-, hQ⟩ := hBody w hw
    simp [rubi1212r96Nondeg, Defined, eval, recEnv, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two, hk1, hA0]
    first | exact fun _ => hQ (by omega) | (trace_state; sorry)
  · simp only [rubi1212r96Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hQ0 : (env "a" + env "c" * t ^ 2) ≠ 0 := (hBody t hF.self_of_nhds).2 (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "d" + env "e" * t) ^ (k - 2) * (env "a" + env "c" * t ^ 2) ^ (q + 1)) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1212r96Nondeg.body = (env "d" + env "e" * t) ^ k * (env "a" + env "c" * t ^ 2) ^ q := by
      simp [rubi1212r96Nondeg, eval, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two]
    have hfun : (fun w => eval I (recEnv env (rubi1212r96Nondeg.integrals.map (·.1)) Φ "x" w) rubi1212r96Nondeg.result) =
        fun w => (env "d" + env "e" * w) ^ (k - 1) * (env "a" * env "e" + -1 * env "c" * env "d" * w) * (env "a" + env "c" * w ^ 2) ^ (q + 1) * (2 * env "a" * env "c" * (env "p" + 1))⁻¹ +
          (2 * env "p" + 3) * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2) * (2 * env "a" * env "c" * (env "p" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1212r96Nondeg, eval, recEnv, hk_m, hk_p, em1, em1', em2, em2', em3, ep1, toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hDp := HasDerivAt.comp t (hasDerivAt_zpow (k - 1) _ (Or.inr (by omega))) hDd
    have hP : HasDerivAt (fun w => env "a" * env "e" + -1 * env "c" * env "d" * w) (-1 * env "c" * env "d" * 1) t :=
      ((hasDerivAt_id' t).const_mul _).const_add _
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ (Or.inl hQ0)) hQd
    refine ((((hDp.mul hP).mul hQp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [show k - 1 - 1 = k - 2 by ring]
    rw [show (env "d" + env "e" * t) ^ (k - 1) = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) by rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring,
      show (env "d" + env "e" * t) ^ k = (env "d" + env "e" * t) ^ (k - 2) * (env "d" + env "e" * t) * (env "d" + env "e" * t) by
        rw [← zpow_succ_of _ _ (Or.inr (by omega)), ← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring,
      zpow_add_one₀ hQ0]
    generalize (env "d" + env "e" * t) ^ (k - 2) = Dk
    generalize (env "a" + env "c" * t ^ 2) ^ q = Qp
    rw [h_m, h_p] at *
    rw [hkq]
    field_simp
    push_cast
    ring

theorem rubi1212r40Nondeg_real : rubi1212r40Nondeg.Holds .real := rubi1212r40Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1212r40Nondeg_complex : rubi1212r40Nondeg.Holds .complex := rubi1212r40Nondeg_holds Interp.complex Interp.complex_lt_rat
theorem rubi1212r46Nondeg_real : rubi1212r46Nondeg.Holds .real := rubi1212r46Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1212r46Nondeg_complex : rubi1212r46Nondeg.Holds .complex := rubi1212r46Nondeg_holds Interp.complex Interp.complex_lt_rat
theorem rubi1212r96Nondeg_real : rubi1212r96Nondeg.Holds .real := rubi1212r96Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1212r96Nondeg_complex : rubi1212r96Nondeg.Holds .complex := rubi1212r96Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec101
