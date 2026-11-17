import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, tenth batch

RUBI 1.2.3.4 #34, #38 and #40 are refuted as stated (a coefficient the result
divides by may vanish).  With the non-degeneracy conditions of their results
they are proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec103

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_1_2_3_4_r40 with the non-degeneracy conditions of its result -/
def rubi1234r40Nondeg : CRule where
  id := "integration.rubi_1_2_3_4_r40_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:40"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "f") (.var "n"))) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.pow (.var "x") (.var "n")))))]
  independent := ["a", "c", "d", "e", "f", "p", "m", "n", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")), .int (.var "n"), .gt (.var "n") (.int 0), .gt (.int (-1)) (.var "m"), .int (.var "p"),
    .ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "f") (.var "n"))) (.app2 .add (.var "m") (.int 1))) (.int 0)]
  priority := 9211
  description := "rubi_1_2_3_4_r40 with the non-degeneracy conditions of its result"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:40" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#40"

/-- rubi_1_2_3_4_r34 with the non-degeneracy conditions of its result -/
def rubi1234r34Nondeg : CRule where
  id := "integration.rubi_1_2_3_4_r34_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:34"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.pow (.var "f") (.var "n")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.var "m"))) (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.app2 .mul (.int 2) (.var "n"))) (.var "m")) (.int 1))) (.pow (.var "x") (.var "n")))))]
  independent := ["a", "c", "d", "e", "f", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")), .int (.var "n"), .gt (.var "n") (.int 0), .gt (.int (-1)) (.var "p"), .gt (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))), .int (.var "p"),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9212
  description := "rubi_1_2_3_4_r34 with the non-degeneracy conditions of its result"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:34" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#34"

/-- rubi_1_2_3_4_r38 with the non-degeneracy conditions of its result -/
def rubi1234r38Nondeg : CRule where
  id := "integration.rubi_1_2_3_4_r38_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:38"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.var "f") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.var "n"))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", .app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.pow (.var "x") (.var "n")))))]
  independent := ["a", "c", "d", "e", "f", "p", "m", "n", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")), .int (.var "n"), .gt (.var "n") (.int 0), .gt (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))), .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1)) (.int 0), .int (.var "p"),
    .ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.int 0)]
  priority := 9213
  description := "rubi_1_2_3_4_r38 with the non-degeneracy conditions of its result"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:38" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#38"


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

theorem rubi1234r40Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1234r40Nondeg.conditions rubi1234r40Nondeg.body rubi1234r40Nondeg.result rubi1234r40Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1234r40Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have gn := hc (.gt (.var "n") (.int 0)) (by simp [rubi1234r40Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r40Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r40Nondeg, Defined, eval, hk_m, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r40Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn; rw [h_n] at gn; exact ord _ _ (by simpa using gn)
  have e2 : I.toInt? (env "n2") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [hn2, h_n]; push_cast; ring)
  have e2' : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have em1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have emn : I.toInt? (env "m" + env "n") = some (k + j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emn' : I.toInt? (env "m" + -1 * env "n") = some (k - j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emj : I.toInt? (env "m" + -env "n") = some (k - j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emj' : I.toInt? (env "m" + -1 * env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emj1 : I.toInt? (env "m" + -env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emj1' : I.toInt? (env "m" + 1 + -env "n") = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ej1 : I.toInt? (env "n" + -1 * 1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have ej1' : I.toInt? (env "n" + -1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hsq : ∀ w : 𝕜, w ^ (2 * j) = (w ^ j) ^ 2 := by
    intro w; rw [mul_comm, zpow_mul]; norm_cast
  have hj0 : ¬ j < 0 := by omega
  have hj2 : ¬ 2 * j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have gm := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi1234r40Nondeg])
  have hk : k < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m] at gm; exact ord _ _ (by simpa using gm)
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1234r40Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hA1 := hc (.ne (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "f") (.var "n"))) (.app2 .add (.var "m") (.int 1))) (.int 0)) (by simp [rubi1234r40Nondeg])
  simp [Cond.Holds, Defined, eval, hk_n] at hA1
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1234r40Nondeg.body → (env "f" * w) ≠ 0 ∧ (q < 0 → (env "a" + env "c" * (w ^ j) ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1234r40Nondeg, Defined, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two, hj0, hj2] at h
    first | exact ⟨mul_ne_zero (h.1 (by omega)).1 (h.1 (by omega)).2, h.2⟩ | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1234r40Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    have h1' : env "f" ≠ 0 ∧ w ≠ 0 := ⟨left_ne_zero_of_mul h1, right_ne_zero_of_mul h1⟩
    simp [Defined, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two, hj0, hj2, h1'.1, h1'.2]
    first | exact h2 | done | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hBody w hw
    have h1' : env "f" ≠ 0 ∧ w ≠ 0 := ⟨left_ne_zero_of_mul h1, right_ne_zero_of_mul h1⟩
    simp [rubi1234r40Nondeg, Defined, eval, recEnv, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two, hj0, hj2, h1'.1, h1'.2, hA0, hA1]
    first | exact fun h => h2 (by omega) | done | (trace_state; sorry)
  · simp only [rubi1234r40Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    obtain ⟨hE0, hQ0'⟩ := hBody t hF.self_of_nhds
    have hf0 : env "f" ≠ 0 := left_ne_zero_of_mul hE0
    have ht0 : t ≠ 0 := right_ne_zero_of_mul hE0
    have hQq : (env "a" + env "c" * (t ^ j) ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (hQ0' h)
      · exact Or.inr (by omega)
    have hQq1 : (env "a" + env "c" * (t ^ j) ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      rcases hQq with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (k + j) * (env "a" + env "c" * (t ^ j) ^ 2) ^ q * (env "a" * env "e" * (env "m" + 1) + -1 * env "c" * env "d" * (env "m" + 2 * env "n" * (env "p" + 1) + 1) * t ^ j)) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1234r40Nondeg.body = (env "f" * t) ^ k * (env "d" + env "e" * t ^ j) * (env "a" + env "c" * (t ^ j) ^ 2) ^ q := by
      simp [rubi1234r40Nondeg, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two]
    have hfun : (fun w => eval I (recEnv env (rubi1234r40Nondeg.integrals.map (·.1)) Φ "x" w) rubi1234r40Nondeg.result) =
        fun w => env "d" * (env "f" * w) ^ (k + 1) * (env "a" + env "c" * (w ^ j) ^ 2) ^ (q + 1) * (env "a" * env "f" * (env "m" + 1))⁻¹ +
          1 * (env "a" * env "f" ^ j * (env "m" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1234r40Nondeg, eval, recEnv, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hY := hasDerivAt_zpow j t (Or.inr (by omega))
    have hQd : HasDerivAt (fun w => (env "a" + env "c" * (w ^ j) ^ 2)) (env "c" * ((2 : ℕ) * (t ^ j) ^ (2 - 1) * ((j : 𝕜) * t ^ (j - 1)))) t :=
      ((hY.pow 2).const_mul (env "c")).const_add (env "a")
    have hEp := HasDerivAt.comp t (hasDerivAt_zpow (k + 1) _ (Or.inl hE0)) ((hasDerivAt_id' t).const_mul (env "f"))
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hQq1) hQd
    refine ((((hEp.const_mul (env "d")).mul hQp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, add_sub_cancel_right]
    rw [zpow_add_one₀ hE0 k, zpow_add₀ hE0 k j, zpow_succ_of _ _ hQq]
    generalize (env "f" * t) ^ k = Ek
    generalize (env "a" + env "c" * (t ^ j) ^ 2) ^ q = Qp
    rw [mul_zpow (env "f") t j, show t ^ j = t ^ (j - 1) * t by rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]]
    generalize t ^ (j - 1) = T1
    generalize env "f" ^ j = Fj at hA1 ⊢
    simp only [h_m, h_n, h_p] at *
    casesm* _ ∧ _
    field_simp
    push_cast
    ring

theorem rubi1234r34Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1234r34Nondeg.conditions rubi1234r34Nondeg.body rubi1234r34Nondeg.result rubi1234r34Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1234r34Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have gn := hc (.gt (.var "n") (.int 0)) (by simp [rubi1234r34Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r34Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r34Nondeg, Defined, eval, hk_m, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r34Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn; rw [h_n] at gn; exact ord _ _ (by simpa using gn)
  have e2 : I.toInt? (env "n2") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [hn2, h_n]; push_cast; ring)
  have e2' : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have em1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have emn : I.toInt? (env "m" + env "n") = some (k + j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emn' : I.toInt? (env "m" + -1 * env "n") = some (k - j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emj : I.toInt? (env "m" + -env "n") = some (k - j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emj' : I.toInt? (env "m" + -1 * env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emj1 : I.toInt? (env "m" + -env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emj1' : I.toInt? (env "m" + 1 + -env "n") = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ej1 : I.toInt? (env "n" + -1 * 1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have ej1' : I.toInt? (env "n" + -1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hsq : ∀ w : 𝕜, w ^ (2 * j) = (w ^ j) ^ 2 := by
    intro w; rw [mul_comm, zpow_mul]; norm_cast
  have hj0 : ¬ j < 0 := by omega
  have hj2 : ¬ 2 * j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have gp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi1234r34Nondeg])
  have hq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp; rw [h_p] at gp; exact ord _ _ (by simpa using gp)
  have gm := hc (.gt (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi1234r34Nondeg])
  have hk : j - 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m, h_n] at gm
    exact ord _ _ (by push_cast; simpa [sub_eq_add_neg] using gm)
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi1234r34Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hk0 : ¬ k < 0 := by omega
  have hkj : ¬ k - j < 0 := by omega
  have hkj1 : ¬ k - j + 1 < 0 := by omega
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1234r34Nondeg.body → (q < 0 → (env "a" + env "c" * (w ^ j) ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1234r34Nondeg, Defined, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two, hj0, hj2, hk0] at h
    first | exact h | exact h.2 | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1234r34Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h2 := hBody w hw
    simp [Defined, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two, hj0, hj2, hkj]
    first | done | exact h2 | exact fun h => h2 (by omega) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h2 := hBody w hw
    simp [rubi1234r34Nondeg, Defined, eval, recEnv, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two, hj0, hj2, hj1, hkj1, hA0]
    first | done | exact fun h => h2 (by omega) | (trace_state; sorry)
  · simp only [rubi1234r34Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hQ0' := hBody t hF.self_of_nhds
    have hQ0 : (env "a" + env "c" * (t ^ j) ^ 2) ≠ 0 := hQ0' (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (k - j) * (env "a" + env "c" * (t ^ j) ^ 2) ^ (q + 1) * (env "a" * env "e" * (env "n" + -1 * env "m" + -1 * 1) + env "c" * env "d" * (2 * env "n" * env "p" + 2 * env "n" + env "m" + 1) * t ^ j)) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1234r34Nondeg.body = (env "f" * t) ^ k * (env "d" + env "e" * t ^ j) * (env "a" + env "c" * (t ^ j) ^ 2) ^ q := by
      simp [rubi1234r34Nondeg, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two]
    have hfun : (fun w => eval I (recEnv env (rubi1234r34Nondeg.integrals.map (·.1)) Φ "x" w) rubi1234r34Nondeg.result) =
        fun w => env "f" ^ (j - 1) * (env "f" * w) ^ (k - j + 1) * (env "a" + env "c" * (w ^ j) ^ 2) ^ (q + 1) * (env "a" * env "e" + -1 * env "c" * env "d" * w ^ j) * (2 * env "a" * env "c" * env "n" * (env "p" + 1))⁻¹ + env "f" ^ j * (2 * env "a" * env "c" * env "n" * (env "p" + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1234r34Nondeg, eval, recEnv, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hY := hasDerivAt_zpow j t (Or.inr (by omega))
    have hQd : HasDerivAt (fun w => (env "a" + env "c" * (w ^ j) ^ 2)) (env "c" * ((2 : ℕ) * (t ^ j) ^ (2 - 1) * ((j : 𝕜) * t ^ (j - 1)))) t :=
      ((hY.pow 2).const_mul (env "c")).const_add (env "a")
    have hEp := HasDerivAt.comp t (hasDerivAt_zpow (k - j + 1) _ (Or.inr (by omega))) ((hasDerivAt_id' t).const_mul (env "f"))
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ (Or.inl hQ0)) hQd
    have hP : HasDerivAt (fun w => env "a" * env "e" + -1 * env "c" * env "d" * w ^ j) (-1 * env "c" * env "d" * ((j : 𝕜) * t ^ (j - 1))) t :=
      (hY.const_mul _).const_add _
    refine (((((hEp.const_mul (env "f" ^ (j - 1))).mul hQp).mul hP).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    have za : ∀ (A : 𝕜) (x y : ℤ), 0 ≤ x → 0 ≤ y → A ^ (x + y) = A ^ x * A ^ y := by
      intro A x y hx hy
      lift x to ℕ using hx
      lift y to ℕ using hy
      rw [← Nat.cast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]
    have rk : (env "f" * t) ^ k = (env "f" * t) ^ (k - j) * (env "f" * t) ^ j := by rw [← za _ _ _ (by omega) (by omega)]; congr 1; ring
    have rk1 : (env "f" * t) ^ (k - j + 1) = (env "f" * t) ^ (k - j) * (env "f" * t) := zpow_succ_of _ _ (Or.inr (by omega))
    have rfj : env "f" ^ j = env "f" ^ (j - 1) * env "f" := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    have rtj : t ^ j = t ^ (j - 1) * t := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [rk, rk1, zpow_add_one₀ hQ0]
    generalize (env "f" * t) ^ (k - j) = Ek
    generalize (env "a" + env "c" * (t ^ j) ^ 2) ^ q = Qp
    rw [mul_zpow (env "f") t j, rfj, rtj]
    generalize t ^ (j - 1) = T1
    generalize env "f" ^ (j - 1) = F1
    simp only [h_m, h_n, h_p] at *
    casesm* _ ∧ _
    field_simp
    push_cast
    ring

theorem rubi1234r38Nondeg_holds [CharZero 𝕜] (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r) :
    AntiderivRecHolds I "x" rubi1234r38Nondeg.conditions rubi1234r38Nondeg.body rubi1234r38Nondeg.result rubi1234r38Nondeg.integrals := by
  intro env hc t hF
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hn2 : env "n2" = 2 * env "n" := by
    have h := hc (.eq (.var "n2") (.app2 .mul (.int 2) (.var "n"))) (by simp [rubi1234r38Nondeg]); simpa [Cond.Holds, Defined, eval] using h
  have gn := hc (.gt (.var "n") (.int 0)) (by simp [rubi1234r38Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r38Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r38Nondeg, Defined, eval, hk_m, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi1234r38Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn; rw [h_n] at gn; exact ord _ _ (by simpa using gn)
  have e2 : I.toInt? (env "n2") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [hn2, h_n]; push_cast; ring)
  have e2' : I.toInt? (2 * env "n") = some (2 * j) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have em1 : I.toInt? (env "m" + 1) = some (k + 1) := (I.toInt?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have emn : I.toInt? (env "m" + env "n") = some (k + j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emn' : I.toInt? (env "m" + -1 * env "n") = some (k - j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emj : I.toInt? (env "m" + -env "n") = some (k - j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emj' : I.toInt? (env "m" + -1 * env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emj1 : I.toInt? (env "m" + -env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have emj1' : I.toInt? (env "m" + 1 + -env "n") = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ej1 : I.toInt? (env "n" + -1 * 1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have ej1' : I.toInt? (env "n" + -1) = some (j - 1) := (I.toInt?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have hsq : ∀ w : 𝕜, w ^ (2 * j) = (w ^ j) ^ 2 := by
    intro w; rw [mul_comm, zpow_mul]; norm_cast
  have hj0 : ¬ j < 0 := by omega
  have hj2 : ¬ 2 * j < 0 := by omega
  have hj1 : ¬ j - 1 < 0 := by omega
  have gm := hc (.gt (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi1234r38Nondeg])
  have hk : j - 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm; rw [h_m, h_n] at gm
    exact ord _ _ (by push_cast; simpa [sub_eq_add_neg] using gm)
  have hA0 := hc (.ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.int 0)) (by simp [rubi1234r38Nondeg])
  simp [Cond.Holds, Defined, eval] at hA0
  have hk0 : ¬ k < 0 := by omega
  have hkj : ¬ k - j < 0 := by omega
  have hkj1 : ¬ k - j + 1 < 0 := by omega
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi1234r38Nondeg.body → (q < 0 → (env "a" + env "c" * (w ^ j) ^ 2) ≠ 0) := by
    intro w h
    simp [rubi1234r38Nondeg, Defined, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two, hj0, hj2, hk0] at h
    first | exact h | exact h.2 | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1234r38Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h2 := hBody w hw
    simp [Defined, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two, hj0, hj2, hkj]
    first | done | exact h2 | exact fun h => h2 (by omega) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have h2 := hBody w hw
    simp [rubi1234r38Nondeg, Defined, eval, recEnv, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two, hj0, hj2, hj1, hkj1, hA0]
    first | done | exact fun h => h2 (by omega) | (trace_state; sorry)
  · simp only [rubi1234r38Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hQ0' := hBody t hF.self_of_nhds
    have hQq : (env "a" + env "c" * (t ^ j) ^ 2) ≠ 0 ∨ 0 ≤ q := by
      by_cases h : q < 0
      · exact Or.inl (hQ0' h)
      · exact Or.inr (by omega)
    have hQq1 : (env "a" + env "c" * (t ^ j) ^ 2) ≠ 0 ∨ 0 ≤ q + 1 := by
      rcases hQq with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hΦ' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (k - j) * (env "a" + env "c" * (t ^ j) ^ 2) ^ q * (env "a" * env "e" * (env "m" + -1 * env "n" + 1) + -1 * env "c" * env "d" * (env "m" + env "n" * (2 * env "p" + 1) + 1) * t ^ j)) t := by
      convert hΦ using 1
      simp [eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two]
    have hEF : eval I (Function.update env "x" t) rubi1234r38Nondeg.body = (env "f" * t) ^ k * (env "d" + env "e" * t ^ j) * (env "a" + env "c" * (t ^ j) ^ 2) ^ q := by
      simp [rubi1234r38Nondeg, eval, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two]
    have hfun : (fun w => eval I (recEnv env (rubi1234r38Nondeg.integrals.map (·.1)) Φ "x" w) rubi1234r38Nondeg.result) =
        fun w => env "e" * env "f" ^ (j - 1) * (env "f" * w) ^ (k - j + 1) * (env "a" + env "c" * (w ^ j) ^ 2) ^ (q + 1) * (env "c" * (env "m" + env "n" * (2 * env "p" + 1) + 1))⁻¹ + -1 * env "f" ^ j * (env "c" * (env "m" + env "n" * (2 * env "p" + 1) + 1))⁻¹ * Φ "I1" w := by
      funext w
      simp [rubi1234r38Nondeg, eval, recEnv, hk_m, hk_n, hk_p, e2, e2', hsq, em1, ep1, emn, emn', emj, emj', emj1, emj1', ej1, ej1', toInt?_neg_one, toInt?_two, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hY := hasDerivAt_zpow j t (Or.inr (by omega))
    have hQd : HasDerivAt (fun w => (env "a" + env "c" * (w ^ j) ^ 2)) (env "c" * ((2 : ℕ) * (t ^ j) ^ (2 - 1) * ((j : 𝕜) * t ^ (j - 1)))) t :=
      ((hY.pow 2).const_mul (env "c")).const_add (env "a")
    have hEp := HasDerivAt.comp t (hasDerivAt_zpow (k - j + 1) _ (Or.inr (by omega))) ((hasDerivAt_id' t).const_mul (env "f"))
    have hQp := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ hQq1) hQd
    refine ((((hEp.const_mul (env "e" * env "f" ^ (j - 1))).mul hQp).mul_const _).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    have za : ∀ (A : 𝕜) (x y : ℤ), 0 ≤ x → 0 ≤ y → A ^ (x + y) = A ^ x * A ^ y := by
      intro A x y hx hy
      lift x to ℕ using hx
      lift y to ℕ using hy
      rw [← Nat.cast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]
    have rk : (env "f" * t) ^ k = (env "f" * t) ^ (k - j) * (env "f" * t) ^ j := by rw [← za _ _ _ (by omega) (by omega)]; congr 1; ring
    have rk1 : (env "f" * t) ^ (k - j + 1) = (env "f" * t) ^ (k - j) * (env "f" * t) := zpow_succ_of _ _ (Or.inr (by omega))
    have rfj : env "f" ^ j = env "f" ^ (j - 1) * env "f" := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    have rtj : t ^ j = t ^ (j - 1) * t := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [rk, rk1, zpow_succ_of _ _ hQq]
    generalize (env "f" * t) ^ (k - j) = Ek
    generalize (env "a" + env "c" * (t ^ j) ^ 2) ^ q = Qp
    rw [mul_zpow (env "f") t j, rfj, rtj]
    generalize t ^ (j - 1) = T1
    generalize env "f" ^ (j - 1) = F1
    simp only [h_m, h_n, h_p] at *
    casesm* _ ∧ _
    field_simp
    push_cast
    ring

theorem rubi1234r40Nondeg_real : rubi1234r40Nondeg.Holds .real := rubi1234r40Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1234r40Nondeg_complex : rubi1234r40Nondeg.Holds .complex := rubi1234r40Nondeg_holds Interp.complex Interp.complex_lt_rat
theorem rubi1234r34Nondeg_real : rubi1234r34Nondeg.Holds .real := rubi1234r34Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1234r34Nondeg_complex : rubi1234r34Nondeg.Holds .complex := rubi1234r34Nondeg_holds Interp.complex Interp.complex_lt_rat
theorem rubi1234r38Nondeg_real : rubi1234r38Nondeg.Holds .real := rubi1234r38Nondeg_holds Interp.real Interp.real_lt_rat
theorem rubi1234r38Nondeg_complex : rubi1234r38Nondeg.Holds .complex := rubi1234r38Nondeg_holds Interp.complex Interp.complex_lt_rat

end Proofs

end OSR.IntegrationRec103
