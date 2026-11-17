import OSR.IntegrationRec91

/-!
# Integration (RUBI): strengthened variants of refuted named rules, seventh batch

RUBI 4.1.12 #45, #46, #53 and #54 are refuted as stated (a coefficient the
result divides by may vanish).  With the non-degeneracy conditions of their
results they are proved over ℝ and ℂ: all powers of `x` have nonnegative
exponents, since `m > 2 n - 1` and `n > 0`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec100

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_4_1_12_r45 with the non-degeneracy conditions of its result -/
def rubi4112r45Nondeg : CRule where
  id := "integration.rubi_4_1_12_r45_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:45"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))) (.pow (.var "p") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))), ("I2", .app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.gt (.var "p") (.int 1), .int (.var "n"), .gt (.var "n") (.int 0), .int (.var "m"), .gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int 0),
    .ne (.var "p") (.int 0)]
  priority := 9181
  description := "rubi_4_1_12_r45 with the non-degeneracy conditions of its result"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:45" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#45"

/-- rubi_4_1_12_r46 with the non-degeneracy conditions of its result -/
def rubi4112r46Nondeg : CRule where
  id := "integration.rubi_4_1_12_r46_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:46"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))) (.pow (.var "p") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))), ("I2", .app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.gt (.var "p") (.int 1), .int (.var "n"), .gt (.var "n") (.int 0), .int (.var "m"), .gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int 0),
    .ne (.var "p") (.int 0)]
  priority := 9182
  description := "rubi_4_1_12_r46 with the non-degeneracy conditions of its result"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:46" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#46"

/-- rubi_4_1_12_r53 with the non-degeneracy conditions of its result -/
def rubi4112r53Nondeg : CRule where
  id := "integration.rubi_4_1_12_r53_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:53"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.int 2)) (.pow (.app2 .add (.var "p") (.int 1)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))), ("I2", .app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.gt (.int (-1)) (.var "p"), .ne (.var "p") (.int (-2)), .int (.var "n"), .gt (.var "n") (.int 0), .int (.var "m"), .gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int 0),
    .ne (.app2 .add (.var "p") (.int 1)) (.int 0)]
  priority := 9183
  description := "rubi_4_1_12_r53 with the non-degeneracy conditions of its result"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:53" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#53"

/-- rubi_4_1_12_r54 with the non-degeneracy conditions of its result -/
def rubi4112r54Nondeg : CRule where
  id := "integration.rubi_4_1_12_r54_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:54"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.int 2)) (.pow (.app2 .add (.var "p") (.int 1)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", .app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))), ("I2", .app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.gt (.int (-1)) (.var "p"), .ne (.var "p") (.int (-2)), .int (.var "n"), .gt (.var "n") (.int 0), .int (.var "m"), .gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int 0),
    .ne (.app2 .add (.var "p") (.int 1)) (.int 0)]
  priority := 9184
  description := "rubi_4_1_12_r54 with the non-degeneracy conditions of its result"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:54" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#54"


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

theorem rubi4112r45Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hp : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivRecHolds I "x" rubi4112r45Nondeg.conditions rubi4112r45Nondeg.body rubi4112r45Nondeg.result rubi4112r45Nondeg.integrals := by
  intro env hc t hF
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int 0)) (by simp [rubi4112r45Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA0
  have hA1 := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int 0)) (by simp [rubi4112r45Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA1
  have hA2 := hc (.ne (.var "p") (.int 0)) (by simp [rubi4112r45Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA2
  have gp := hc (.gt (.var "p") (.int 1)) (by simp [rubi4112r45Nondeg])
  have gn := hc (.gt (.var "n") (.int 0)) (by simp [rubi4112r45Nondeg])
  have gm := hc (.gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi4112r45Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r45Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r45Nondeg, Defined, eval, hk_m, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r45Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hqq : 1 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp
    rw [h_p] at gp
    exact ord _ _ (by simpa using gp)
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn
    rw [h_n] at gn
    exact ord _ _ (by simpa using gn)
  have hk : 2 * j - 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm
    rw [h_n, h_m] at gm
    have := ord (2 * j - 1) k (by push_cast; simpa [sub_eq_add_neg] using gm)
    exact this

  have hq0 : ¬ q < 0 := by omega
  have hq2 : ¬ q - 2 < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hj0 : ¬ j < 0 := by omega
  have hkj : ¬ k - 2 * j < 0 := by omega
  have hkj1 : ¬ k - 2 * j + 1 < 0 := by omega
  have hkj2 : ¬ k - j + 1 < 0 := by omega
  have ea : I.toInt? (env "m" + -1 * 2 * env "n" + 1) = some (k - 2 * j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ea' : I.toInt? (env "m" + -(2 * env "n") + 1) = some (k - 2 * j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have eb : I.toInt? (env "m" + -1 * env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have eb' : I.toInt? (env "m" + -env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ec : I.toInt? (env "m" + -1 * 2 * env "n") = some (k - 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ec' : I.toInt? (env "m" + -(2 * env "n")) = some (k - 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2 : I.toInt? (env "p" + -1 * 2) = some (q - 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2' : I.toInt? (env "p" + -2) = some (q - 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have eq1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have eq2 : I.toInt? (env "p" + 2) = some (q + 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi4112r45Nondeg.body → (q < 0 → I.sin (env "a" + env "b" * w ^ j) ≠ 0) := by
    intro w h
    simp [rubi4112r45Nondeg, Defined, eval, hk_m, hk_n, hk_p, hk0, hj0] at h
    first | exact h | exact fun h' => h h' | tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r45Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hM := hBody w hw
      simp [Defined, eval, hk_m, hk_n, hk_p, ea, ea', eb, eb', ec, ec', ep1, ep1', ep2, ep2', eq1, eq2, hk0, hj0, hkj, hkj1, hkj2, hq0, hq1, hq2]
      first | done | exact hM hq0 | exact fun h => hM (by omega) | exact ⟨hM hq0, hM hq0⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hM := hBody w hw
    simp [rubi4112r45Nondeg, Defined, eval, recEnv, hk_m, hk_n, hk_p, ea, ea', eb, eb', ec, ec', ep1, ep1', ep2, ep2', eq1, eq2, hk0, hj0, hkj, hkj1, hkj2, hq0, hq1, hq2, toInt?_neg_one, toInt?_two, hA0, hA1, hA2]
    first | done | exact hM hq0 | exact ⟨hM hq0, hM hq0⟩ | exact fun h => hM (by omega) | exact ⟨fun h => hM (by omega), fun h => hM (by omega)⟩ | (trace_state; sorry)
  · simp only [rubi4112r45Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hM0' := hBody t hF.self_of_nhds

    have hΦ1' : HasDerivAt (Φ "I1") (t ^ k * I.sin (env "a" + env "b" * t ^ j) ^ (q - 2)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, hk_p, ep2, ep2', eq2, ec, ec']
    have hΦ2' : HasDerivAt (Φ "I2") (t ^ (k - 2 * j) * I.sin (env "a" + env "b" * t ^ j) ^ q) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, hk_p, ep2, ep2', eq2, ec, ec']
    have hEF : eval I (Function.update env "x" t) rubi4112r45Nondeg.body = t ^ k * I.sin (env "a" + env "b" * t ^ j) ^ q := by
      simp [rubi4112r45Nondeg, eval, hk_m, hk_n, hk_p]
    set W2 := (env "b" ^ 2 * env "n" ^ 2 * env "p" ^ 2)⁻¹ with hW2_def
    set W1 := (env "b" * env "n" * env "p")⁻¹ with hW1_def
    set Pv := (env "p")⁻¹ with hPv_def
    have hU2 : (env "b" ^ 2 * env "n" ^ 2 * env "p" ^ 2) * W2 = 1 := by rw [hW2_def]; exact mul_inv_cancel₀ (by simp_all)
    have hW1e : W1 = env "b" * env "n" * env "p" * W2 := by
      rw [hW1_def, hW2_def]
      simp only [h_n, h_p] at hA0 hA1 hA2 ⊢
      casesm* _ ∧ _
      first | (field_simp; done) | (field_simp; ring)
    have hPve : Pv = env "b" ^ 2 * env "n" ^ 2 * env "p" * W2 := by
      rw [hPv_def, hW2_def]
      simp only [h_n, h_p] at hA0 hA1 hA2 ⊢
      casesm* _ ∧ _
      first | (field_simp; done) | (field_simp; ring)
    have hfun : (fun w => eval I (recEnv env (rubi4112r45Nondeg.integrals.map (·.1)) Φ "x" w) rubi4112r45Nondeg.result) =
        fun w => (env "m" + -1 * env "n" + 1) * w ^ (k - 2 * j + 1) * I.sin (env "a" + env "b" * w ^ j) ^ q * W2 + -1 * w ^ (k - j + 1) * I.cos (env "a" + env "b" * w ^ j) * I.sin (env "a" + env "b" * w ^ j) ^ (q - 1) * W1 + (env "p" + -1) * Pv * Φ "I1" w + -1 * (env "m" + -1 * env "n" + 1) * (env "m" + -1 * 2 * env "n" + 1) * W2 * Φ "I2" w := by
      funext w
      simp [rubi4112r45Nondeg, eval, recEnv, hk_m, hk_n, hk_p, ea, ea', eb, eb', ep1, ep1', eq1, eq2, toInt?_neg_one, toInt?_two, hW2_def, hW1_def, hPv_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hin : HasDerivAt (fun w => (env "a" + env "b" * w ^ j)) (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t (Or.inr (by omega))).const_mul _).const_add _
    have hMd := HasDerivAt.comp t (hs _) hin
    have hNd := HasDerivAt.comp t (hcs _) hin
    have hX1 := hasDerivAt_zpow (k - 2 * j + 1) t (Or.inr (by omega))
    have hX2 := hasDerivAt_zpow (k - j + 1) t (Or.inr (by omega))
    have hMq := HasDerivAt.comp t (hasDerivAt_zpow q _ (Or.inr (by omega))) hMd
    have hMq1 := HasDerivAt.comp t (hasDerivAt_zpow (q - 1) _ (Or.inr (by omega))) hMd
    refine ((((((hX1.const_mul _).mul hMq).mul_const W2).add ((((hX2.const_mul (-1)).mul hNd).mul hMq1).mul_const W1)).add
      (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [show q - 1 - 1 = q - 2 by ring]
    have rM0 : I.sin (env "a" + env "b" * t ^ j) ^ q = I.sin (env "a" + env "b" * t ^ j) ^ (q - 2) * I.sin (env "a" + env "b" * t ^ j) * I.sin (env "a" + env "b" * t ^ j) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), ← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    have rM1 : I.sin (env "a" + env "b" * t ^ j) ^ (q - 1) = I.sin (env "a" + env "b" * t ^ j) ^ (q - 2) * I.sin (env "a" + env "b" * t ^ j) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    rw [rM0, rM1]
    generalize I.sin (env "a" + env "b" * t ^ j) ^ (q - 2) = Rm
    have za : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b → t ^ (a + b) = t ^ a * t ^ b := by
      intro a b ha hb
      lift a to ℕ using ha
      lift b to ℕ using hb
      rw [← Nat.cast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]
    have r1 : t ^ (k - 2 * j + 1) = t ^ (k - 2 * j) * t := zpow_succ_of _ _ (Or.inr (by omega))
    have r2 : t ^ (k - j) = t ^ (k - 2 * j) * t ^ j := by
      rw [← za _ _ (by omega) (by omega)]; congr 1; ring
    have r3 : t ^ (k - j + 1) = t ^ (k - 2 * j) * t ^ j * t := by
      rw [zpow_succ_of _ _ (Or.inr (by omega)), r2]
    have r4 : t ^ k = t ^ (k - 2 * j) * t ^ j * t ^ j := by
      rw [← za _ _ (by omega) (by omega), ← za _ _ (by omega) (by omega)]; congr 1; ring
    have k1 : t ^ (j - 1) * t = t ^ j := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [r4, r3, r1, r2]
    have hpt := hp (env "a" + env "b" * t ^ j)
    generalize I.sin (env "a" + env "b" * t ^ j) = S at hpt ⊢
    generalize I.cos (env "a" + env "b" * t ^ j) = C at hpt ⊢
    generalize t ^ (k - 2 * j) = P0
    generalize t ^ (j - 1) = N1 at k1 ⊢
    generalize t ^ j = Xn at k1 ⊢
    rw [hW1e, hPve]
    clear_value W2 W1 Pv
    simp only [h_m, h_n, h_p] at hU2 ⊢
    push_cast
    linear_combination (-C^2*N1*P0*Rm*Xn*t + P0*Rm*Xn^2) * hU2 + (N1*P0*Rm*W2*Xn*env "b"^2*(j : 𝕜)^2*(q : 𝕜)*t - N1*P0*Rm*Xn*t) * hpt + (C*P0*Rm*S*W2*env "b"*(k : 𝕜)*(j : 𝕜)*(q : 𝕜) - C*P0*Rm*S*W2*env "b"*(j : 𝕜)^2*(q : 𝕜) + C*P0*Rm*S*W2*env "b"*(j : 𝕜)*(q : 𝕜) + P0*Rm*S^2*Xn + P0*Rm*W2*Xn*env "b"^2*(j : 𝕜)^2*(q : 𝕜) - P0*Rm*Xn) * k1

theorem rubi4112r46Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hp : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivRecHolds I "x" rubi4112r46Nondeg.conditions rubi4112r46Nondeg.body rubi4112r46Nondeg.result rubi4112r46Nondeg.integrals := by
  intro env hc t hF
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int 0)) (by simp [rubi4112r46Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA0
  have hA1 := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int 0)) (by simp [rubi4112r46Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA1
  have hA2 := hc (.ne (.var "p") (.int 0)) (by simp [rubi4112r46Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA2
  have gp := hc (.gt (.var "p") (.int 1)) (by simp [rubi4112r46Nondeg])
  have gn := hc (.gt (.var "n") (.int 0)) (by simp [rubi4112r46Nondeg])
  have gm := hc (.gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi4112r46Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r46Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r46Nondeg, Defined, eval, hk_m, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r46Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hqq : 1 < q := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp
    rw [h_p] at gp
    exact ord _ _ (by simpa using gp)
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn
    rw [h_n] at gn
    exact ord _ _ (by simpa using gn)
  have hk : 2 * j - 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm
    rw [h_n, h_m] at gm
    have := ord (2 * j - 1) k (by push_cast; simpa [sub_eq_add_neg] using gm)
    exact this

  have hq0 : ¬ q < 0 := by omega
  have hq2 : ¬ q - 2 < 0 := by omega
  have hq1 : ¬ q - 1 < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hj0 : ¬ j < 0 := by omega
  have hkj : ¬ k - 2 * j < 0 := by omega
  have hkj1 : ¬ k - 2 * j + 1 < 0 := by omega
  have hkj2 : ¬ k - j + 1 < 0 := by omega
  have ea : I.toInt? (env "m" + -1 * 2 * env "n" + 1) = some (k - 2 * j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ea' : I.toInt? (env "m" + -(2 * env "n") + 1) = some (k - 2 * j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have eb : I.toInt? (env "m" + -1 * env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have eb' : I.toInt? (env "m" + -env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ec : I.toInt? (env "m" + -1 * 2 * env "n") = some (k - 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ec' : I.toInt? (env "m" + -(2 * env "n")) = some (k - 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2 : I.toInt? (env "p" + -1 * 2) = some (q - 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2' : I.toInt? (env "p" + -2) = some (q - 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have eq1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have eq2 : I.toInt? (env "p" + 2) = some (q + 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi4112r46Nondeg.body → (q < 0 → I.cos (env "a" + env "b" * w ^ j) ≠ 0) := by
    intro w h
    simp [rubi4112r46Nondeg, Defined, eval, hk_m, hk_n, hk_p, hk0, hj0] at h
    first | exact h | exact fun h' => h h' | tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r46Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hM := hBody w hw
      simp [Defined, eval, hk_m, hk_n, hk_p, ea, ea', eb, eb', ec, ec', ep1, ep1', ep2, ep2', eq1, eq2, hk0, hj0, hkj, hkj1, hkj2, hq0, hq1, hq2]
      first | done | exact hM hq0 | exact fun h => hM (by omega) | exact ⟨hM hq0, hM hq0⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hM := hBody w hw
    simp [rubi4112r46Nondeg, Defined, eval, recEnv, hk_m, hk_n, hk_p, ea, ea', eb, eb', ec, ec', ep1, ep1', ep2, ep2', eq1, eq2, hk0, hj0, hkj, hkj1, hkj2, hq0, hq1, hq2, toInt?_neg_one, toInt?_two, hA0, hA1, hA2]
    first | done | exact hM hq0 | exact ⟨hM hq0, hM hq0⟩ | exact fun h => hM (by omega) | exact ⟨fun h => hM (by omega), fun h => hM (by omega)⟩ | (trace_state; sorry)
  · simp only [rubi4112r46Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hM0' := hBody t hF.self_of_nhds

    have hΦ1' : HasDerivAt (Φ "I1") (t ^ k * I.cos (env "a" + env "b" * t ^ j) ^ (q - 2)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, hk_p, ep2, ep2', eq2, ec, ec']
    have hΦ2' : HasDerivAt (Φ "I2") (t ^ (k - 2 * j) * I.cos (env "a" + env "b" * t ^ j) ^ q) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, hk_p, ep2, ep2', eq2, ec, ec']
    have hEF : eval I (Function.update env "x" t) rubi4112r46Nondeg.body = t ^ k * I.cos (env "a" + env "b" * t ^ j) ^ q := by
      simp [rubi4112r46Nondeg, eval, hk_m, hk_n, hk_p]
    set W2 := (env "b" ^ 2 * env "n" ^ 2 * env "p" ^ 2)⁻¹ with hW2_def
    set W1 := (env "b" * env "n" * env "p")⁻¹ with hW1_def
    set Pv := (env "p")⁻¹ with hPv_def
    have hU2 : (env "b" ^ 2 * env "n" ^ 2 * env "p" ^ 2) * W2 = 1 := by rw [hW2_def]; exact mul_inv_cancel₀ (by simp_all)
    have hW1e : W1 = env "b" * env "n" * env "p" * W2 := by
      rw [hW1_def, hW2_def]
      simp only [h_n, h_p] at hA0 hA1 hA2 ⊢
      casesm* _ ∧ _
      first | (field_simp; done) | (field_simp; ring)
    have hPve : Pv = env "b" ^ 2 * env "n" ^ 2 * env "p" * W2 := by
      rw [hPv_def, hW2_def]
      simp only [h_n, h_p] at hA0 hA1 hA2 ⊢
      casesm* _ ∧ _
      first | (field_simp; done) | (field_simp; ring)
    have hfun : (fun w => eval I (recEnv env (rubi4112r46Nondeg.integrals.map (·.1)) Φ "x" w) rubi4112r46Nondeg.result) =
        fun w => (env "m" + -1 * env "n" + 1) * w ^ (k - 2 * j + 1) * I.cos (env "a" + env "b" * w ^ j) ^ q * W2 + 1 * w ^ (k - j + 1) * I.sin (env "a" + env "b" * w ^ j) * I.cos (env "a" + env "b" * w ^ j) ^ (q - 1) * W1 + (env "p" + -1) * Pv * Φ "I1" w + -1 * (env "m" + -1 * env "n" + 1) * (env "m" + -1 * 2 * env "n" + 1) * W2 * Φ "I2" w := by
      funext w
      simp [rubi4112r46Nondeg, eval, recEnv, hk_m, hk_n, hk_p, ea, ea', eb, eb', ep1, ep1', eq1, eq2, toInt?_neg_one, toInt?_two, hW2_def, hW1_def, hPv_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hin : HasDerivAt (fun w => (env "a" + env "b" * w ^ j)) (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t (Or.inr (by omega))).const_mul _).const_add _
    have hMd := HasDerivAt.comp t (hcs _) hin
    have hNd := HasDerivAt.comp t (hs _) hin
    have hX1 := hasDerivAt_zpow (k - 2 * j + 1) t (Or.inr (by omega))
    have hX2 := hasDerivAt_zpow (k - j + 1) t (Or.inr (by omega))
    have hMq := HasDerivAt.comp t (hasDerivAt_zpow q _ (Or.inr (by omega))) hMd
    have hMq1 := HasDerivAt.comp t (hasDerivAt_zpow (q - 1) _ (Or.inr (by omega))) hMd
    refine ((((((hX1.const_mul _).mul hMq).mul_const W2).add ((((hX2.const_mul (1)).mul hNd).mul hMq1).mul_const W1)).add
      (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [show q - 1 - 1 = q - 2 by ring]
    have rM0 : I.cos (env "a" + env "b" * t ^ j) ^ q = I.cos (env "a" + env "b" * t ^ j) ^ (q - 2) * I.cos (env "a" + env "b" * t ^ j) * I.cos (env "a" + env "b" * t ^ j) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), ← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    have rM1 : I.cos (env "a" + env "b" * t ^ j) ^ (q - 1) = I.cos (env "a" + env "b" * t ^ j) ^ (q - 2) * I.cos (env "a" + env "b" * t ^ j) := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega))]; congr 1; ring
    rw [rM0, rM1]
    generalize I.cos (env "a" + env "b" * t ^ j) ^ (q - 2) = Rm
    have za : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b → t ^ (a + b) = t ^ a * t ^ b := by
      intro a b ha hb
      lift a to ℕ using ha
      lift b to ℕ using hb
      rw [← Nat.cast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]
    have r1 : t ^ (k - 2 * j + 1) = t ^ (k - 2 * j) * t := zpow_succ_of _ _ (Or.inr (by omega))
    have r2 : t ^ (k - j) = t ^ (k - 2 * j) * t ^ j := by
      rw [← za _ _ (by omega) (by omega)]; congr 1; ring
    have r3 : t ^ (k - j + 1) = t ^ (k - 2 * j) * t ^ j * t := by
      rw [zpow_succ_of _ _ (Or.inr (by omega)), r2]
    have r4 : t ^ k = t ^ (k - 2 * j) * t ^ j * t ^ j := by
      rw [← za _ _ (by omega) (by omega), ← za _ _ (by omega) (by omega)]; congr 1; ring
    have k1 : t ^ (j - 1) * t = t ^ j := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [r4, r3, r1, r2]
    have hpt := hp (env "a" + env "b" * t ^ j)
    generalize I.sin (env "a" + env "b" * t ^ j) = S at hpt ⊢
    generalize I.cos (env "a" + env "b" * t ^ j) = C at hpt ⊢
    generalize t ^ (k - 2 * j) = P0
    generalize t ^ (j - 1) = N1 at k1 ⊢
    generalize t ^ j = Xn at k1 ⊢
    rw [hW1e, hPve]
    clear_value W2 W1 Pv
    simp only [h_m, h_n, h_p] at hU2 ⊢
    push_cast
    linear_combination (-N1*P0*Rm*S^2*Xn*t + P0*Rm*Xn^2) * hU2 + (N1*P0*Rm*W2*Xn*env "b"^2*(j : 𝕜)^2*(q : 𝕜)*t - P0*Rm*Xn^2) * hpt + (-C*P0*Rm*S*W2*env "b"*(k : 𝕜)*(j : 𝕜)*(q : 𝕜) + C*P0*Rm*S*W2*env "b"*(j : 𝕜)^2*(q : 𝕜) - C*P0*Rm*S*W2*env "b"*(j : 𝕜)*(q : 𝕜) - P0*Rm*S^2*Xn + P0*Rm*W2*Xn*env "b"^2*(j : 𝕜)^2*(q : 𝕜)) * k1

theorem rubi4112r53Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hp : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivRecHolds I "x" rubi4112r53Nondeg.conditions rubi4112r53Nondeg.body rubi4112r53Nondeg.result rubi4112r53Nondeg.integrals := by
  intro env hc t hF
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi4112r53Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA0
  have hA1 := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int 0)) (by simp [rubi4112r53Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA1
  have hA2 := hc (.ne (.app2 .add (.var "p") (.int 1)) (.int 0)) (by simp [rubi4112r53Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA2
  have gp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi4112r53Nondeg])
  have gn := hc (.gt (.var "n") (.int 0)) (by simp [rubi4112r53Nondeg])
  have gm := hc (.gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi4112r53Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r53Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r53Nondeg, Defined, eval, hk_m, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r53Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hqq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp
    rw [h_p] at gp
    exact ord _ _ (by simpa using gp)
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn
    rw [h_n] at gn
    exact ord _ _ (by simpa using gn)
  have hk : 2 * j - 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm
    rw [h_n, h_m] at gm
    have := ord (2 * j - 1) k (by push_cast; simpa [sub_eq_add_neg] using gm)
    exact this
  have hq22 : q ≠ -2 := by
    have h := hc (.ne (.var "p") (.int (-2))) (by simp [rubi4112r53Nondeg])
    simp [Cond.Holds, Defined, eval] at h; intro h0; apply h; rw [h_p, h0]; simp
  have hq0 : q < 0 := by omega
  have hq1 : q + 1 < 0 := by omega
  have hq2 : q + 2 < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hj0 : ¬ j < 0 := by omega
  have hkj : ¬ k - 2 * j < 0 := by omega
  have hkj1 : ¬ k - 2 * j + 1 < 0 := by omega
  have hkj2 : ¬ k - j + 1 < 0 := by omega
  have ea : I.toInt? (env "m" + -1 * 2 * env "n" + 1) = some (k - 2 * j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ea' : I.toInt? (env "m" + -(2 * env "n") + 1) = some (k - 2 * j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have eb : I.toInt? (env "m" + -1 * env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have eb' : I.toInt? (env "m" + -env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ec : I.toInt? (env "m" + -1 * 2 * env "n") = some (k - 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ec' : I.toInt? (env "m" + -(2 * env "n")) = some (k - 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2 : I.toInt? (env "p" + -1 * 2) = some (q - 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2' : I.toInt? (env "p" + -2) = some (q - 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have eq1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have eq2 : I.toInt? (env "p" + 2) = some (q + 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi4112r53Nondeg.body → (q < 0 → I.sin (env "a" + env "b" * w ^ j) ≠ 0) := by
    intro w h
    simp [rubi4112r53Nondeg, Defined, eval, hk_m, hk_n, hk_p, hk0, hj0] at h
    first | exact h | exact fun h' => h h' | tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r53Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hM := hBody w hw
      simp [Defined, eval, hk_m, hk_n, hk_p, ea, ea', eb, eb', ec, ec', ep1, ep1', ep2, ep2', eq1, eq2, hk0, hj0, hkj, hkj1, hkj2, hq0, hq1, hq2]
      first | done | exact hM hq0 | exact fun h => hM (by omega) | exact ⟨hM hq0, hM hq0⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hM := hBody w hw
    simp [rubi4112r53Nondeg, Defined, eval, recEnv, hk_m, hk_n, hk_p, ea, ea', eb, eb', ec, ec', ep1, ep1', ep2, ep2', eq1, eq2, hk0, hj0, hkj, hkj1, hkj2, hq0, hq1, hq2, toInt?_neg_one, toInt?_two, hA0, hA1, hA2]
    first | done | exact hM hq0 | exact ⟨hM hq0, hM hq0⟩ | exact fun h => hM (by omega) | exact ⟨fun h => hM (by omega), fun h => hM (by omega)⟩ | (trace_state; sorry)
  · simp only [rubi4112r53Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hM0' := hBody t hF.self_of_nhds
    have hM0 : I.sin (env "a" + env "b" * t ^ j) ≠ 0 := hM0' hq0
    have hΦ1' : HasDerivAt (Φ "I1") (t ^ k * I.sin (env "a" + env "b" * t ^ j) ^ (q + 2)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, hk_p, ep2, ep2', eq2, ec, ec']
    have hΦ2' : HasDerivAt (Φ "I2") (t ^ (k - 2 * j) * I.sin (env "a" + env "b" * t ^ j) ^ (q + 2)) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, hk_p, ep2, ep2', eq2, ec, ec']
    have hEF : eval I (Function.update env "x" t) rubi4112r53Nondeg.body = t ^ k * I.sin (env "a" + env "b" * t ^ j) ^ q := by
      simp [rubi4112r53Nondeg, eval, hk_m, hk_n, hk_p]
    set W2 := (env "b" ^ 2 * env "n" ^ 2 * (env "p" + 1) * (env "p" + 2))⁻¹ with hW2_def
    set W1 := (env "b" * env "n" * (env "p" + 1))⁻¹ with hW1_def
    set Pv := ((env "p" + 1))⁻¹ with hPv_def
    have hU2 : (env "b" ^ 2 * env "n" ^ 2 * (env "p" + 1) * (env "p" + 2)) * W2 = 1 := by rw [hW2_def]; exact mul_inv_cancel₀ (by simp_all)
    have hW1e : W1 = env "b" * env "n" * (env "p" + 2) * W2 := by
      rw [hW1_def, hW2_def]
      simp only [h_n, h_p] at hA0 hA1 hA2 ⊢
      casesm* _ ∧ _
      first | (field_simp; done) | (field_simp; ring)
    have hPve : Pv = env "b" ^ 2 * env "n" ^ 2 * (env "p" + 2) * W2 := by
      rw [hPv_def, hW2_def]
      simp only [h_n, h_p] at hA0 hA1 hA2 ⊢
      casesm* _ ∧ _
      first | (field_simp; done) | (field_simp; ring)
    have hfun : (fun w => eval I (recEnv env (rubi4112r53Nondeg.integrals.map (·.1)) Φ "x" w) rubi4112r53Nondeg.result) =
        fun w => 1 * w ^ (k - j + 1) * I.cos (env "a" + env "b" * w ^ j) * I.sin (env "a" + env "b" * w ^ j) ^ (q + 1) * W1 + -1 * (env "m" + -1 * env "n" + 1) * w ^ (k - 2 * j + 1) * I.sin (env "a" + env "b" * w ^ j) ^ (q + 2) * W2 + (env "p" + 2) * Pv * Φ "I1" w + (env "m" + -1 * env "n" + 1) * (env "m" + -1 * 2 * env "n" + 1) * W2 * Φ "I2" w := by
      funext w
      simp [rubi4112r53Nondeg, eval, recEnv, hk_m, hk_n, hk_p, ea, ea', eb, eb', ep1, ep1', eq1, eq2, toInt?_neg_one, toInt?_two, hW2_def, hW1_def, hPv_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hin : HasDerivAt (fun w => (env "a" + env "b" * w ^ j)) (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t (Or.inr (by omega))).const_mul _).const_add _
    have hMd := HasDerivAt.comp t (hs _) hin
    have hNd := HasDerivAt.comp t (hcs _) hin
    have hX1 := hasDerivAt_zpow (k - 2 * j + 1) t (Or.inr (by omega))
    have hX2 := hasDerivAt_zpow (k - j + 1) t (Or.inr (by omega))
    have hMq1 := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ (Or.inl hM0)) hMd
    have hMq2 := HasDerivAt.comp t (hasDerivAt_zpow (q + 2) _ (Or.inl hM0)) hMd
    refine (((((((hX2.const_mul (1)).mul hNd).mul hMq1).mul_const W1).add (((hX1.const_mul _).mul hMq2).mul_const W2)).add
      (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [show q + 2 - 1 = q + 1 by ring]
    have rM1 : I.sin (env "a" + env "b" * t ^ j) ^ (q + 1) = I.sin (env "a" + env "b" * t ^ j) ^ q * I.sin (env "a" + env "b" * t ^ j) := zpow_add_one₀ hM0 q
    have rM2 : I.sin (env "a" + env "b" * t ^ j) ^ (q + 2) = I.sin (env "a" + env "b" * t ^ j) ^ q * I.sin (env "a" + env "b" * t ^ j) * I.sin (env "a" + env "b" * t ^ j) := by
      rw [show q + 2 = q + 1 + 1 by ring, zpow_add_one₀ hM0, zpow_add_one₀ hM0]
    rw [rM2, rM1]
    generalize I.sin (env "a" + env "b" * t ^ j) ^ q = Rm
    have za : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b → t ^ (a + b) = t ^ a * t ^ b := by
      intro a b ha hb
      lift a to ℕ using ha
      lift b to ℕ using hb
      rw [← Nat.cast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]
    have r1 : t ^ (k - 2 * j + 1) = t ^ (k - 2 * j) * t := zpow_succ_of _ _ (Or.inr (by omega))
    have r2 : t ^ (k - j) = t ^ (k - 2 * j) * t ^ j := by
      rw [← za _ _ (by omega) (by omega)]; congr 1; ring
    have r3 : t ^ (k - j + 1) = t ^ (k - 2 * j) * t ^ j * t := by
      rw [zpow_succ_of _ _ (Or.inr (by omega)), r2]
    have r4 : t ^ k = t ^ (k - 2 * j) * t ^ j * t ^ j := by
      rw [← za _ _ (by omega) (by omega), ← za _ _ (by omega) (by omega)]; congr 1; ring
    have k1 : t ^ (j - 1) * t = t ^ j := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [r4, r3, r1, r2]
    have hpt := hp (env "a" + env "b" * t ^ j)
    generalize I.sin (env "a" + env "b" * t ^ j) = S at hpt ⊢
    generalize I.cos (env "a" + env "b" * t ^ j) = C at hpt ⊢
    generalize t ^ (k - 2 * j) = P0
    generalize t ^ (j - 1) = N1 at k1 ⊢
    generalize t ^ j = Xn at k1 ⊢
    rw [hW1e, hPve]
    clear_value W2 W1 Pv
    simp only [h_m, h_n, h_p] at hU2 ⊢
    push_cast
    linear_combination (C^2*N1*P0*Rm*Xn*t + P0*Rm*S^2*Xn^2) * hU2 + (N1*P0*Rm*Xn*t) * hpt + (-C*P0*Rm*S*W2*env "b"*(k : 𝕜)*(j : 𝕜)*(q : 𝕜) - 2*C*P0*Rm*S*W2*env "b"*(k : 𝕜)*(j : 𝕜) + C*P0*Rm*S*W2*env "b"*(j : 𝕜)^2*(q : 𝕜) + 2*C*P0*Rm*S*W2*env "b"*(j : 𝕜)^2 - C*P0*Rm*S*W2*env "b"*(j : 𝕜)*(q : 𝕜) - 2*C*P0*Rm*S*W2*env "b"*(j : 𝕜) - P0*Rm*S^2*W2*Xn*env "b"^2*(j : 𝕜)^2*(q : 𝕜) - 2*P0*Rm*S^2*W2*Xn*env "b"^2*(j : 𝕜)^2 - P0*Rm*S^2*Xn + P0*Rm*Xn) * k1

theorem rubi4112r54Nondeg_holds (I : Interp 𝕜) (hlt : ∀ q r : ℚ, I.lt (q : 𝕜) (r : 𝕜) ↔ q < r)
    (hs : ∀ u : 𝕜, HasDerivAt I.sin (I.cos u) u) (hcs : ∀ u : 𝕜, HasDerivAt I.cos (-I.sin u) u)
    (hp : ∀ u : 𝕜, I.sin u ^ 2 + I.cos u ^ 2 = 1) :
    AntiderivRecHolds I "x" rubi4112r54Nondeg.conditions rubi4112r54Nondeg.body rubi4112r54Nondeg.result rubi4112r54Nondeg.integrals := by
  intro env hc t hF
  have hA0 := hc (.ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)) (by simp [rubi4112r54Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA0
  have hA1 := hc (.ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int 0)) (by simp [rubi4112r54Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA1
  have hA2 := hc (.ne (.app2 .add (.var "p") (.int 1)) (.int 0)) (by simp [rubi4112r54Nondeg])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hA2
  have gp := hc (.gt (.int (-1)) (.var "p")) (by simp [rubi4112r54Nondeg])
  have gn := hc (.gt (.var "n") (.int 0)) (by simp [rubi4112r54Nondeg])
  have gm := hc (.gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))) (by simp [rubi4112r54Nondeg])
  rcases hk_m : I.toInt? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r54Nondeg, Defined, eval, hk_m] at h
  rcases hk_n : I.toInt? (env "n") with _ | j
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r54Nondeg, Defined, eval, hk_m, hk_n] at h
  rcases hk_p : I.toInt? (env "p") with _ | q
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r54Nondeg, Defined, eval, hk_m, hk_n, hk_p] at h
  have h_m : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk_m
  have h_n : env "n" = (j : 𝕜) := (I.toInt?_eq _ _).1 hk_n
  have h_p : env "p" = (q : 𝕜) := (I.toInt?_eq _ _).1 hk_p
  have ord : ∀ (x y : ℤ), I.lt (x : 𝕜) (y : 𝕜) → x < y := by
    intro x y h
    have h' : I.lt ((x : ℚ) : 𝕜) ((y : ℚ) : 𝕜) := by rw [Rat.cast_intCast, Rat.cast_intCast]; exact h
    exact_mod_cast (hlt _ _).1 h'
  have hqq : q < -1 := by
    simp only [Cond.Holds, Defined, eval, true_and] at gp
    rw [h_p] at gp
    exact ord _ _ (by simpa using gp)
  have hj : 0 < j := by
    simp only [Cond.Holds, Defined, eval, true_and] at gn
    rw [h_n] at gn
    exact ord _ _ (by simpa using gn)
  have hk : 2 * j - 1 < k := by
    simp only [Cond.Holds, Defined, eval, true_and] at gm
    rw [h_n, h_m] at gm
    have := ord (2 * j - 1) k (by push_cast; simpa [sub_eq_add_neg] using gm)
    exact this
  have hq22 : q ≠ -2 := by
    have h := hc (.ne (.var "p") (.int (-2))) (by simp [rubi4112r54Nondeg])
    simp [Cond.Holds, Defined, eval] at h; intro h0; apply h; rw [h_p, h0]; simp
  have hq0 : q < 0 := by omega
  have hq1 : q + 1 < 0 := by omega
  have hq2 : q + 2 < 0 := by omega
  have hk0 : ¬ k < 0 := by omega
  have hj0 : ¬ j < 0 := by omega
  have hkj : ¬ k - 2 * j < 0 := by omega
  have hkj1 : ¬ k - 2 * j + 1 < 0 := by omega
  have hkj2 : ¬ k - j + 1 < 0 := by omega
  have ea : I.toInt? (env "m" + -1 * 2 * env "n" + 1) = some (k - 2 * j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ea' : I.toInt? (env "m" + -(2 * env "n") + 1) = some (k - 2 * j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have eb : I.toInt? (env "m" + -1 * env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have eb' : I.toInt? (env "m" + -env "n" + 1) = some (k - j + 1) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ec : I.toInt? (env "m" + -1 * 2 * env "n") = some (k - 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ec' : I.toInt? (env "m" + -(2 * env "n")) = some (k - 2 * j) := (I.toInt?_eq _ _).2 (by rw [h_m, h_n]; push_cast; ring)
  have ep1 : I.toInt? (env "p" + -1 * 1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep1' : I.toInt? (env "p" + -1) = some (q - 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2 : I.toInt? (env "p" + -1 * 2) = some (q - 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep2' : I.toInt? (env "p" + -2) = some (q - 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have eq1 : I.toInt? (env "p" + 1) = some (q + 1) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have eq2 : I.toInt? (env "p" + 2) = some (q + 2) := (I.toInt?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hBody : ∀ w, Defined I (Function.update env "x" w) rubi4112r54Nondeg.body → (q < 0 → I.cos (env "a" + env "b" * w ^ j) ≠ 0) := by
    intro w h
    simp [rubi4112r54Nondeg, Defined, eval, hk_m, hk_n, hk_p, hk0, hj0] at h
    first | exact h | exact fun h' => h h' | tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r54Nondeg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hM := hBody w hw
      simp [Defined, eval, hk_m, hk_n, hk_p, ea, ea', eb, eb', ec, ec', ep1, ep1', ep2, ep2', eq1, eq2, hk0, hj0, hkj, hkj1, hkj2, hq0, hq1, hq2]
      first | done | exact hM hq0 | exact fun h => hM (by omega) | exact ⟨hM hq0, hM hq0⟩ | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hM := hBody w hw
    simp [rubi4112r54Nondeg, Defined, eval, recEnv, hk_m, hk_n, hk_p, ea, ea', eb, eb', ec, ec', ep1, ep1', ep2, ep2', eq1, eq2, hk0, hj0, hkj, hkj1, hkj2, hq0, hq1, hq2, toInt?_neg_one, toInt?_two, hA0, hA1, hA2]
    first | done | exact hM hq0 | exact ⟨hM hq0, hM hq0⟩ | exact fun h => hM (by omega) | exact ⟨fun h => hM (by omega), fun h => hM (by omega)⟩ | (trace_state; sorry)
  · simp only [rubi4112r54Nondeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hM0' := hBody t hF.self_of_nhds
    have hM0 : I.cos (env "a" + env "b" * t ^ j) ≠ 0 := hM0' hq0
    have hΦ1' : HasDerivAt (Φ "I1") (t ^ k * I.cos (env "a" + env "b" * t ^ j) ^ (q + 2)) t := by
      convert hΦ1 using 1
      simp [eval, hk_m, hk_n, hk_p, ep2, ep2', eq2, ec, ec']
    have hΦ2' : HasDerivAt (Φ "I2") (t ^ (k - 2 * j) * I.cos (env "a" + env "b" * t ^ j) ^ (q + 2)) t := by
      convert hΦ2 using 1
      simp [eval, hk_m, hk_n, hk_p, ep2, ep2', eq2, ec, ec']
    have hEF : eval I (Function.update env "x" t) rubi4112r54Nondeg.body = t ^ k * I.cos (env "a" + env "b" * t ^ j) ^ q := by
      simp [rubi4112r54Nondeg, eval, hk_m, hk_n, hk_p]
    set W2 := (env "b" ^ 2 * env "n" ^ 2 * (env "p" + 1) * (env "p" + 2))⁻¹ with hW2_def
    set W1 := (env "b" * env "n" * (env "p" + 1))⁻¹ with hW1_def
    set Pv := ((env "p" + 1))⁻¹ with hPv_def
    have hU2 : (env "b" ^ 2 * env "n" ^ 2 * (env "p" + 1) * (env "p" + 2)) * W2 = 1 := by rw [hW2_def]; exact mul_inv_cancel₀ (by simp_all)
    have hW1e : W1 = env "b" * env "n" * (env "p" + 2) * W2 := by
      rw [hW1_def, hW2_def]
      simp only [h_n, h_p] at hA0 hA1 hA2 ⊢
      casesm* _ ∧ _
      first | (field_simp; done) | (field_simp; ring)
    have hPve : Pv = env "b" ^ 2 * env "n" ^ 2 * (env "p" + 2) * W2 := by
      rw [hPv_def, hW2_def]
      simp only [h_n, h_p] at hA0 hA1 hA2 ⊢
      casesm* _ ∧ _
      first | (field_simp; done) | (field_simp; ring)
    have hfun : (fun w => eval I (recEnv env (rubi4112r54Nondeg.integrals.map (·.1)) Φ "x" w) rubi4112r54Nondeg.result) =
        fun w => -1 * w ^ (k - j + 1) * I.sin (env "a" + env "b" * w ^ j) * I.cos (env "a" + env "b" * w ^ j) ^ (q + 1) * W1 + -1 * (env "m" + -1 * env "n" + 1) * w ^ (k - 2 * j + 1) * I.cos (env "a" + env "b" * w ^ j) ^ (q + 2) * W2 + (env "p" + 2) * Pv * Φ "I1" w + (env "m" + -1 * env "n" + 1) * (env "m" + -1 * 2 * env "n" + 1) * W2 * Φ "I2" w := by
      funext w
      simp [rubi4112r54Nondeg, eval, recEnv, hk_m, hk_n, hk_p, ea, ea', eb, eb', ep1, ep1', eq1, eq2, toInt?_neg_one, toInt?_two, hW2_def, hW1_def, hPv_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
      try first | ring1 | simp
    rw [hfun, hEF]
    have hin : HasDerivAt (fun w => (env "a" + env "b" * w ^ j)) (env "b" * ((j : 𝕜) * t ^ (j - 1))) t :=
      ((hasDerivAt_zpow j t (Or.inr (by omega))).const_mul _).const_add _
    have hMd := HasDerivAt.comp t (hcs _) hin
    have hNd := HasDerivAt.comp t (hs _) hin
    have hX1 := hasDerivAt_zpow (k - 2 * j + 1) t (Or.inr (by omega))
    have hX2 := hasDerivAt_zpow (k - j + 1) t (Or.inr (by omega))
    have hMq1 := HasDerivAt.comp t (hasDerivAt_zpow (q + 1) _ (Or.inl hM0)) hMd
    have hMq2 := HasDerivAt.comp t (hasDerivAt_zpow (q + 2) _ (Or.inl hM0)) hMd
    refine (((((((hX2.const_mul (-1)).mul hNd).mul hMq1).mul_const W1).add (((hX1.const_mul _).mul hMq2).mul_const W2)).add
      (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    rw [show q + 2 - 1 = q + 1 by ring]
    have rM1 : I.cos (env "a" + env "b" * t ^ j) ^ (q + 1) = I.cos (env "a" + env "b" * t ^ j) ^ q * I.cos (env "a" + env "b" * t ^ j) := zpow_add_one₀ hM0 q
    have rM2 : I.cos (env "a" + env "b" * t ^ j) ^ (q + 2) = I.cos (env "a" + env "b" * t ^ j) ^ q * I.cos (env "a" + env "b" * t ^ j) * I.cos (env "a" + env "b" * t ^ j) := by
      rw [show q + 2 = q + 1 + 1 by ring, zpow_add_one₀ hM0, zpow_add_one₀ hM0]
    rw [rM2, rM1]
    generalize I.cos (env "a" + env "b" * t ^ j) ^ q = Rm
    have za : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b → t ^ (a + b) = t ^ a * t ^ b := by
      intro a b ha hb
      lift a to ℕ using ha
      lift b to ℕ using hb
      rw [← Nat.cast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]
    have r1 : t ^ (k - 2 * j + 1) = t ^ (k - 2 * j) * t := zpow_succ_of _ _ (Or.inr (by omega))
    have r2 : t ^ (k - j) = t ^ (k - 2 * j) * t ^ j := by
      rw [← za _ _ (by omega) (by omega)]; congr 1; ring
    have r3 : t ^ (k - j + 1) = t ^ (k - 2 * j) * t ^ j * t := by
      rw [zpow_succ_of _ _ (Or.inr (by omega)), r2]
    have r4 : t ^ k = t ^ (k - 2 * j) * t ^ j * t ^ j := by
      rw [← za _ _ (by omega) (by omega), ← za _ _ (by omega) (by omega)]; congr 1; ring
    have k1 : t ^ (j - 1) * t = t ^ j := by
      rw [← zpow_succ_of _ _ (Or.inr (by omega)), sub_add_cancel]
    rw [r4, r3, r1, r2]
    have hpt := hp (env "a" + env "b" * t ^ j)
    generalize I.sin (env "a" + env "b" * t ^ j) = S at hpt ⊢
    generalize I.cos (env "a" + env "b" * t ^ j) = C at hpt ⊢
    generalize t ^ (k - 2 * j) = P0
    generalize t ^ (j - 1) = N1 at k1 ⊢
    generalize t ^ j = Xn at k1 ⊢
    rw [hW1e, hPve]
    clear_value W2 W1 Pv
    simp only [h_m, h_n, h_p] at hU2 ⊢
    push_cast
    linear_combination (C^2*P0*Rm*Xn^2 + N1*P0*Rm*S^2*Xn*t) * hU2 + (-N1*P0*Rm*W2*Xn*env "b"^2*(j : 𝕜)^2*(q : 𝕜)*t - 2*N1*P0*Rm*W2*Xn*env "b"^2*(j : 𝕜)^2*t + P0*Rm*W2*Xn^2*env "b"^2*(j : 𝕜)^2*(q : 𝕜) + 2*P0*Rm*W2*Xn^2*env "b"^2*(j : 𝕜)^2 + P0*Rm*Xn^2) * hpt + (C*P0*Rm*S*W2*env "b"*(k : 𝕜)*(j : 𝕜)*(q : 𝕜) + 2*C*P0*Rm*S*W2*env "b"*(k : 𝕜)*(j : 𝕜) - C*P0*Rm*S*W2*env "b"*(j : 𝕜)^2*(q : 𝕜) - 2*C*P0*Rm*S*W2*env "b"*(j : 𝕜)^2 + C*P0*Rm*S*W2*env "b"*(j : 𝕜)*(q : 𝕜) + 2*C*P0*Rm*S*W2*env "b"*(j : 𝕜) + P0*Rm*S^2*W2*Xn*env "b"^2*(j : 𝕜)^2*(q : 𝕜) + 2*P0*Rm*S^2*W2*Xn*env "b"^2*(j : 𝕜)^2 + P0*Rm*S^2*Xn - P0*Rm*W2*Xn*env "b"^2*(j : 𝕜)^2*(q : 𝕜) - 2*P0*Rm*W2*Xn*env "b"^2*(j : 𝕜)^2) * k1

theorem rubi4112r45Nondeg_real : rubi4112r45Nondeg.Holds .real :=
  rubi4112r45Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos Real.sin_sq_add_cos_sq
theorem rubi4112r45Nondeg_complex : rubi4112r45Nondeg.Holds .complex :=
  rubi4112r45Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos Complex.sin_sq_add_cos_sq
theorem rubi4112r46Nondeg_real : rubi4112r46Nondeg.Holds .real :=
  rubi4112r46Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos Real.sin_sq_add_cos_sq
theorem rubi4112r46Nondeg_complex : rubi4112r46Nondeg.Holds .complex :=
  rubi4112r46Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos Complex.sin_sq_add_cos_sq
theorem rubi4112r53Nondeg_real : rubi4112r53Nondeg.Holds .real :=
  rubi4112r53Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos Real.sin_sq_add_cos_sq
theorem rubi4112r53Nondeg_complex : rubi4112r53Nondeg.Holds .complex :=
  rubi4112r53Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos Complex.sin_sq_add_cos_sq
theorem rubi4112r54Nondeg_real : rubi4112r54Nondeg.Holds .real :=
  rubi4112r54Nondeg_holds Interp.real Interp.real_lt_rat Real.hasDerivAt_sin Real.hasDerivAt_cos Real.sin_sq_add_cos_sq
theorem rubi4112r54Nondeg_complex : rubi4112r54Nondeg.Holds .complex :=
  rubi4112r54Nondeg_holds Interp.complex Interp.complex_lt_rat Complex.hasDerivAt_sin Complex.hasDerivAt_cos Complex.sin_sq_add_cos_sq

end Proofs

end OSR.IntegrationRec100
