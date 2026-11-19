import OSR.IntegrationRec91

/-!
# Integration (RUBI): `sinh` and `cosh` of `d (a + b log(c xⁿ))`

With `θ = d (a + b log(c xⁿ))`, `x θ' = b d n` wherever `log(c xⁿ)` is defined
(also for `n = 0`), and `cosh² θ - sinh² θ = 1` gives the closed forms and the
reduction formulas.  6.7.8 #3 to #6 are proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec156

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 6.7.8 #3 -/
def rubi678r3 : CRule where
  id := "integration.rubi_6_7_8_r3"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:3"
  shape := .antideriv; x := "x"
  body := (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.var "x")) (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int (-1)))))
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int 0)]
  priority := 11866
  description := "RUBI 6.7.8 #3"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:3" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p.m#3"

/-- RUBI 6.7.8 #4 -/
def rubi678r4 : CRule where
  id := "integration.rubi_6_7_8_r4"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:4"
  shape := .antideriv; x := "x"
  body := (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.var "x")) (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int (-1)))))
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int 0)]
  priority := 11867
  description := "RUBI 6.7.8 #4"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:4" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p.m#4"

/-- RUBI 6.7.8 #5 -/
def rubi678r5 : CRule where
  id := "integration.rubi_6_7_8_r5"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:5"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p"))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.var "p")) (.var "x")) (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 1),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int 0)]
  priority := 11868
  description := "RUBI 6.7.8 #5"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:5" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p.m#5"

/-- RUBI 6.7.8 #6 -/
def rubi678r6 : CRule where
  id := "integration.rubi_6_7_8_r6"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:6"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p"))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.var "p")) (.var "x")) (.pow (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 1),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.int (-1)) (.int 1))) (.int 0)]
  priority := 11869
  description := "RUBI 6.7.8 #6"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:6" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p.m#6"

/-! ## Proofs -/

theorem rubi678r3_real : rubi678r3.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi678r3.conditions rubi678r3.body rubi678r3.result
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi678r3, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have ht := hF.self_of_nhds
  simp [rubi678r3, Defined, eval, Interp.real, i2, im1, hk_n] at ht
  obtain ⟨hpos0, hpos⟩ : (kn < 0 → t ≠ 0) ∧ 0 < env "c" * t ^ kn := by
    first | exact ht | exact ht.1
  have hor : t ≠ 0 ∨ 0 ≤ kn := by
    by_cases h : kn < 0
    · exact Or.inl (hpos0 h)
    · exact Or.inr (by omega)
  have hne : env "c" * t ^ kn ≠ 0 := hpos.ne'
  have hL := (Real.hasDerivAt_log hne).comp t ((hasDerivAt_zpow kn t hor).const_mul (env "c"))
  have hkey : t * ((env "c" * t ^ kn)⁻¹ * (env "c" * ((kn : ℝ) * t ^ (kn - 1)))) = kn := by
    rcases eq_or_ne t 0 with h0 | h0
    · have h1 : (t : ℝ) ^ kn ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hk0 : kn = 0 := by
        by_contra hk; rw [h0] at h1; exact h1 (zero_zpow kn hk)
      subst hk0; simp
    · have hc0 : env "c" ≠ 0 := fun h => hne (by rw [h, zero_mul])
      rw [zpow_sub_one₀ h0]
      field_simp
  obtain ⟨Q, hQ, hkQ⟩ : ∃ Q : ℝ, (env "c" * t ^ kn)⁻¹ * (env "c" * ((kn : ℝ) * t ^ (kn - 1))) = Q ∧ t * Q = kn :=
    ⟨_, rfl, hkey⟩
  rw [hQ] at hL
  have hθ := ((hL.const_mul (env "b")).const_add (env "a")).const_mul (env "d")
  have hS := (Real.hasDerivAt_sinh _).comp t hθ
  have hC := (Real.hasDerivAt_cosh _).comp t hθ
  have hcd := hc _ (List.mem_cons_self)
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    simp [rubi678r3, Defined, eval, Interp.real, i2, im1, hk_n] at hw ⊢
    tauto
  · have hF0 := ((((hasDerivAt_id t).mul (Real.hasDerivAt_sinh _ |>.comp t hθ)).neg).mul_const (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + -1)⁻¹).add
      ((((hasDerivAt_id t).const_mul (env "b" * env "d" * env "n")).mul (Real.hasDerivAt_cosh _ |>.comp t hθ)).mul_const (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + -1)⁻¹)
    convert hF0 using 1
    · funext v; simp [rubi678r3, eval, Interp.real, i2, im1, hk_n, Function.comp_def]; try (first | ring1 | simp | (left; ring1))
    · simp [rubi678r3, eval, Interp.real, i2, im1, hk_n, Function.comp_def]
      have hr := Real.cosh_sq_sub_sinh_sq (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn)))
      generalize Real.sinh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) = S at *
      generalize Real.cosh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) = C at *
      rw [hkn] at hcd ⊢
      have hK : env "d" ^ 2 * env "b" ^ 2 * (kn : ℝ) ^ 2 + -1 ≠ 0 := by intro h; apply hcd; linear_combination h
      have hK' : env "b" ^ 2 * env "d" ^ 2 * (kn : ℝ) ^ 2 + -1 ≠ 0 := by intro h; apply hcd; linear_combination h
      field_simp
      linear_combination (0) * hr + (-env "b"*env "d"*(-C + S*env "b"*env "d"*(kn:ℝ))) * hkQ

theorem rubi678r4_real : rubi678r4.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi678r4.conditions rubi678r4.body rubi678r4.result
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi678r4, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have ht := hF.self_of_nhds
  simp [rubi678r4, Defined, eval, Interp.real, i2, im1, hk_n] at ht
  obtain ⟨hpos0, hpos⟩ : (kn < 0 → t ≠ 0) ∧ 0 < env "c" * t ^ kn := by
    first | exact ht | exact ht.1
  have hor : t ≠ 0 ∨ 0 ≤ kn := by
    by_cases h : kn < 0
    · exact Or.inl (hpos0 h)
    · exact Or.inr (by omega)
  have hne : env "c" * t ^ kn ≠ 0 := hpos.ne'
  have hL := (Real.hasDerivAt_log hne).comp t ((hasDerivAt_zpow kn t hor).const_mul (env "c"))
  have hkey : t * ((env "c" * t ^ kn)⁻¹ * (env "c" * ((kn : ℝ) * t ^ (kn - 1)))) = kn := by
    rcases eq_or_ne t 0 with h0 | h0
    · have h1 : (t : ℝ) ^ kn ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hk0 : kn = 0 := by
        by_contra hk; rw [h0] at h1; exact h1 (zero_zpow kn hk)
      subst hk0; simp
    · have hc0 : env "c" ≠ 0 := fun h => hne (by rw [h, zero_mul])
      rw [zpow_sub_one₀ h0]
      field_simp
  obtain ⟨Q, hQ, hkQ⟩ : ∃ Q : ℝ, (env "c" * t ^ kn)⁻¹ * (env "c" * ((kn : ℝ) * t ^ (kn - 1))) = Q ∧ t * Q = kn :=
    ⟨_, rfl, hkey⟩
  rw [hQ] at hL
  have hθ := ((hL.const_mul (env "b")).const_add (env "a")).const_mul (env "d")
  have hS := (Real.hasDerivAt_sinh _).comp t hθ
  have hC := (Real.hasDerivAt_cosh _).comp t hθ
  have hcd := hc _ (List.mem_cons_self)
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    simp [rubi678r4, Defined, eval, Interp.real, i2, im1, hk_n] at hw ⊢
    tauto
  · have hF0 := ((((hasDerivAt_id t).mul (Real.hasDerivAt_cosh _ |>.comp t hθ)).neg).mul_const (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + -1)⁻¹).add
      ((((hasDerivAt_id t).const_mul (env "b" * env "d" * env "n")).mul (Real.hasDerivAt_sinh _ |>.comp t hθ)).mul_const (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + -1)⁻¹)
    convert hF0 using 1
    · funext v; simp [rubi678r4, eval, Interp.real, i2, im1, hk_n, Function.comp_def]; try (first | ring1 | simp | (left; ring1))
    · simp [rubi678r4, eval, Interp.real, i2, im1, hk_n, Function.comp_def]
      have hr := Real.cosh_sq_sub_sinh_sq (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn)))
      generalize Real.sinh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) = S at *
      generalize Real.cosh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) = C at *
      rw [hkn] at hcd ⊢
      have hK : env "d" ^ 2 * env "b" ^ 2 * (kn : ℝ) ^ 2 + -1 ≠ 0 := by intro h; apply hcd; linear_combination h
      have hK' : env "b" ^ 2 * env "d" ^ 2 * (kn : ℝ) ^ 2 + -1 ≠ 0 := by intro h; apply hcd; linear_combination h
      field_simp
      linear_combination (0) * hr + (-env "b"*env "d"*(C*env "b"*env "d"*(kn:ℝ) - S)) * hkQ

set_option maxHeartbeats 1000000 in
theorem rubi678r5_real : rubi678r5.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi678r5.conditions rubi678r5.body rubi678r5.result rubi678r5.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi678r5, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi678r5, Defined, eval, Interp.real, hk_n, hk_p] at h
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p1 : intValue? (env "p" + -1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p2 : intValue? (env "p" + -2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p3 : intValue? (env "p" + -1 * 1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p4 : intValue? (env "p" + -1 * 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp1 : 1 < kp := by
    have h := hc _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp [Cond.Holds, Defined, eval, Interp.real, hkp] at h; exact_mod_cast h
  have ht := hF.self_of_nhds
  simp [rubi678r5, Defined, eval, Interp.real, i2, im1, hk_n, hk_p, p1, p2, p3, p4] at ht
  obtain ⟨hpos0, hpos⟩ : (kn < 0 → t ≠ 0) ∧ 0 < env "c" * t ^ kn := by
    first | exact ht | exact ht.1
  have hor : t ≠ 0 ∨ 0 ≤ kn := by
    by_cases h : kn < 0
    · exact Or.inl (hpos0 h)
    · exact Or.inr (by omega)
  have hne : env "c" * t ^ kn ≠ 0 := hpos.ne'
  have hL := (Real.hasDerivAt_log hne).comp t ((hasDerivAt_zpow kn t hor).const_mul (env "c"))
  have hkey : t * ((env "c" * t ^ kn)⁻¹ * (env "c" * ((kn : ℝ) * t ^ (kn - 1)))) = kn := by
    rcases eq_or_ne t 0 with h0 | h0
    · have h1 : (t : ℝ) ^ kn ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hk0 : kn = 0 := by
        by_contra hk; rw [h0] at h1; exact h1 (zero_zpow kn hk)
      subst hk0; simp
    · have hc0 : env "c" ≠ 0 := fun h => hne (by rw [h, zero_mul])
      rw [zpow_sub_one₀ h0]
      field_simp
  obtain ⟨Q, hQ, hkQ⟩ : ∃ Q : ℝ, (env "c" * t ^ kn)⁻¹ * (env "c" * ((kn : ℝ) * t ^ (kn - 1))) = Q ∧ t * Q = kn :=
    ⟨_, rfl, hkey⟩
  rw [hQ] at hL
  have hθ := ((hL.const_mul (env "b")).const_add (env "a")).const_mul (env "d")
  have hS := (Real.hasDerivAt_sinh _).comp t hθ
  have hC := (Real.hasDerivAt_cosh _).comp t hθ
  have hcd := hc _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi678r5, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi678r5, Defined, eval, Interp.real, i2, im1, hk_n, hk_p, p1, p2, p3, p4] at hw ⊢
    have : ¬ kp - 2 < 0 := by omega
    have : ¬ kp < 2 := by omega
    have : ¬ kp ≤ 1 := by omega
    have : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
    first | tauto | simp_all
  · filter_upwards [hF] with w hw
    simp [rubi678r5, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, hk_p, p1, p2, p3, p4] at hw ⊢
    have : ¬ kp - 1 < 0 := by omega
    have : ¬ kp < 1 := by omega
    have : ¬ kp ≤ 1 := by omega
    have : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
    first | tauto | simp_all
  · simp only [rubi678r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hSp := (hasDerivAt_zpow kp _ (Or.inr (by omega))).comp t (Real.hasDerivAt_sinh _ |>.comp t hθ)
    have hSq := (hasDerivAt_zpow (kp - 1) _ (Or.inr (by omega))).comp t (Real.hasDerivAt_sinh _ |>.comp t hθ)
    have hF0 := (((((hasDerivAt_id t).mul hSp).neg).mul_const (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" ^ 2 + -1)⁻¹).add
      (((((hasDerivAt_id t).const_mul (env "b" * env "d" * env "n" * env "p")).mul (Real.hasDerivAt_cosh _ |>.comp t hθ)).mul hSq).mul_const (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" ^ 2 + -1)⁻¹)).add
      (hΦ.const_mul (-(env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" * (env "p" + -1)) * (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" ^ 2 + -1)⁻¹))
    convert hF0 using 1
    · funext v; simp [rubi678r5, eval, recEnv, Interp.real, i2, im1, hk_n, hk_p, p1, p2, p3, p4, Function.comp_def]; try (first | ring1 | simp | (left; ring1))
    · simp [rubi678r5, eval, Interp.real, i2, im1, hk_n, hk_p, p1, p2, p3, p4, Function.comp_def]
      have hr := Real.cosh_sq_sub_sinh_sq (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn)))
      have e1 : Real.sinh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) ^ (kp - 1) = Real.sinh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) ^ (kp - 2) * Real.sinh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) := by
        rw [show kp - 1 = (kp - 2) + 1 by ring, zpow_add' (Or.inr (Or.inl (by omega))), zpow_one]
      have e2 : Real.sinh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) ^ kp = Real.sinh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) ^ (kp - 2) * Real.sinh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) ^ 2 := by
        conv_lhs => rw [show kp = (kp - 2) + 2 by ring]
        rw [zpow_add' (Or.inr (Or.inl (by omega)))]; norm_cast
      rw [show kp - 1 - 1 = kp - 2 by ring, e1, e2]
      generalize Real.sinh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) ^ (kp - 2) = P
      generalize Real.sinh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) = S at *
      generalize Real.cosh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) = C at *
      rw [hkn, hkp] at hcd ⊢
      have hK : env "d" ^ 2 * env "b" ^ 2 * (kn : ℝ) ^ 2 * (kp : ℝ) ^ 2 + -1 ≠ 0 := by intro h; apply hcd; linear_combination h
      have hK' : env "b" ^ 2 * env "d" ^ 2 * (kn : ℝ) ^ 2 * (kp : ℝ) ^ 2 + -1 ≠ 0 := by intro h; apply hcd; linear_combination h
      have hK'' : (kp : ℝ) ^ 2 * env "d" ^ 2 * env "b" ^ 2 * (kn : ℝ) ^ 2 + -1 ≠ 0 := by intro h; apply hcd; linear_combination h
      field_simp
      linear_combination (-P*Q*env "b"^2*env "d"^2*(kn:ℝ)*(kp:ℝ)*t*((kp:ℝ) - 1)) * hr + (-P*env "b"*env "d"*(kp:ℝ)*(-C*S + S^2*env "b"*env "d"*(kn:ℝ)*(kp:ℝ) + env "b"*env "d"*(kn:ℝ)*(kp:ℝ) - env "b"*env "d"*(kn:ℝ))) * hkQ

set_option maxHeartbeats 1000000 in
theorem rubi678r6_real : rubi678r6.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi678r6.conditions rubi678r6.body rubi678r6.result rubi678r6.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi678r6, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi678r6, Defined, eval, Interp.real, hk_n, hk_p] at h
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p1 : intValue? (env "p" + -1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p2 : intValue? (env "p" + -2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p3 : intValue? (env "p" + -1 * 1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p4 : intValue? (env "p" + -1 * 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp1 : 1 < kp := by
    have h := hc _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp [Cond.Holds, Defined, eval, Interp.real, hkp] at h; exact_mod_cast h
  have ht := hF.self_of_nhds
  simp [rubi678r6, Defined, eval, Interp.real, i2, im1, hk_n, hk_p, p1, p2, p3, p4] at ht
  obtain ⟨hpos0, hpos⟩ : (kn < 0 → t ≠ 0) ∧ 0 < env "c" * t ^ kn := by
    first | exact ht | exact ht.1
  have hor : t ≠ 0 ∨ 0 ≤ kn := by
    by_cases h : kn < 0
    · exact Or.inl (hpos0 h)
    · exact Or.inr (by omega)
  have hne : env "c" * t ^ kn ≠ 0 := hpos.ne'
  have hL := (Real.hasDerivAt_log hne).comp t ((hasDerivAt_zpow kn t hor).const_mul (env "c"))
  have hkey : t * ((env "c" * t ^ kn)⁻¹ * (env "c" * ((kn : ℝ) * t ^ (kn - 1)))) = kn := by
    rcases eq_or_ne t 0 with h0 | h0
    · have h1 : (t : ℝ) ^ kn ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hk0 : kn = 0 := by
        by_contra hk; rw [h0] at h1; exact h1 (zero_zpow kn hk)
      subst hk0; simp
    · have hc0 : env "c" ≠ 0 := fun h => hne (by rw [h, zero_mul])
      rw [zpow_sub_one₀ h0]
      field_simp
  obtain ⟨Q, hQ, hkQ⟩ : ∃ Q : ℝ, (env "c" * t ^ kn)⁻¹ * (env "c" * ((kn : ℝ) * t ^ (kn - 1))) = Q ∧ t * Q = kn :=
    ⟨_, rfl, hkey⟩
  rw [hQ] at hL
  have hθ := ((hL.const_mul (env "b")).const_add (env "a")).const_mul (env "d")
  have hS := (Real.hasDerivAt_sinh _).comp t hθ
  have hC := (Real.hasDerivAt_cosh _).comp t hθ
  have hcd := hc _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi678r6, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi678r6, Defined, eval, Interp.real, i2, im1, hk_n, hk_p, p1, p2, p3, p4] at hw ⊢
    have : ¬ kp - 2 < 0 := by omega
    have : ¬ kp < 2 := by omega
    have : ¬ kp ≤ 1 := by omega
    have : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
    first | tauto | simp_all
  · filter_upwards [hF] with w hw
    simp [rubi678r6, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, hk_p, p1, p2, p3, p4] at hw ⊢
    have : ¬ kp - 1 < 0 := by omega
    have : ¬ kp < 1 := by omega
    have : ¬ kp ≤ 1 := by omega
    have : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
    first | tauto | simp_all
  · simp only [rubi678r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hSp := (hasDerivAt_zpow kp _ (Or.inr (by omega))).comp t (Real.hasDerivAt_cosh _ |>.comp t hθ)
    have hSq := (hasDerivAt_zpow (kp - 1) _ (Or.inr (by omega))).comp t (Real.hasDerivAt_cosh _ |>.comp t hθ)
    have hF0 := (((((hasDerivAt_id t).mul hSp).neg).mul_const (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" ^ 2 + -1)⁻¹).add
      (((((hasDerivAt_id t).const_mul (env "b" * env "d" * env "n" * env "p")).mul (Real.hasDerivAt_sinh _ |>.comp t hθ)).mul hSq).mul_const (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" ^ 2 + -1)⁻¹)).add
      (hΦ.const_mul ((env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" * (env "p" + -1)) * (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 * env "p" ^ 2 + -1)⁻¹))
    convert hF0 using 1
    · funext v; simp [rubi678r6, eval, recEnv, Interp.real, i2, im1, hk_n, hk_p, p1, p2, p3, p4, Function.comp_def]; try (first | ring1 | simp | (left; ring1))
    · simp [rubi678r6, eval, Interp.real, i2, im1, hk_n, hk_p, p1, p2, p3, p4, Function.comp_def]
      have hr := Real.cosh_sq_sub_sinh_sq (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn)))
      have e1 : Real.cosh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) ^ (kp - 1) = Real.cosh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) ^ (kp - 2) * Real.cosh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) := by
        rw [show kp - 1 = (kp - 2) + 1 by ring, zpow_add' (Or.inr (Or.inl (by omega))), zpow_one]
      have e2 : Real.cosh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) ^ kp = Real.cosh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) ^ (kp - 2) * Real.cosh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) ^ 2 := by
        conv_lhs => rw [show kp = (kp - 2) + 2 by ring]
        rw [zpow_add' (Or.inr (Or.inl (by omega)))]; norm_cast
      rw [show kp - 1 - 1 = kp - 2 by ring, e1, e2]
      generalize Real.cosh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) ^ (kp - 2) = P
      generalize Real.sinh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) = S at *
      generalize Real.cosh (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ kn))) = C at *
      rw [hkn, hkp] at hcd ⊢
      have hK : env "d" ^ 2 * env "b" ^ 2 * (kn : ℝ) ^ 2 * (kp : ℝ) ^ 2 + -1 ≠ 0 := by intro h; apply hcd; linear_combination h
      have hK' : env "b" ^ 2 * env "d" ^ 2 * (kn : ℝ) ^ 2 * (kp : ℝ) ^ 2 + -1 ≠ 0 := by intro h; apply hcd; linear_combination h
      have hK'' : (kp : ℝ) ^ 2 * env "d" ^ 2 * env "b" ^ 2 * (kn : ℝ) ^ 2 + -1 ≠ 0 := by intro h; apply hcd; linear_combination h
      field_simp
      linear_combination (-P*env "b"^2*env "d"^2*(kn:ℝ)*(kp:ℝ)*(Q*t - (kn:ℝ)*(kp:ℝ))) * hr + (-P*env "b"*env "d"*(kp:ℝ)*(-C*S + S^2*env "b"*env "d"*(kn:ℝ)*(kp:ℝ) + env "b"*env "d"*(kn:ℝ))) * hkQ

end OSR.IntegrationRec156
