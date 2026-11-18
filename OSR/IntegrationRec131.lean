import OSR.IntegrationRec91

/-!
# Integration (RUBI): integration by parts of arctanh and arctan of a monomial

`∫ A(u) = x A(u) - ∫ x u' A'(u)` for `A = artanh` (`u = a + b xⁿ` or
`c xⁿ`) and `A = arctan` (`u = a + b xⁿ`).  Mathlib has no derivative of
`Real.artanh`; `hasDerivAt_artanh` derives it from `artanh_eq_half_log`.
Proved over ℝ (`arctanh` has no complex interpretation in the fragment; the
arctan rule is not carried to ℂ).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec131

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #1 -/
def rubi734mr1 : CRule where
  id := "integration.rubi_7_3_4_misc_r1"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:1"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arctanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "n")) (.pow (.app2 .add (.app2 .add (.app2 .add (.int 1) (.app2 .mul (.int (-1)) (.pow (.var "a") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "b")) (.pow (.var "x") (.var "n")))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.int (-1)))))]
  independent := ["a", "b", "n"]
  priority := 10701
  description := "RUBI 7.3.4 #1"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:1" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent.m#1"

/-- RUBI 7.3.7 #1 -/
def rubi737r1 : CRule where
  id := "integration.rubi_7_3_7_r1"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:1"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arctanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "n")) (.pow (.app2 .add (.app2 .add (.app2 .add (.int 1) (.app2 .mul (.int (-1)) (.pow (.var "a") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "b")) (.pow (.var "x") (.var "n")))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.int (-1)))))]
  independent := ["a", "b", "n"]
  priority := 10702
  description := "RUBI 7.3.7 #1"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:1" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#1"

/-- RUBI 7.3.1 #168 -/
def rubi731r168 : CRule where
  id := "integration.rubi_7_3_1_r168"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:168"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctanh (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arctanh (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "n")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "n")) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.int (-1)))))]
  independent := ["c", "n"]
  priority := 10703
  description := "RUBI 7.3.1 #168"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:168" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#168"

/-- RUBI 5.3.7 #1 -/
def rubi537r1 : CRule where
  id := "integration.rubi_5_3_7_r1"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:1"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arctan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "n")) (.pow (.app2 .add (.app2 .add (.app2 .add (.int 1) (.pow (.var "a") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.pow (.var "x") (.var "n")))) (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.int (-1)))))]
  independent := ["a", "b", "n"]
  priority := 10704
  description := "RUBI 5.3.7 #1"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:1" "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#1"

/-! ## Proofs -/

open Set in
/-- The derivative of `Real.artanh` on `(-1, 1)`. -/
theorem hasDerivAt_artanh {x : ℝ} (h1 : -1 < x) (h2 : x < 1) :
    HasDerivAt Real.artanh (1 - x ^ 2)⁻¹ x := by
  have hev : (fun y => 1 / 2 * Real.log ((1 + y) / (1 - y))) =ᶠ[𝓝 x] Real.artanh := by
    filter_upwards [Ioo_mem_nhds h1 h2] with y hy
    rw [Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩]
  have hp : 0 < 1 + x := by linarith
  have hq : 0 < 1 - x := by linarith
  have hd : HasDerivAt (fun y => (1 + y) / (1 - y)) ((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) x :=
    ((hasDerivAt_id x).const_add 1).div ((hasDerivAt_id x).const_sub 1) (ne_of_gt hq) |>.congr_deriv (by simp)
  have := (hd.log (div_pos hp hq).ne').const_mul (1 / 2 : ℝ)
  refine (this.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  have hne : 1 - x ^ 2 ≠ 0 := by nlinarith
  have hq' : 1 - x ≠ 0 := ne_of_gt hq
  have hp' : 1 + x ≠ 0 := ne_of_gt hp
  field_simp
  ring

/-- `n (x · x^(n-1)) = n xⁿ` for every integer `n` and every `x`. -/
theorem int_mul_zpow_pred (x : ℝ) (k : ℤ) : (k : ℝ) * (x * x ^ (k - 1)) = k * x ^ k := by
  rcases eq_or_ne k 0 with hk | hk
  · simp [hk]
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx, zero_zpow k hk]
  · rw [mul_comm x, ← zpow_add_one₀ hx, sub_add_cancel]

theorem rubi734mr1_real : rubi734mr1.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr1.conditions rubi734mr1.body rubi734mr1.result rubi734mr1.integrals
  intro env hc t hF
  rcases hk : intValue? (env "n") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi734mr1, Defined, eval, Interp.real, hk] at h
  have h_n : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have e2 : intValue? (2 * env "n") = some (2 * k) := (intValue?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hsq : ∀ w : ℝ, w ^ (2 * k) = (w ^ k) ^ 2 := fun w => by rw [mul_comm, zpow_mul]; norm_cast
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi734mr1.body → (k < 0 → w ≠ 0) ∧ -1 < (env "a" + env "b" * w ^ k) ∧ (env "a" + env "b" * w ^ k) < 1 := by
    intro w h
    simp [rubi734mr1, Defined, eval, Interp.real, hk] at h
    first | exact h | tauto | (trace_state; sorry)
  have hDnz : ∀ w, -1 < (env "a" + env "b" * w ^ k) → (env "a" + env "b" * w ^ k) < 1 → (1 - (env "a" + env "b" * w ^ k) ^ 2) ≠ 0 := by
    intro w h1 h2; nlinarith
  obtain ⟨hw0, hd1, hd2⟩ := hBody t hF.self_of_nhds
  have hor : t ≠ 0 ∨ 0 ≤ k := by
    by_cases h : k < 0
    · exact Or.inl (hw0 h)
    · exact Or.inr (by omega)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734mr1, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [Defined, eval, Interp.real, hk, e2, i2, im1, hsq]
    have hA1 := hb.1
    have hA2 : 2 * k < 0 → ¬ w = 0 := fun h => hb.1 (by omega)
    have hDw : (1 - (env "a" + env "b" * w ^ k) ^ 2) ≠ 0 := hDnz w hb.2.1 hb.2.2
    refine ⟨hA1, ?_⟩
    try refine ⟨⟨hA1, hA2⟩, ?_⟩
    try refine ⟨hA2, ?_⟩
    intro h0; apply hDw; linear_combination h0
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi734mr1, Defined, eval, recEnv, Interp.real, hk]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi734mr1, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t ^ k * (1 - (env "a" + env "b" * t ^ k) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk, e2, i2, im1, hsq]
      first | ring1 | (left; ring1) | trivial | simp | (trace_state; sorry)
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734mr1.integrals.map (·.1)) Φ "x" w) rubi734mr1.result) =
        fun w => w * Real.artanh (env "a" + env "b" * w ^ k) + -1 * env "b" * env "n" * Φ "I1" w := by
      funext w; simp [rubi734mr1, eval, recEnv, Interp.real, hk]
    have hEF : eval Interp.real (Function.update env "x" t) rubi734mr1.body = Real.artanh (env "a" + env "b" * t ^ k) := by
      simp [rubi734mr1, eval, Interp.real, hk]
    rw [hfun, hEF]
    have hu : HasDerivAt (fun w => (env "a" + env "b" * w ^ k)) (env "b" * ((k : ℝ) * t ^ (k - 1))) t := by
      simpa using (((hasDerivAt_zpow k t hor).const_mul (env "b")).const_add (env "a"))
    have hA := (hasDerivAt_artanh hd1 hd2).comp t hu
    refine (((hasDerivAt_id t).mul hA).add (hΦ'.const_mul _)).congr_deriv ?_
    have tk := int_mul_zpow_pred t k
    rw [h_n]
    simp only [id, one_mul, Function.comp_def]
    generalize (1 - (env "a" + env "b" * t ^ k) ^ 2)⁻¹ = Q
    linear_combination (env "b" * Q) * tk

theorem rubi737r1_real : rubi737r1.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r1.conditions rubi737r1.body rubi737r1.result rubi737r1.integrals
  intro env hc t hF
  rcases hk : intValue? (env "n") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi737r1, Defined, eval, Interp.real, hk] at h
  have h_n : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have e2 : intValue? (2 * env "n") = some (2 * k) := (intValue?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hsq : ∀ w : ℝ, w ^ (2 * k) = (w ^ k) ^ 2 := fun w => by rw [mul_comm, zpow_mul]; norm_cast
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r1.body → (k < 0 → w ≠ 0) ∧ -1 < (env "a" + env "b" * w ^ k) ∧ (env "a" + env "b" * w ^ k) < 1 := by
    intro w h
    simp [rubi737r1, Defined, eval, Interp.real, hk] at h
    first | exact h | tauto | (trace_state; sorry)
  have hDnz : ∀ w, -1 < (env "a" + env "b" * w ^ k) → (env "a" + env "b" * w ^ k) < 1 → (1 - (env "a" + env "b" * w ^ k) ^ 2) ≠ 0 := by
    intro w h1 h2; nlinarith
  obtain ⟨hw0, hd1, hd2⟩ := hBody t hF.self_of_nhds
  have hor : t ≠ 0 ∨ 0 ≤ k := by
    by_cases h : k < 0
    · exact Or.inl (hw0 h)
    · exact Or.inr (by omega)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r1, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [Defined, eval, Interp.real, hk, e2, i2, im1, hsq]
    have hA1 := hb.1
    have hA2 : 2 * k < 0 → ¬ w = 0 := fun h => hb.1 (by omega)
    have hDw : (1 - (env "a" + env "b" * w ^ k) ^ 2) ≠ 0 := hDnz w hb.2.1 hb.2.2
    refine ⟨hA1, ?_⟩
    try refine ⟨⟨hA1, hA2⟩, ?_⟩
    try refine ⟨hA2, ?_⟩
    intro h0; apply hDw; linear_combination h0
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi737r1, Defined, eval, recEnv, Interp.real, hk]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi737r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t ^ k * (1 - (env "a" + env "b" * t ^ k) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk, e2, i2, im1, hsq]
      first | ring1 | (left; ring1) | trivial | simp | (trace_state; sorry)
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r1.integrals.map (·.1)) Φ "x" w) rubi737r1.result) =
        fun w => w * Real.artanh (env "a" + env "b" * w ^ k) + -1 * env "b" * env "n" * Φ "I1" w := by
      funext w; simp [rubi737r1, eval, recEnv, Interp.real, hk]
    have hEF : eval Interp.real (Function.update env "x" t) rubi737r1.body = Real.artanh (env "a" + env "b" * t ^ k) := by
      simp [rubi737r1, eval, Interp.real, hk]
    rw [hfun, hEF]
    have hu : HasDerivAt (fun w => (env "a" + env "b" * w ^ k)) (env "b" * ((k : ℝ) * t ^ (k - 1))) t := by
      simpa using (((hasDerivAt_zpow k t hor).const_mul (env "b")).const_add (env "a"))
    have hA := (hasDerivAt_artanh hd1 hd2).comp t hu
    refine (((hasDerivAt_id t).mul hA).add (hΦ'.const_mul _)).congr_deriv ?_
    have tk := int_mul_zpow_pred t k
    rw [h_n]
    simp only [id, one_mul, Function.comp_def]
    generalize (1 - (env "a" + env "b" * t ^ k) ^ 2)⁻¹ = Q
    linear_combination (env "b" * Q) * tk

theorem rubi731r168_real : rubi731r168.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r168.conditions rubi731r168.body rubi731r168.result rubi731r168.integrals
  intro env hc t hF
  rcases hk : intValue? (env "n") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r168, Defined, eval, Interp.real, hk] at h
  have h_n : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have e2 : intValue? (2 * env "n") = some (2 * k) := (intValue?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hsq : ∀ w : ℝ, w ^ (2 * k) = (w ^ k) ^ 2 := fun w => by rw [mul_comm, zpow_mul]; norm_cast
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r168.body → (k < 0 → w ≠ 0) ∧ -1 < (env "c" * w ^ k) ∧ (env "c" * w ^ k) < 1 := by
    intro w h
    simp [rubi731r168, Defined, eval, Interp.real, hk] at h
    first | exact h | tauto | (trace_state; sorry)
  have hDnz : ∀ w, -1 < (env "c" * w ^ k) → (env "c" * w ^ k) < 1 → (1 - (env "c" * w ^ k) ^ 2) ≠ 0 := by
    intro w h1 h2; nlinarith
  obtain ⟨hw0, hd1, hd2⟩ := hBody t hF.self_of_nhds
  have hor : t ≠ 0 ∨ 0 ≤ k := by
    by_cases h : k < 0
    · exact Or.inl (hw0 h)
    · exact Or.inr (by omega)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r168, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [Defined, eval, Interp.real, hk, e2, i2, im1, hsq]
    have hA1 := hb.1
    have hA2 : 2 * k < 0 → ¬ w = 0 := fun h => hb.1 (by omega)
    have hDw : (1 - (env "c" * w ^ k) ^ 2) ≠ 0 := hDnz w hb.2.1 hb.2.2
    refine ⟨hA1, ?_⟩
    try refine ⟨⟨hA1, hA2⟩, ?_⟩
    try refine ⟨hA2, ?_⟩
    intro h0; apply hDw; linear_combination h0
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi731r168, Defined, eval, recEnv, Interp.real, hk]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi731r168, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t ^ k * (1 - (env "c" * t ^ k) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk, e2, i2, im1, hsq]
      first | ring1 | (left; ring1) | trivial | simp | (trace_state; sorry)
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r168.integrals.map (·.1)) Φ "x" w) rubi731r168.result) =
        fun w => w * Real.artanh (env "c" * w ^ k) + -1 * env "c" * env "n" * Φ "I1" w := by
      funext w; simp [rubi731r168, eval, recEnv, Interp.real, hk]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r168.body = Real.artanh (env "c" * t ^ k) := by
      simp [rubi731r168, eval, Interp.real, hk]
    rw [hfun, hEF]
    have hu : HasDerivAt (fun w => (env "c" * w ^ k)) (env "c" * ((k : ℝ) * t ^ (k - 1))) t := by
      simpa using (((hasDerivAt_zpow k t hor).const_mul (env "c")))
    have hA := (hasDerivAt_artanh hd1 hd2).comp t hu
    refine (((hasDerivAt_id t).mul hA).add (hΦ'.const_mul _)).congr_deriv ?_
    have tk := int_mul_zpow_pred t k
    rw [h_n]
    simp only [id, one_mul, Function.comp_def]
    generalize (1 - (env "c" * t ^ k) ^ 2)⁻¹ = Q
    linear_combination (env "c" * Q) * tk

theorem rubi537r1_real : rubi537r1.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi537r1.conditions rubi537r1.body rubi537r1.result rubi537r1.integrals
  intro env hc t hF
  rcases hk : intValue? (env "n") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi537r1, Defined, eval, Interp.real, hk] at h
  have h_n : env "n" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have e2 : intValue? (2 * env "n") = some (2 * k) := (intValue?_eq _ _).2 (by rw [h_n]; push_cast; ring)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hsq : ∀ w : ℝ, w ^ (2 * k) = (w ^ k) ^ 2 := fun w => by rw [mul_comm, zpow_mul]; norm_cast
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi537r1.body → (k < 0 → w ≠ 0) ∧ True := by
    intro w h
    simp [rubi537r1, Defined, eval, Interp.real, hk] at h
    first | exact h | tauto | (trace_state; sorry)
  have hDnz : ∀ w, (1 + (env "a" + env "b" * w ^ k) ^ 2) ≠ 0 := by
    intro w; positivity
  obtain ⟨hw0, -⟩ := hBody t hF.self_of_nhds
  have hor : t ≠ 0 ∨ 0 ≤ k := by
    by_cases h : k < 0
    · exact Or.inl (hw0 h)
    · exact Or.inr (by omega)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi537r1, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [Defined, eval, Interp.real, hk, e2, i2, im1, hsq]
    have hA1 := hb.1
    have hA2 : 2 * k < 0 → ¬ w = 0 := fun h => hb.1 (by omega)
    have hDw : (1 + (env "a" + env "b" * w ^ k) ^ 2) ≠ 0 := hDnz w
    refine ⟨hA1, ?_⟩
    try refine ⟨⟨hA1, hA2⟩, ?_⟩
    try refine ⟨hA2, ?_⟩
    intro h0; apply hDw; linear_combination h0
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi537r1, Defined, eval, recEnv, Interp.real, hk]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi537r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t ^ k * (1 + (env "a" + env "b" * t ^ k) ^ 2)⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, hk, e2, i2, im1, hsq]
      first | ring1 | (left; ring1) | trivial | simp | (trace_state; sorry)
    have hfun : (fun w => eval Interp.real (recEnv env (rubi537r1.integrals.map (·.1)) Φ "x" w) rubi537r1.result) =
        fun w => w * Real.arctan (env "a" + env "b" * w ^ k) + -1 * env "b" * env "n" * Φ "I1" w := by
      funext w; simp [rubi537r1, eval, recEnv, Interp.real, hk]
    have hEF : eval Interp.real (Function.update env "x" t) rubi537r1.body = Real.arctan (env "a" + env "b" * t ^ k) := by
      simp [rubi537r1, eval, Interp.real, hk]
    rw [hfun, hEF]
    have hu : HasDerivAt (fun w => (env "a" + env "b" * w ^ k)) (env "b" * ((k : ℝ) * t ^ (k - 1))) t := by
      simpa using (((hasDerivAt_zpow k t hor).const_mul (env "b")).const_add (env "a"))
    have hA := (Real.hasDerivAt_arctan' _).comp t hu
    refine (((hasDerivAt_id t).mul hA).add (hΦ'.const_mul _)).congr_deriv ?_
    have tk := int_mul_zpow_pred t k
    rw [h_n]
    simp only [id, one_mul, Function.comp_def]
    generalize (1 + (env "a" + env "b" * t ^ k) ^ 2)⁻¹ = Q
    linear_combination (env "b" * Q) * tk


end OSR.IntegrationRec131
