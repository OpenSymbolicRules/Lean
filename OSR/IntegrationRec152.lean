import OSR.IntegrationRec91

/-!
# Integration (RUBI): integration by parts of `x^m (a + b F(c x))^n`

For `F` = arcsin, arccos, arsinh and arcosh, `d/dx F(c x)` is `± c/√(1 - c² x²)`,
`c/√(1 + c² x²)` and `c/(√(1 + c x) √(c x - 1))`.  An integrand defined on a
neighbourhood keeps `c x` in the open domain, where these derivatives hold.
5.1.1 #1, #2, 5.1.2 #5, #6, 7.1.1 #1, 7.1.2 #3, 7.2.1 #1 and 7.2.2 #3 are proved
over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec152

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 5.1.1 #1 -/
def rubi511r1 : CRule where
  id := "integration.rubi_5_1_1_r1"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n:1"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "n"]
  conditions := [.gt (.var "n") (.int 0)]
  priority := 11841
  description := "RUBI 5.1.1 #1"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n:1" "5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n.m#1"

/-- RUBI 5.1.1 #2 -/
def rubi511r2 : CRule where
  id := "integration.rubi_5_1_1_r2"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n:2"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "n")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "n"]
  conditions := [.gt (.var "n") (.int 0)]
  priority := 11842
  description := "RUBI 5.1.1 #2"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n:2" "5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n.m#2"

/-- RUBI 7.1.1 #1 -/
def rubi711r1 : CRule where
  id := "integration.rubi_7_1_1_r1"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.1 (a+b arcsinh(c x))^n:1"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "n"]
  conditions := [.gt (.var "n") (.int 0)]
  priority := 11843
  description := "RUBI 7.1.1 #1"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.1 (a+b arcsinh(c x))^n:1" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.1 (a+b arcsinh(c x))^n.m#1"

/-- RUBI 7.2.1 #1 -/
def rubi721r1 : CRule where
  id := "integration.rubi_7_2_1_r1"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.1 (a+b arccosh(c x))^n:1"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "n"]
  conditions := [.gt (.var "n") (.int 0)]
  priority := 11844
  description := "RUBI 7.2.1 #1"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.1 (a+b arccosh(c x))^n:1" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.1 (a+b arccosh(c x))^n.m#1"

/-- RUBI 5.1.2 #5 -/
def rubi512r5 : CRule where
  id := "integration.rubi_5_1_2_r5"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .gt (.var "n") (.int 0)]
  priority := 11845
  description := "RUBI 5.1.2 #5"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:5" "5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n.m#5"

/-- RUBI 5.1.2 #6 -/
def rubi512r6 : CRule where
  id := "integration.rubi_5_1_2_r6"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "n")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .gt (.var "n") (.int 0)]
  priority := 11846
  description := "RUBI 5.1.2 #6"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:6" "5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n.m#6"

/-- RUBI 7.1.2 #3 -/
def rubi712r3 : CRule where
  id := "integration.rubi_7_1_2_r3"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b arcsinh(c x))^n:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .gt (.var "n") (.int 0)]
  priority := 11847
  description := "RUBI 7.1.2 #3"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b arcsinh(c x))^n:3" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b arcsinh(c x))^n.m#3"

/-- RUBI 7.2.2 #3 -/
def rubi722r3 : CRule where
  id := "integration.rubi_7_2_2_r3"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.2 (d x)^m (a+b arccosh(c x))^n:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .gt (.var "n") (.int 0)]
  priority := 11848
  description := "RUBI 7.2.2 #3"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.2 (d x)^m (a+b arccosh(c x))^n:3" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.2 (d x)^m (a+b arccosh(c x))^n.m#3"

/-! ## Proofs -/

/-- A neighbourhood on which `c z ∈ [-1, 1]` puts `c w` in `(-1, 1)`. -/
theorem strict_Icc {c w : ℝ} (h : ∀ᶠ z in 𝓝 w, -1 ≤ c * z ∧ c * z ≤ 1) : -1 < c * w ∧ c * w < 1 := by
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.1 h
  have h1 := hb (y := w + ε / 2) (by rw [Real.dist_eq, show w + ε / 2 - w = ε / 2 by ring, abs_of_pos (by linarith)]; linarith)
  have h2 := hb (y := w - ε / 2) (by rw [Real.dist_eq, show w - ε / 2 - w = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]; linarith)
  rcases lt_trichotomy c 0 with hc | hc | hc
  · constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  · subst hc; norm_num
  · constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- A neighbourhood on which `1 ≤ c z` puts `c w` in `(1, ∞)`. -/
theorem strict_Ici {c w : ℝ} (h : ∀ᶠ z in 𝓝 w, 1 ≤ c * z) : 1 < c * w := by
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.1 h
  have h1 := hb (y := w + ε / 2) (by rw [Real.dist_eq, show w + ε / 2 - w = ε / 2 by ring, abs_of_pos (by linarith)]; linarith)
  have h2 := hb (y := w - ε / 2) (by rw [Real.dist_eq, show w - ε / 2 - w = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]; linarith)
  rcases lt_trichotomy c 0 with hc | hc | hc
  · nlinarith
  · subst hc; norm_num at h1
  · nlinarith

theorem rubi511r1_real : rubi511r1.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi511r1.conditions rubi511r1.body rubi511r1.result rubi511r1.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi511r1, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1' : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1'' : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hn0 : 0 < kn := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi511r1])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h; simp [Interp.real] at h; exact_mod_cast h
  have hpt : ∀ z, Defined Interp.real (Function.update env "x" z) rubi511r1.body → -1 ≤ env "c" * z ∧ env "c" * z ≤ 1 := by
    intro z hz; simp [rubi511r1, Defined, eval, Interp.real, hk_n] at hz; tauto
  have hstr : ∀ᶠ w in 𝓝 t, -1 < env "c" * w ∧ env "c" * w < 1 :=
    hF.eventually_nhds.mono fun w hw => strict_Icc (hw.mono fun z hz => hpt z hz)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi511r1, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF, hstr] with w hw hs
    simp [rubi511r1, Defined, eval, Interp.real, i2, im1, hk_n, n1, n1', n1''] at hw ⊢
    have hsq : 0 < 1 + -(env "c" ^ 2 * w ^ 2) := by nlinarith [mul_pos (sub_pos.2 hs.2) (by linarith [hs.1] : (0:ℝ) < 1 + env "c" * w)]
    have hsq' : ¬√(1 + -(env "c" ^ 2 * w ^ 2)) = 0 := (Real.sqrt_pos.2 hsq).ne'
    have hle : env "c" ^ 2 * w ^ 2 ≤ 1 := by linarith
    have k1 : ¬ kn < 1 := by omega
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi511r1, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1''] at hw ⊢
    tauto
  · simp only [rubi511r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi511r1, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1''] at ht hΦ ⊢
    have hs0 := hstr.self_of_nhds
    have hR : √(1 + -(env "c" ^ 2 * t ^ 2)) ≠ 0 := (Real.sqrt_pos.2 (by nlinarith [mul_pos (sub_pos.2 hs0.2) (by linarith [hs0.1] : (0:ℝ) < 1 + env "c" * t)])).ne'
    have hlin : HasDerivAt (fun v : ℝ => env "c" * v) (env "c") t := by simpa using (hasDerivAt_id t).const_mul (env "c")
    have hF' := (Real.hasDerivAt_arcsin (ne_of_gt hs0.1) (ne_of_lt hs0.2)).comp t hlin
    have hA := (hF'.const_mul (env "b")).const_add (env "a")
    have hAn := (hasDerivAt_zpow kn _ (Or.inr hn0.le)).comp t hA
    have hP := (hasDerivAt_id t).mul hAn
    refine HasDerivAt.congr_deriv (by
      first
        | exact hP.add ((hΦ.const_mul _).neg)
        | exact hP.add (hΦ.const_mul _)) ?_
    rw [show (1 : ℝ) - (env "c" * t) ^ 2 = 1 + -(env "c" ^ 2 * t ^ 2) by ring]
    simp only [Function.comp_def, id, one_mul, add_sub_cancel_right]
    rw [hkn]
    push_cast
    field_simp
    ring

theorem rubi511r2_real : rubi511r2.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi511r2.conditions rubi511r2.body rubi511r2.result rubi511r2.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi511r2, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1' : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1'' : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hn0 : 0 < kn := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi511r2])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h; simp [Interp.real] at h; exact_mod_cast h
  have hpt : ∀ z, Defined Interp.real (Function.update env "x" z) rubi511r2.body → -1 ≤ env "c" * z ∧ env "c" * z ≤ 1 := by
    intro z hz; simp [rubi511r2, Defined, eval, Interp.real, hk_n] at hz; tauto
  have hstr : ∀ᶠ w in 𝓝 t, -1 < env "c" * w ∧ env "c" * w < 1 :=
    hF.eventually_nhds.mono fun w hw => strict_Icc (hw.mono fun z hz => hpt z hz)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi511r2, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF, hstr] with w hw hs
    simp [rubi511r2, Defined, eval, Interp.real, i2, im1, hk_n, n1, n1', n1''] at hw ⊢
    have hsq : 0 < 1 + -(env "c" ^ 2 * w ^ 2) := by nlinarith [mul_pos (sub_pos.2 hs.2) (by linarith [hs.1] : (0:ℝ) < 1 + env "c" * w)]
    have hsq' : ¬√(1 + -(env "c" ^ 2 * w ^ 2)) = 0 := (Real.sqrt_pos.2 hsq).ne'
    have hle : env "c" ^ 2 * w ^ 2 ≤ 1 := by linarith
    have k1 : ¬ kn < 1 := by omega
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi511r2, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1''] at hw ⊢
    tauto
  · simp only [rubi511r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi511r2, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1''] at ht hΦ ⊢
    have hs0 := hstr.self_of_nhds
    have hR : √(1 + -(env "c" ^ 2 * t ^ 2)) ≠ 0 := (Real.sqrt_pos.2 (by nlinarith [mul_pos (sub_pos.2 hs0.2) (by linarith [hs0.1] : (0:ℝ) < 1 + env "c" * t)])).ne'
    have hlin : HasDerivAt (fun v : ℝ => env "c" * v) (env "c") t := by simpa using (hasDerivAt_id t).const_mul (env "c")
    have hF' := (Real.hasDerivAt_arccos (ne_of_gt hs0.1) (ne_of_lt hs0.2)).comp t hlin
    have hA := (hF'.const_mul (env "b")).const_add (env "a")
    have hAn := (hasDerivAt_zpow kn _ (Or.inr hn0.le)).comp t hA
    have hP := (hasDerivAt_id t).mul hAn
    refine HasDerivAt.congr_deriv (by
      first
        | exact hP.add ((hΦ.const_mul _).neg)
        | exact hP.add (hΦ.const_mul _)) ?_
    rw [show (1 : ℝ) - (env "c" * t) ^ 2 = 1 + -(env "c" ^ 2 * t ^ 2) by ring]
    simp only [Function.comp_def, id, one_mul, add_sub_cancel_right]
    rw [hkn]
    push_cast
    field_simp
    ring

theorem rubi711r1_real : rubi711r1.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi711r1.conditions rubi711r1.body rubi711r1.result rubi711r1.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi711r1, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1' : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1'' : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hn0 : 0 < kn := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi711r1])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h; simp [Interp.real] at h; exact_mod_cast h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi711r1, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi711r1, Defined, eval, Interp.real, i2, im1, hk_n, n1, n1', n1''] at hw ⊢
    have hsq : 0 < 1 + env "c" ^ 2 * w ^ 2 := by positivity
    have hsq' : ¬√(1 + env "c" ^ 2 * w ^ 2) = 0 := (Real.sqrt_pos.2 hsq).ne'
    have hle : 0 ≤ 1 + env "c" ^ 2 * w ^ 2 := hsq.le
    have k1 : ¬ kn < 1 := by omega
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi711r1, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1''] at hw ⊢
    tauto
  · simp only [rubi711r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi711r1, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1''] at ht hΦ ⊢
    have hR : √(1 + env "c" ^ 2 * t ^ 2) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    have hlin : HasDerivAt (fun v : ℝ => env "c" * v) (env "c") t := by simpa using (hasDerivAt_id t).const_mul (env "c")
    have hF' := (Real.hasDerivAt_arsinh _).comp t hlin
    have hA := (hF'.const_mul (env "b")).const_add (env "a")
    have hAn := (hasDerivAt_zpow kn _ (Or.inr hn0.le)).comp t hA
    have hP := (hasDerivAt_id t).mul hAn
    refine HasDerivAt.congr_deriv (by
      first
        | exact hP.add ((hΦ.const_mul _).neg)
        | exact hP.add (hΦ.const_mul _)) ?_
    rw [mul_pow]
    simp only [Function.comp_def, id, one_mul, add_sub_cancel_right]
    rw [hkn]
    push_cast
    field_simp
    ring

theorem rubi721r1_real : rubi721r1.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi721r1.conditions rubi721r1.body rubi721r1.result rubi721r1.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi721r1, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1' : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1'' : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hn0 : 0 < kn := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi721r1])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h; simp [Interp.real] at h; exact_mod_cast h
  have hpt : ∀ z, Defined Interp.real (Function.update env "x" z) rubi721r1.body → 1 ≤ env "c" * z := by
    intro z hz; simp [rubi721r1, Defined, eval, Interp.real, hk_n] at hz; tauto
  have hstr : ∀ᶠ w in 𝓝 t, 1 < env "c" * w :=
    hF.eventually_nhds.mono fun w hw => strict_Ici (hw.mono fun z hz => hpt z hz)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi721r1, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF, hstr] with w hw hs
    simp [rubi721r1, Defined, eval, Interp.real, i2, im1, hk_n, n1, n1', n1''] at hw ⊢
    have hq1 : ¬√(1 + env "c" * w) = 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have hq2 : ¬√(-1 + env "c" * w) = 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have hle : 0 ≤ 1 + env "c" * w := by linarith
    have hle' : 1 ≤ env "c" * w := hs.le
    have k1 : ¬ kn < 1 := by omega
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi721r1, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1''] at hw ⊢
    tauto
  · simp only [rubi721r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi721r1, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1''] at ht hΦ ⊢
    have hs0 := hstr.self_of_nhds
    have hR1 : √(1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have hR2 : √(-1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have hlin : HasDerivAt (fun v : ℝ => env "c" * v) (env "c") t := by simpa using (hasDerivAt_id t).const_mul (env "c")
    have hF' := (Real.hasDerivAt_arcosh (Set.mem_Ioi.2 hs0)).comp t hlin
    have hA := (hF'.const_mul (env "b")).const_add (env "a")
    have hAn := (hasDerivAt_zpow kn _ (Or.inr hn0.le)).comp t hA
    have hP := (hasDerivAt_id t).mul hAn
    refine HasDerivAt.congr_deriv (by
      first
        | exact hP.add ((hΦ.const_mul _).neg)
        | exact hP.add (hΦ.const_mul _)) ?_
    rw [show (env "c" * t) ^ 2 - 1 = (-1 + env "c" * t) * (1 + env "c" * t) by ring, Real.sqrt_mul (by linarith)]
    simp only [Function.comp_def, id, one_mul, add_sub_cancel_right]
    rw [hkn]
    push_cast
    field_simp
    ring

theorem rubi512r5_real : rubi512r5.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi512r5.conditions rubi512r5.body rubi512r5.result rubi512r5.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi512r5, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1' : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1'' : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hn0 : 0 < kn := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi512r5])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h; simp [Interp.real] at h; exact_mod_cast h
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi512r5, Defined, eval, Interp.real, hk_m] at h
  have hkm : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have m1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [hkm]; push_cast; ring)
  have hm0 : 0 < km := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi512r5])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkm] at h; simp [Interp.real] at h; exact_mod_cast h
  have hpt : ∀ z, Defined Interp.real (Function.update env "x" z) rubi512r5.body → -1 ≤ env "c" * z ∧ env "c" * z ≤ 1 := by
    intro z hz; simp [rubi512r5, Defined, eval, Interp.real, hk_n, hk_m, m1] at hz; tauto
  have hstr : ∀ᶠ w in 𝓝 t, -1 < env "c" * w ∧ env "c" * w < 1 :=
    hF.eventually_nhds.mono fun w hw => strict_Icc (hw.mono fun z hz => hpt z hz)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi512r5, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF, hstr] with w hw hs
    simp [rubi512r5, Defined, eval, Interp.real, i2, im1, hk_n, n1, n1', n1'', hk_m, m1] at hw ⊢
    have hsq : 0 < 1 + -(env "c" ^ 2 * w ^ 2) := by nlinarith [mul_pos (sub_pos.2 hs.2) (by linarith [hs.1] : (0:ℝ) < 1 + env "c" * w)]
    have hsq' : ¬√(1 + -(env "c" ^ 2 * w ^ 2)) = 0 := (Real.sqrt_pos.2 hsq).ne'
    have hle : env "c" ^ 2 * w ^ 2 ≤ 1 := by linarith
    have k1 : ¬ kn < 1 := by omega
    have k2 : ¬ km + 1 < 0 := by omega
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi512r5, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1'', hk_m, m1] at hw ⊢
    have hm1 : ¬ env "m" + 1 = 0 := by rw [hkm]; norm_cast; omega
    have k2 : ¬ km + 1 < 0 := by omega
    tauto
  · simp only [rubi512r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi512r5, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1'', hk_m, m1] at ht hΦ ⊢
    have hs0 := hstr.self_of_nhds
    have hR : √(1 + -(env "c" ^ 2 * t ^ 2)) ≠ 0 := (Real.sqrt_pos.2 (by nlinarith [mul_pos (sub_pos.2 hs0.2) (by linarith [hs0.1] : (0:ℝ) < 1 + env "c" * t)])).ne'
    have hlin : HasDerivAt (fun v : ℝ => env "c" * v) (env "c") t := by simpa using (hasDerivAt_id t).const_mul (env "c")
    have hF' := (Real.hasDerivAt_arcsin (ne_of_gt hs0.1) (ne_of_lt hs0.2)).comp t hlin
    have hA := (hF'.const_mul (env "b")).const_add (env "a")
    have hAn := (hasDerivAt_zpow kn _ (Or.inr hn0.le)).comp t hA
    have hX := hasDerivAt_zpow (km + 1) t (Or.inr (by omega))
    have hP := (hX.mul hAn).mul_const (env "m" + 1)⁻¹
    refine HasDerivAt.congr_deriv (by
      first
        | exact hP.add ((hΦ.const_mul _).neg)
        | exact hP.add (hΦ.const_mul _)) ?_
    rw [show (1 : ℝ) - (env "c" * t) ^ 2 = 1 + -(env "c" ^ 2 * t ^ 2) by ring]
    simp only [Function.comp_def, id, one_mul, add_sub_cancel_right]
    rw [hkn]
    rw [hkm]
    have hm1 : (km : ℝ) + 1 ≠ 0 := by norm_cast; omega
    push_cast
    field_simp
    ring

theorem rubi512r6_real : rubi512r6.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi512r6.conditions rubi512r6.body rubi512r6.result rubi512r6.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi512r6, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1' : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1'' : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hn0 : 0 < kn := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi512r6])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h; simp [Interp.real] at h; exact_mod_cast h
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi512r6, Defined, eval, Interp.real, hk_m] at h
  have hkm : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have m1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [hkm]; push_cast; ring)
  have hm0 : 0 < km := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi512r6])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkm] at h; simp [Interp.real] at h; exact_mod_cast h
  have hpt : ∀ z, Defined Interp.real (Function.update env "x" z) rubi512r6.body → -1 ≤ env "c" * z ∧ env "c" * z ≤ 1 := by
    intro z hz; simp [rubi512r6, Defined, eval, Interp.real, hk_n, hk_m, m1] at hz; tauto
  have hstr : ∀ᶠ w in 𝓝 t, -1 < env "c" * w ∧ env "c" * w < 1 :=
    hF.eventually_nhds.mono fun w hw => strict_Icc (hw.mono fun z hz => hpt z hz)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi512r6, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF, hstr] with w hw hs
    simp [rubi512r6, Defined, eval, Interp.real, i2, im1, hk_n, n1, n1', n1'', hk_m, m1] at hw ⊢
    have hsq : 0 < 1 + -(env "c" ^ 2 * w ^ 2) := by nlinarith [mul_pos (sub_pos.2 hs.2) (by linarith [hs.1] : (0:ℝ) < 1 + env "c" * w)]
    have hsq' : ¬√(1 + -(env "c" ^ 2 * w ^ 2)) = 0 := (Real.sqrt_pos.2 hsq).ne'
    have hle : env "c" ^ 2 * w ^ 2 ≤ 1 := by linarith
    have k1 : ¬ kn < 1 := by omega
    have k2 : ¬ km + 1 < 0 := by omega
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi512r6, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1'', hk_m, m1] at hw ⊢
    have hm1 : ¬ env "m" + 1 = 0 := by rw [hkm]; norm_cast; omega
    have k2 : ¬ km + 1 < 0 := by omega
    tauto
  · simp only [rubi512r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi512r6, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1'', hk_m, m1] at ht hΦ ⊢
    have hs0 := hstr.self_of_nhds
    have hR : √(1 + -(env "c" ^ 2 * t ^ 2)) ≠ 0 := (Real.sqrt_pos.2 (by nlinarith [mul_pos (sub_pos.2 hs0.2) (by linarith [hs0.1] : (0:ℝ) < 1 + env "c" * t)])).ne'
    have hlin : HasDerivAt (fun v : ℝ => env "c" * v) (env "c") t := by simpa using (hasDerivAt_id t).const_mul (env "c")
    have hF' := (Real.hasDerivAt_arccos (ne_of_gt hs0.1) (ne_of_lt hs0.2)).comp t hlin
    have hA := (hF'.const_mul (env "b")).const_add (env "a")
    have hAn := (hasDerivAt_zpow kn _ (Or.inr hn0.le)).comp t hA
    have hX := hasDerivAt_zpow (km + 1) t (Or.inr (by omega))
    have hP := (hX.mul hAn).mul_const (env "m" + 1)⁻¹
    refine HasDerivAt.congr_deriv (by
      first
        | exact hP.add ((hΦ.const_mul _).neg)
        | exact hP.add (hΦ.const_mul _)) ?_
    rw [show (1 : ℝ) - (env "c" * t) ^ 2 = 1 + -(env "c" ^ 2 * t ^ 2) by ring]
    simp only [Function.comp_def, id, one_mul, add_sub_cancel_right]
    rw [hkn]
    rw [hkm]
    have hm1 : (km : ℝ) + 1 ≠ 0 := by norm_cast; omega
    push_cast
    field_simp
    ring

theorem rubi712r3_real : rubi712r3.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi712r3.conditions rubi712r3.body rubi712r3.result rubi712r3.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi712r3, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1' : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1'' : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hn0 : 0 < kn := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi712r3])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h; simp [Interp.real] at h; exact_mod_cast h
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi712r3, Defined, eval, Interp.real, hk_m] at h
  have hkm : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have m1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [hkm]; push_cast; ring)
  have hm0 : 0 < km := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi712r3])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkm] at h; simp [Interp.real] at h; exact_mod_cast h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi712r3, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi712r3, Defined, eval, Interp.real, i2, im1, hk_n, n1, n1', n1'', hk_m, m1] at hw ⊢
    have hsq : 0 < 1 + env "c" ^ 2 * w ^ 2 := by positivity
    have hsq' : ¬√(1 + env "c" ^ 2 * w ^ 2) = 0 := (Real.sqrt_pos.2 hsq).ne'
    have hle : 0 ≤ 1 + env "c" ^ 2 * w ^ 2 := hsq.le
    have k1 : ¬ kn < 1 := by omega
    have k2 : ¬ km + 1 < 0 := by omega
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi712r3, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1'', hk_m, m1] at hw ⊢
    have hm1 : ¬ env "m" + 1 = 0 := by rw [hkm]; norm_cast; omega
    have k2 : ¬ km + 1 < 0 := by omega
    tauto
  · simp only [rubi712r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi712r3, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1'', hk_m, m1] at ht hΦ ⊢
    have hR : √(1 + env "c" ^ 2 * t ^ 2) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    have hlin : HasDerivAt (fun v : ℝ => env "c" * v) (env "c") t := by simpa using (hasDerivAt_id t).const_mul (env "c")
    have hF' := (Real.hasDerivAt_arsinh _).comp t hlin
    have hA := (hF'.const_mul (env "b")).const_add (env "a")
    have hAn := (hasDerivAt_zpow kn _ (Or.inr hn0.le)).comp t hA
    have hX := hasDerivAt_zpow (km + 1) t (Or.inr (by omega))
    have hP := (hX.mul hAn).mul_const (env "m" + 1)⁻¹
    refine HasDerivAt.congr_deriv (by
      first
        | exact hP.add ((hΦ.const_mul _).neg)
        | exact hP.add (hΦ.const_mul _)) ?_
    rw [mul_pow]
    simp only [Function.comp_def, id, one_mul, add_sub_cancel_right]
    rw [hkn]
    rw [hkm]
    have hm1 : (km : ℝ) + 1 ≠ 0 := by norm_cast; omega
    push_cast
    field_simp
    ring

theorem rubi722r3_real : rubi722r3.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi722r3.conditions rubi722r3.body rubi722r3.result rubi722r3.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi722r3, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1' : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n1'' : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hn0 : 0 < kn := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi722r3])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h; simp [Interp.real] at h; exact_mod_cast h
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi722r3, Defined, eval, Interp.real, hk_m] at h
  have hkm : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have m1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [hkm]; push_cast; ring)
  have hm0 : 0 < km := by
    have h := hc (.gt (.var "m") (.int 0)) (by simp [rubi722r3])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkm] at h; simp [Interp.real] at h; exact_mod_cast h
  have hpt : ∀ z, Defined Interp.real (Function.update env "x" z) rubi722r3.body → 1 ≤ env "c" * z := by
    intro z hz; simp [rubi722r3, Defined, eval, Interp.real, hk_n, hk_m, m1] at hz; tauto
  have hstr : ∀ᶠ w in 𝓝 t, 1 < env "c" * w :=
    hF.eventually_nhds.mono fun w hw => strict_Ici (hw.mono fun z hz => hpt z hz)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi722r3, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF, hstr] with w hw hs
    simp [rubi722r3, Defined, eval, Interp.real, i2, im1, hk_n, n1, n1', n1'', hk_m, m1] at hw ⊢
    have hq1 : ¬√(1 + env "c" * w) = 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have hq2 : ¬√(-1 + env "c" * w) = 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have hle : 0 ≤ 1 + env "c" * w := by linarith
    have hle' : 1 ≤ env "c" * w := hs.le
    have k1 : ¬ kn < 1 := by omega
    have k2 : ¬ km + 1 < 0 := by omega
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi722r3, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1'', hk_m, m1] at hw ⊢
    have hm1 : ¬ env "m" + 1 = 0 := by rw [hkm]; norm_cast; omega
    have k2 : ¬ km + 1 < 0 := by omega
    tauto
  · simp only [rubi722r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi722r3, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n1', n1'', hk_m, m1] at ht hΦ ⊢
    have hs0 := hstr.self_of_nhds
    have hR1 : √(1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have hR2 : √(-1 + env "c" * t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have hlin : HasDerivAt (fun v : ℝ => env "c" * v) (env "c") t := by simpa using (hasDerivAt_id t).const_mul (env "c")
    have hF' := (Real.hasDerivAt_arcosh (Set.mem_Ioi.2 hs0)).comp t hlin
    have hA := (hF'.const_mul (env "b")).const_add (env "a")
    have hAn := (hasDerivAt_zpow kn _ (Or.inr hn0.le)).comp t hA
    have hX := hasDerivAt_zpow (km + 1) t (Or.inr (by omega))
    have hP := (hX.mul hAn).mul_const (env "m" + 1)⁻¹
    refine HasDerivAt.congr_deriv (by
      first
        | exact hP.add ((hΦ.const_mul _).neg)
        | exact hP.add (hΦ.const_mul _)) ?_
    rw [show (env "c" * t) ^ 2 - 1 = (-1 + env "c" * t) * (1 + env "c" * t) by ring, Real.sqrt_mul (by linarith)]
    simp only [Function.comp_def, id, one_mul, add_sub_cancel_right]
    rw [hkn]
    rw [hkm]
    have hm1 : (km : ℝ) + 1 ≠ 0 := by norm_cast; omega
    push_cast
    field_simp
    ring

end OSR.IntegrationRec152
