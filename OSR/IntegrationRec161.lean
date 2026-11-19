import OSR.IntegrationRec91

/-!
# Integration (RUBI): more integrations by parts

6.1.12 #27, #28 (`(e x)^m sinh(c + d xⁿ)`, `(e x)^m cosh(c + d xⁿ)`),
4.1.12 #41, #42 (`x^m sin^p(a + b xⁿ)` with `m + n = 0`), 5.3.5 #7
(`(e + f x)^m (a + b arctan(c + d x))^p`) and 3.3 #9 integrate by parts.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec161

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 5.3.5 #7 -/
def rubi535r7 : CRule where
  id := "integration.rubi_5_3_5_r7"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.5 u (a+b arctan(c+d x))^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "p"))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "p")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.int 1) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .int (.var "m"),
    .gt (.int (-1)) (.var "m")]
  priority := 11891
  description := "RUBI 5.3.5 #7"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.5 u (a+b arctan(c+d x))^p:7" "5 Inverse trig functions/5.3 Inverse tangent/5.3.5 u (a+b arctan(c+d x))^p.m#7"

/-- RUBI 6.1.12 #27 -/
def rubi6112r27 : CRule where
  id := "integration.rubi_6_1_12_r27"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "n")) (.pow (.app2 .mul (.pow (.var "e") (.var "n")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 11892
  description := "RUBI 6.1.12 #27"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:27" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#27"

/-- RUBI 6.1.12 #28 -/
def rubi6112r28 : CRule where
  id := "integration.rubi_6_1_12_r28"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:28"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "n")) (.pow (.app2 .mul (.pow (.var "e") (.var "n")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 11893
  description := "RUBI 6.1.12 #28"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:28" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#28"

/-- RUBI 4.1.12 #41 -/
def rubi4112r41 : CRule where
  id := "integration.rubi_4_1_12_r41"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:41"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 1),
    .eq (.app2 .add (.var "m") (.var "n")) (.int 0),
    .ne (.var "n") (.int 1),
    .int (.var "n")]
  priority := 11894
  description := "RUBI 4.1.12 #41"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:41" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#41"

/-- RUBI 4.1.12 #42 -/
def rubi4112r42 : CRule where
  id := "integration.rubi_4_1_12_r42"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:42"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 1),
    .eq (.app2 .add (.var "m") (.var "n")) (.int 0),
    .ne (.var "n") (.int 1),
    .int (.var "n")]
  priority := 11895
  description := "RUBI 4.1.12 #42"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:42" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#42"

/-- RUBI 3.3 #9 -/
def rubi33r9 : CRule where
  id := "integration.rubi_3_3_r9"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p")) (.pow (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.var "p")) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int 0),
    .gt (.var "p") (.int 0)]
  priority := 11896
  description := "RUBI 3.3 #9"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:9" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#9"

/-! ## Proofs -/

theorem rubi6112r27_real : rubi6112r27.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6112r27.conditions rubi6112r27.body rubi6112r27.result rubi6112r27.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi6112r27, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi6112r27, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkm : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have m1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [hkm]; push_cast; ring)
  have mn : intValue? (env "m" + env "n") = some (km + kn) := (intValue?_eq _ _).2 (by rw [hkm, hkn]; push_cast; ring)
  have hn0 : 0 < kn := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi6112r27])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h; simp [Interp.real] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hm1 : km < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi6112r27])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkm] at h; simp [Interp.real] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hpt : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6112r27.body → env "e" * w ≠ 0 := by
    intro w hw; simp [rubi6112r27, Defined, eval, Interp.real, hk_m, hk_n] at hw
    have hneg : km < 0 := by omega
    simp only [ne_eq, mul_eq_zero, not_or]; tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r27, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h0 := hpt w hw
    simp [rubi6112r27, Defined, eval, Interp.real, hk_m, hk_n, mn] at hw ⊢
    have he : env "e" ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have hw0 : w ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    tauto
  · filter_upwards [hF] with w hw
    have h0 := hpt w hw
    simp [rubi6112r27, Defined, eval, recEnv, Interp.real, hk_m, hk_n, m1, im1] at hw ⊢
    have hm : env "m" + 1 ≠ 0 := by rw [hkm]; norm_cast; omega
    have he : env "e" ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have hEk : env "e" ^ kn ≠ 0 := zpow_ne_zero _ he
    first | tauto | simp_all | (trace_state; sorry)
  · simp only [rubi6112r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have h0 := hpt t hF.self_of_nhds
    have he : env "e" ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have ht0 : t ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    simp [rubi6112r27, eval, Interp.real, hk_m, hk_n, mn] at hΦ
    have hlin : HasDerivAt (fun v : ℝ => env "e" * v) (env "e") t := by
      simpa using (hasDerivAt_id t).const_mul (env "e")
    have hX := (hasDerivAt_zpow (km + 1) (env "e" * t) (Or.inl h0)).comp t hlin
    have hu := ((hasDerivAt_zpow kn t (Or.inr hn0.le)).const_mul (env "d")).const_add (env "c")
    have hS := (Real.hasDerivAt_sinh _).comp t hu
    have hF0 := ((hX.mul hS).mul_const (env "e" * (env "m" + 1))⁻¹).add
      (hΦ.const_mul (-(env "d" * env "n") * (env "e" ^ kn * (env "m" + 1))⁻¹))
    convert hF0 using 1
    · funext v; simp [rubi6112r27, eval, recEnv, Interp.real, hk_m, hk_n, m1, mn, im1, Function.comp_def]; try ring
    · simp [rubi6112r27, eval, Interp.real, hk_m, hk_n, Function.comp_def]
      rw [hkm, hkn]
      have hm : (km : ℝ) + 1 ≠ 0 := by norm_cast; omega
      have hP : (env "e" * t) ^ km ≠ 0 := zpow_ne_zero _ h0
      rw [show (env "e" * t) ^ (km + kn) = (env "e" * t) ^ km * (env "e" ^ kn * t ^ kn) by rw [zpow_add₀ h0, mul_zpow (env "e") t kn]]
      rw [show (env "e" * t) ^ (km + 1) = (env "e" * t) ^ km * (env "e" * t) from zpow_add_one₀ h0 _]
      rw [zpow_sub_one₀ ht0]
      push_cast
      generalize (env "e" * t) ^ km = P at *
      generalize Real.sinh (env "c" + env "d" * t ^ kn) = S
      generalize Real.cosh (env "c" + env "d" * t ^ kn) = C
      have hE : env "e" ^ kn ≠ 0 := zpow_ne_zero _ he
      have hT : t ^ kn ≠ 0 := zpow_ne_zero _ ht0
      field_simp
      ring

theorem rubi6112r27_complex : rubi6112r27.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6112r27.conditions rubi6112r27.body rubi6112r27.result rubi6112r27.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi6112r27, Defined, eval, Interp.complex, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi6112r27, Defined, eval, Interp.complex, hk_m, hk_n] at h
  have hkm : env "m" = (km : ℂ) := (intValue?_eq _ _).1 hk_m
  have hkn : env "n" = (kn : ℂ) := (intValue?_eq _ _).1 hk_n
  have m1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [hkm]; push_cast; ring)
  have mn : intValue? (env "m" + env "n") = some (km + kn) := (intValue?_eq _ _).2 (by rw [hkm, hkn]; push_cast; ring)
  have hn0 : 0 < kn := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi6112r27])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h; simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hm1 : km < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi6112r27])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkm] at h; simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hpt : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi6112r27.body → env "e" * w ≠ 0 := by
    intro w hw; simp [rubi6112r27, Defined, eval, Interp.complex, hk_m, hk_n] at hw
    have hneg : km < 0 := by omega
    simp only [ne_eq, mul_eq_zero, not_or]; tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r27, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h0 := hpt w hw
    simp [rubi6112r27, Defined, eval, Interp.complex, hk_m, hk_n, mn] at hw ⊢
    have he : env "e" ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have hw0 : w ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    tauto
  · filter_upwards [hF] with w hw
    have h0 := hpt w hw
    simp [rubi6112r27, Defined, eval, recEnv, Interp.complex, hk_m, hk_n, m1, im1] at hw ⊢
    have hm : env "m" + 1 ≠ 0 := by rw [hkm]; norm_cast; omega
    have he : env "e" ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have hEk : env "e" ^ kn ≠ 0 := zpow_ne_zero _ he
    first | tauto | simp_all | (trace_state; sorry)
  · simp only [rubi6112r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have h0 := hpt t hF.self_of_nhds
    have he : env "e" ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have ht0 : t ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    simp [rubi6112r27, eval, Interp.complex, hk_m, hk_n, mn] at hΦ
    have hlin : HasDerivAt (fun v : ℂ => env "e" * v) (env "e") t := by
      simpa using (hasDerivAt_id t).const_mul (env "e")
    have hX := (hasDerivAt_zpow (km + 1) (env "e" * t) (Or.inl h0)).comp t hlin
    have hu := ((hasDerivAt_zpow kn t (Or.inr hn0.le)).const_mul (env "d")).const_add (env "c")
    have hS := (Complex.hasDerivAt_sinh _).comp t hu
    have hF0 := ((hX.mul hS).mul_const (env "e" * (env "m" + 1))⁻¹).add
      (hΦ.const_mul (-(env "d" * env "n") * (env "e" ^ kn * (env "m" + 1))⁻¹))
    convert hF0 using 1
    · funext v; simp [rubi6112r27, eval, recEnv, Interp.complex, hk_m, hk_n, m1, mn, im1, Function.comp_def]; try ring
    · simp [rubi6112r27, eval, Interp.complex, hk_m, hk_n, Function.comp_def]
      rw [hkm, hkn]
      have hm : (km : ℂ) + 1 ≠ 0 := by norm_cast; omega
      have hP : (env "e" * t) ^ km ≠ 0 := zpow_ne_zero _ h0
      rw [show (env "e" * t) ^ (km + kn) = (env "e" * t) ^ km * (env "e" ^ kn * t ^ kn) by rw [zpow_add₀ h0, mul_zpow (env "e") t kn]]
      rw [show (env "e" * t) ^ (km + 1) = (env "e" * t) ^ km * (env "e" * t) from zpow_add_one₀ h0 _]
      rw [zpow_sub_one₀ ht0]
      push_cast
      generalize (env "e" * t) ^ km = P at *
      generalize Complex.sinh (env "c" + env "d" * t ^ kn) = S
      generalize Complex.cosh (env "c" + env "d" * t ^ kn) = C
      have hE : env "e" ^ kn ≠ 0 := zpow_ne_zero _ he
      have hT : t ^ kn ≠ 0 := zpow_ne_zero _ ht0
      field_simp
      ring

theorem rubi6112r28_real : rubi6112r28.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6112r28.conditions rubi6112r28.body rubi6112r28.result rubi6112r28.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi6112r28, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi6112r28, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkm : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have m1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [hkm]; push_cast; ring)
  have mn : intValue? (env "m" + env "n") = some (km + kn) := (intValue?_eq _ _).2 (by rw [hkm, hkn]; push_cast; ring)
  have hn0 : 0 < kn := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi6112r28])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h; simp [Interp.real] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hm1 : km < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi6112r28])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkm] at h; simp [Interp.real] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hpt : ∀ w, Defined Interp.real (Function.update env "x" w) rubi6112r28.body → env "e" * w ≠ 0 := by
    intro w hw; simp [rubi6112r28, Defined, eval, Interp.real, hk_m, hk_n] at hw
    have hneg : km < 0 := by omega
    simp only [ne_eq, mul_eq_zero, not_or]; tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r28, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h0 := hpt w hw
    simp [rubi6112r28, Defined, eval, Interp.real, hk_m, hk_n, mn] at hw ⊢
    have he : env "e" ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have hw0 : w ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    tauto
  · filter_upwards [hF] with w hw
    have h0 := hpt w hw
    simp [rubi6112r28, Defined, eval, recEnv, Interp.real, hk_m, hk_n, m1, im1] at hw ⊢
    have hm : env "m" + 1 ≠ 0 := by rw [hkm]; norm_cast; omega
    have he : env "e" ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have hEk : env "e" ^ kn ≠ 0 := zpow_ne_zero _ he
    first | tauto | simp_all | (trace_state; sorry)
  · simp only [rubi6112r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have h0 := hpt t hF.self_of_nhds
    have he : env "e" ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have ht0 : t ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    simp [rubi6112r28, eval, Interp.real, hk_m, hk_n, mn] at hΦ
    have hlin : HasDerivAt (fun v : ℝ => env "e" * v) (env "e") t := by
      simpa using (hasDerivAt_id t).const_mul (env "e")
    have hX := (hasDerivAt_zpow (km + 1) (env "e" * t) (Or.inl h0)).comp t hlin
    have hu := ((hasDerivAt_zpow kn t (Or.inr hn0.le)).const_mul (env "d")).const_add (env "c")
    have hS := (Real.hasDerivAt_cosh _).comp t hu
    have hF0 := ((hX.mul hS).mul_const (env "e" * (env "m" + 1))⁻¹).add
      (hΦ.const_mul (-(env "d" * env "n") * (env "e" ^ kn * (env "m" + 1))⁻¹))
    convert hF0 using 1
    · funext v; simp [rubi6112r28, eval, recEnv, Interp.real, hk_m, hk_n, m1, mn, im1, Function.comp_def]; try ring
    · simp [rubi6112r28, eval, Interp.real, hk_m, hk_n, Function.comp_def]
      rw [hkm, hkn]
      have hm : (km : ℝ) + 1 ≠ 0 := by norm_cast; omega
      have hP : (env "e" * t) ^ km ≠ 0 := zpow_ne_zero _ h0
      rw [show (env "e" * t) ^ (km + kn) = (env "e" * t) ^ km * (env "e" ^ kn * t ^ kn) by rw [zpow_add₀ h0, mul_zpow (env "e") t kn]]
      rw [show (env "e" * t) ^ (km + 1) = (env "e" * t) ^ km * (env "e" * t) from zpow_add_one₀ h0 _]
      rw [zpow_sub_one₀ ht0]
      push_cast
      generalize (env "e" * t) ^ km = P at *
      generalize Real.cosh (env "c" + env "d" * t ^ kn) = S
      generalize Real.sinh (env "c" + env "d" * t ^ kn) = C
      have hE : env "e" ^ kn ≠ 0 := zpow_ne_zero _ he
      have hT : t ^ kn ≠ 0 := zpow_ne_zero _ ht0
      field_simp
      ring

theorem rubi6112r28_complex : rubi6112r28.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6112r28.conditions rubi6112r28.body rubi6112r28.result rubi6112r28.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi6112r28, Defined, eval, Interp.complex, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi6112r28, Defined, eval, Interp.complex, hk_m, hk_n] at h
  have hkm : env "m" = (km : ℂ) := (intValue?_eq _ _).1 hk_m
  have hkn : env "n" = (kn : ℂ) := (intValue?_eq _ _).1 hk_n
  have m1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [hkm]; push_cast; ring)
  have mn : intValue? (env "m" + env "n") = some (km + kn) := (intValue?_eq _ _).2 (by rw [hkm, hkn]; push_cast; ring)
  have hn0 : 0 < kn := by
    have h := hc (.gt (.var "n") (.int 0)) (by simp [rubi6112r28])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h; simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hm1 : km < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi6112r28])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkm] at h; simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hpt : ∀ w, Defined Interp.complex (Function.update env "x" w) rubi6112r28.body → env "e" * w ≠ 0 := by
    intro w hw; simp [rubi6112r28, Defined, eval, Interp.complex, hk_m, hk_n] at hw
    have hneg : km < 0 := by omega
    simp only [ne_eq, mul_eq_zero, not_or]; tauto
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r28, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h0 := hpt w hw
    simp [rubi6112r28, Defined, eval, Interp.complex, hk_m, hk_n, mn] at hw ⊢
    have he : env "e" ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have hw0 : w ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    tauto
  · filter_upwards [hF] with w hw
    have h0 := hpt w hw
    simp [rubi6112r28, Defined, eval, recEnv, Interp.complex, hk_m, hk_n, m1, im1] at hw ⊢
    have hm : env "m" + 1 ≠ 0 := by rw [hkm]; norm_cast; omega
    have he : env "e" ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have hEk : env "e" ^ kn ≠ 0 := zpow_ne_zero _ he
    first | tauto | simp_all | (trace_state; sorry)
  · simp only [rubi6112r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have h0 := hpt t hF.self_of_nhds
    have he : env "e" ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have ht0 : t ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    simp [rubi6112r28, eval, Interp.complex, hk_m, hk_n, mn] at hΦ
    have hlin : HasDerivAt (fun v : ℂ => env "e" * v) (env "e") t := by
      simpa using (hasDerivAt_id t).const_mul (env "e")
    have hX := (hasDerivAt_zpow (km + 1) (env "e" * t) (Or.inl h0)).comp t hlin
    have hu := ((hasDerivAt_zpow kn t (Or.inr hn0.le)).const_mul (env "d")).const_add (env "c")
    have hS := (Complex.hasDerivAt_cosh _).comp t hu
    have hF0 := ((hX.mul hS).mul_const (env "e" * (env "m" + 1))⁻¹).add
      (hΦ.const_mul (-(env "d" * env "n") * (env "e" ^ kn * (env "m" + 1))⁻¹))
    convert hF0 using 1
    · funext v; simp [rubi6112r28, eval, recEnv, Interp.complex, hk_m, hk_n, m1, mn, im1, Function.comp_def]; try ring
    · simp [rubi6112r28, eval, Interp.complex, hk_m, hk_n, Function.comp_def]
      rw [hkm, hkn]
      have hm : (km : ℂ) + 1 ≠ 0 := by norm_cast; omega
      have hP : (env "e" * t) ^ km ≠ 0 := zpow_ne_zero _ h0
      rw [show (env "e" * t) ^ (km + kn) = (env "e" * t) ^ km * (env "e" ^ kn * t ^ kn) by rw [zpow_add₀ h0, mul_zpow (env "e") t kn]]
      rw [show (env "e" * t) ^ (km + 1) = (env "e" * t) ^ km * (env "e" * t) from zpow_add_one₀ h0 _]
      rw [zpow_sub_one₀ ht0]
      push_cast
      generalize (env "e" * t) ^ km = P at *
      generalize Complex.cosh (env "c" + env "d" * t ^ kn) = S
      generalize Complex.sinh (env "c" + env "d" * t ^ kn) = C
      have hE : env "e" ^ kn ≠ 0 := zpow_ne_zero _ he
      have hT : t ^ kn ≠ 0 := zpow_ne_zero _ ht0
      field_simp
      ring

theorem rubi4112r41_real : rubi4112r41.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4112r41.conditions rubi4112r41.body rubi4112r41.result rubi4112r41.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r41, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r41, Defined, eval, Interp.real, hk_m, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r41, Defined, eval, Interp.real, hk_m, hk_n, hk_p] at h
  have hkm : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have m1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [hkm]; push_cast; ring)
  have p1 : intValue? (env "p" + -1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p1' : intValue? (env "p" + -1 * 1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp1 : 1 < kp := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi4112r41])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkp] at h; simp [Interp.real] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hmn : km + kn = 0 := by
    have h := hc (.eq (.app2 .add (.var "m") (.var "n")) (.int 0)) (by simp [rubi4112r41])
    simp [Cond.Holds, Defined, eval, hkm, hkn] at h
    exact_mod_cast (show ((km + kn : ℤ) : ℝ) = 0 by push_cast; linear_combination h)
  have hn1 : kn ≠ 1 := by
    have h := hc (.ne (.var "n") (.int 1)) (by simp [rubi4112r41])
    simp [Cond.Holds, Defined, eval, hkn] at h
    intro h1; apply h; simp [h1]
  have hm1 : (km : ℝ) + 1 ≠ 0 := by norm_cast; omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r41, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi4112r41, Defined, eval, Interp.real, hk_m, hk_n, hk_p, p1, p1'] at hw ⊢
    have : ¬ kp - 1 < 0 := by omega
    have : ¬ kp < 1 := by omega
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi4112r41, Defined, eval, recEnv, Interp.real, hk_m, hk_n, hk_p, m1, im1] at hw ⊢
    have : ¬ km + 1 < 0 → True := fun _ => trivial
    have hm' : ¬ env "m" + 1 = 0 := by rw [hkm]; exact hm1
    exact ⟨⟨fun h => hw.1 (by omega), hw.2⟩, hm'⟩
  · simp only [rubi4112r41, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi4112r41, Defined, eval, Interp.real, hk_m, hk_n, hk_p] at ht
    simp [rubi4112r41, eval, Interp.real, hk_m, hk_n, hk_p, p1, p1'] at hΦ
    have hor : t ≠ 0 ∨ kn = 0 := by
      rcases eq_or_ne t 0 with h | h
      · right; by_contra hk
        rcases lt_or_gt_of_ne hk with hk | hk
        · exact (ht.2.1 hk) h
        · exact (ht.1 (by omega)) h
      · exact Or.inl h
    have hkey : (kn : ℝ) * (t ^ (km + 1) * t ^ (kn - 1)) = kn := by
      rcases hor with h | h
      · rw [← zpow_add₀ h, show km + 1 + (kn - 1) = 0 by omega, zpow_zero, mul_one]
      · subst h; simp
    have hX := hasDerivAt_zpow (km + 1) t (by rcases hor with h | h; exact Or.inl h; exact Or.inr (by omega))
    have hu := ((hasDerivAt_zpow kn t (by rcases hor with h | h; exact Or.inl h; exact Or.inr (by omega))).const_mul (env "b")).const_add (env "a")
    have hSp := (hasDerivAt_zpow kp _ (Or.inr (by omega))).comp t ((Real.hasDerivAt_sin _).comp t hu)
    have hF0 := ((hX.mul hSp).mul_const (env "m" + 1)⁻¹).add
      (hΦ.const_mul (-(env "b" * env "n" * env "p") * (env "m" + 1)⁻¹))
    convert hF0 using 1
    · funext v; simp [rubi4112r41, eval, recEnv, Interp.real, hk_m, hk_n, hk_p, m1, p1, p1', im1, Function.comp_def]; try ring
    · simp [rubi4112r41, eval, Interp.real, hk_m, hk_n, hk_p, Function.comp_def]
      rw [hkm, hkn, hkp]
      generalize Real.sin (env "a" + env "b" * t ^ kn) ^ (kp - 1) = Q
      generalize Real.sin (env "a" + env "b" * t ^ kn) ^ kp = P
      generalize Real.cos (env "a" + env "b" * t ^ kn) = C
      generalize Real.sin (env "a" + env "b" * t ^ kn) = S
      field_simp
      linear_combination (-((kp : _) * Q * C * env "b")) * hkey

theorem rubi4112r41_complex : rubi4112r41.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4112r41.conditions rubi4112r41.body rubi4112r41.result rubi4112r41.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r41, Defined, eval, Interp.complex, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r41, Defined, eval, Interp.complex, hk_m, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r41, Defined, eval, Interp.complex, hk_m, hk_n, hk_p] at h
  have hkm : env "m" = (km : ℂ) := (intValue?_eq _ _).1 hk_m
  have hkn : env "n" = (kn : ℂ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℂ) := (intValue?_eq _ _).1 hk_p
  have m1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [hkm]; push_cast; ring)
  have p1 : intValue? (env "p" + -1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p1' : intValue? (env "p" + -1 * 1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp1 : 1 < kp := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi4112r41])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkp] at h; simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hmn : km + kn = 0 := by
    have h := hc (.eq (.app2 .add (.var "m") (.var "n")) (.int 0)) (by simp [rubi4112r41])
    simp [Cond.Holds, Defined, eval, hkm, hkn] at h
    exact_mod_cast (show ((km + kn : ℤ) : ℂ) = 0 by push_cast; linear_combination h)
  have hn1 : kn ≠ 1 := by
    have h := hc (.ne (.var "n") (.int 1)) (by simp [rubi4112r41])
    simp [Cond.Holds, Defined, eval, hkn] at h
    intro h1; apply h; simp [h1]
  have hm1 : (km : ℂ) + 1 ≠ 0 := by norm_cast; omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r41, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi4112r41, Defined, eval, Interp.complex, hk_m, hk_n, hk_p, p1, p1'] at hw ⊢
    have : ¬ kp - 1 < 0 := by omega
    have : ¬ kp < 1 := by omega
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi4112r41, Defined, eval, recEnv, Interp.complex, hk_m, hk_n, hk_p, m1, im1] at hw ⊢
    have : ¬ km + 1 < 0 → True := fun _ => trivial
    have hm' : ¬ env "m" + 1 = 0 := by rw [hkm]; exact hm1
    exact ⟨⟨fun h => hw.1 (by omega), hw.2⟩, hm'⟩
  · simp only [rubi4112r41, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi4112r41, Defined, eval, Interp.complex, hk_m, hk_n, hk_p] at ht
    simp [rubi4112r41, eval, Interp.complex, hk_m, hk_n, hk_p, p1, p1'] at hΦ
    have hor : t ≠ 0 ∨ kn = 0 := by
      rcases eq_or_ne t 0 with h | h
      · right; by_contra hk
        rcases lt_or_gt_of_ne hk with hk | hk
        · exact (ht.2.1 hk) h
        · exact (ht.1 (by omega)) h
      · exact Or.inl h
    have hkey : (kn : ℂ) * (t ^ (km + 1) * t ^ (kn - 1)) = kn := by
      rcases hor with h | h
      · rw [← zpow_add₀ h, show km + 1 + (kn - 1) = 0 by omega, zpow_zero, mul_one]
      · subst h; simp
    have hX := hasDerivAt_zpow (km + 1) t (by rcases hor with h | h; exact Or.inl h; exact Or.inr (by omega))
    have hu := ((hasDerivAt_zpow kn t (by rcases hor with h | h; exact Or.inl h; exact Or.inr (by omega))).const_mul (env "b")).const_add (env "a")
    have hSp := (hasDerivAt_zpow kp _ (Or.inr (by omega))).comp t ((Complex.hasDerivAt_sin _).comp t hu)
    have hF0 := ((hX.mul hSp).mul_const (env "m" + 1)⁻¹).add
      (hΦ.const_mul (-(env "b" * env "n" * env "p") * (env "m" + 1)⁻¹))
    convert hF0 using 1
    · funext v; simp [rubi4112r41, eval, recEnv, Interp.complex, hk_m, hk_n, hk_p, m1, p1, p1', im1, Function.comp_def]; try ring
    · simp [rubi4112r41, eval, Interp.complex, hk_m, hk_n, hk_p, Function.comp_def]
      rw [hkm, hkn, hkp]
      generalize Complex.sin (env "a" + env "b" * t ^ kn) ^ (kp - 1) = Q
      generalize Complex.sin (env "a" + env "b" * t ^ kn) ^ kp = P
      generalize Complex.cos (env "a" + env "b" * t ^ kn) = C
      generalize Complex.sin (env "a" + env "b" * t ^ kn) = S
      field_simp
      linear_combination (-((kp : _) * Q * C * env "b")) * hkey

theorem rubi4112r42_real : rubi4112r42.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4112r42.conditions rubi4112r42.body rubi4112r42.result rubi4112r42.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r42, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r42, Defined, eval, Interp.real, hk_m, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r42, Defined, eval, Interp.real, hk_m, hk_n, hk_p] at h
  have hkm : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have m1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [hkm]; push_cast; ring)
  have p1 : intValue? (env "p" + -1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p1' : intValue? (env "p" + -1 * 1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp1 : 1 < kp := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi4112r42])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkp] at h; simp [Interp.real] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hmn : km + kn = 0 := by
    have h := hc (.eq (.app2 .add (.var "m") (.var "n")) (.int 0)) (by simp [rubi4112r42])
    simp [Cond.Holds, Defined, eval, hkm, hkn] at h
    exact_mod_cast (show ((km + kn : ℤ) : ℝ) = 0 by push_cast; linear_combination h)
  have hn1 : kn ≠ 1 := by
    have h := hc (.ne (.var "n") (.int 1)) (by simp [rubi4112r42])
    simp [Cond.Holds, Defined, eval, hkn] at h
    intro h1; apply h; simp [h1]
  have hm1 : (km : ℝ) + 1 ≠ 0 := by norm_cast; omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r42, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi4112r42, Defined, eval, Interp.real, hk_m, hk_n, hk_p, p1, p1'] at hw ⊢
    have : ¬ kp - 1 < 0 := by omega
    have : ¬ kp < 1 := by omega
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi4112r42, Defined, eval, recEnv, Interp.real, hk_m, hk_n, hk_p, m1, im1] at hw ⊢
    have : ¬ km + 1 < 0 → True := fun _ => trivial
    have hm' : ¬ env "m" + 1 = 0 := by rw [hkm]; exact hm1
    exact ⟨⟨fun h => hw.1 (by omega), hw.2⟩, hm'⟩
  · simp only [rubi4112r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi4112r42, Defined, eval, Interp.real, hk_m, hk_n, hk_p] at ht
    simp [rubi4112r42, eval, Interp.real, hk_m, hk_n, hk_p, p1, p1'] at hΦ
    have hor : t ≠ 0 ∨ kn = 0 := by
      rcases eq_or_ne t 0 with h | h
      · right; by_contra hk
        rcases lt_or_gt_of_ne hk with hk | hk
        · exact (ht.2.1 hk) h
        · exact (ht.1 (by omega)) h
      · exact Or.inl h
    have hkey : (kn : ℝ) * (t ^ (km + 1) * t ^ (kn - 1)) = kn := by
      rcases hor with h | h
      · rw [← zpow_add₀ h, show km + 1 + (kn - 1) = 0 by omega, zpow_zero, mul_one]
      · subst h; simp
    have hX := hasDerivAt_zpow (km + 1) t (by rcases hor with h | h; exact Or.inl h; exact Or.inr (by omega))
    have hu := ((hasDerivAt_zpow kn t (by rcases hor with h | h; exact Or.inl h; exact Or.inr (by omega))).const_mul (env "b")).const_add (env "a")
    have hSp := (hasDerivAt_zpow kp _ (Or.inr (by omega))).comp t ((Real.hasDerivAt_cos _).comp t hu)
    have hF0 := ((hX.mul hSp).mul_const (env "m" + 1)⁻¹).add
      (hΦ.const_mul ((env "b" * env "n" * env "p") * (env "m" + 1)⁻¹))
    convert hF0 using 1
    · funext v; simp [rubi4112r42, eval, recEnv, Interp.real, hk_m, hk_n, hk_p, m1, p1, p1', im1, Function.comp_def]; try ring
    · simp [rubi4112r42, eval, Interp.real, hk_m, hk_n, hk_p, Function.comp_def]
      rw [hkm, hkn, hkp]
      generalize Real.cos (env "a" + env "b" * t ^ kn) ^ (kp - 1) = Q
      generalize Real.cos (env "a" + env "b" * t ^ kn) ^ kp = P
      generalize Real.sin (env "a" + env "b" * t ^ kn) = C
      generalize Real.sin (env "a" + env "b" * t ^ kn) = S
      field_simp
      linear_combination (((kp : _) * Q * C * env "b")) * hkey

theorem rubi4112r42_complex : rubi4112r42.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4112r42.conditions rubi4112r42.body rubi4112r42.result rubi4112r42.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r42, Defined, eval, Interp.complex, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r42, Defined, eval, Interp.complex, hk_m, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi4112r42, Defined, eval, Interp.complex, hk_m, hk_n, hk_p] at h
  have hkm : env "m" = (km : ℂ) := (intValue?_eq _ _).1 hk_m
  have hkn : env "n" = (kn : ℂ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℂ) := (intValue?_eq _ _).1 hk_p
  have m1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [hkm]; push_cast; ring)
  have p1 : intValue? (env "p" + -1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p1' : intValue? (env "p" + -1 * 1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp1 : 1 < kp := by
    have h := hc (.gt (.var "p") (.int 1)) (by simp [rubi4112r42])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkp] at h; simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hmn : km + kn = 0 := by
    have h := hc (.eq (.app2 .add (.var "m") (.var "n")) (.int 0)) (by simp [rubi4112r42])
    simp [Cond.Holds, Defined, eval, hkm, hkn] at h
    exact_mod_cast (show ((km + kn : ℤ) : ℂ) = 0 by push_cast; linear_combination h)
  have hn1 : kn ≠ 1 := by
    have h := hc (.ne (.var "n") (.int 1)) (by simp [rubi4112r42])
    simp [Cond.Holds, Defined, eval, hkn] at h
    intro h1; apply h; simp [h1]
  have hm1 : (km : ℂ) + 1 ≠ 0 := by norm_cast; omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4112r42, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi4112r42, Defined, eval, Interp.complex, hk_m, hk_n, hk_p, p1, p1'] at hw ⊢
    have : ¬ kp - 1 < 0 := by omega
    have : ¬ kp < 1 := by omega
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi4112r42, Defined, eval, recEnv, Interp.complex, hk_m, hk_n, hk_p, m1, im1] at hw ⊢
    have : ¬ km + 1 < 0 → True := fun _ => trivial
    have hm' : ¬ env "m" + 1 = 0 := by rw [hkm]; exact hm1
    exact ⟨⟨fun h => hw.1 (by omega), hw.2⟩, hm'⟩
  · simp only [rubi4112r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi4112r42, Defined, eval, Interp.complex, hk_m, hk_n, hk_p] at ht
    simp [rubi4112r42, eval, Interp.complex, hk_m, hk_n, hk_p, p1, p1'] at hΦ
    have hor : t ≠ 0 ∨ kn = 0 := by
      rcases eq_or_ne t 0 with h | h
      · right; by_contra hk
        rcases lt_or_gt_of_ne hk with hk | hk
        · exact (ht.2.1 hk) h
        · exact (ht.1 (by omega)) h
      · exact Or.inl h
    have hkey : (kn : ℂ) * (t ^ (km + 1) * t ^ (kn - 1)) = kn := by
      rcases hor with h | h
      · rw [← zpow_add₀ h, show km + 1 + (kn - 1) = 0 by omega, zpow_zero, mul_one]
      · subst h; simp
    have hX := hasDerivAt_zpow (km + 1) t (by rcases hor with h | h; exact Or.inl h; exact Or.inr (by omega))
    have hu := ((hasDerivAt_zpow kn t (by rcases hor with h | h; exact Or.inl h; exact Or.inr (by omega))).const_mul (env "b")).const_add (env "a")
    have hSp := (hasDerivAt_zpow kp _ (Or.inr (by omega))).comp t ((Complex.hasDerivAt_cos _).comp t hu)
    have hF0 := ((hX.mul hSp).mul_const (env "m" + 1)⁻¹).add
      (hΦ.const_mul ((env "b" * env "n" * env "p") * (env "m" + 1)⁻¹))
    convert hF0 using 1
    · funext v; simp [rubi4112r42, eval, recEnv, Interp.complex, hk_m, hk_n, hk_p, m1, p1, p1', im1, Function.comp_def]; try ring
    · simp [rubi4112r42, eval, Interp.complex, hk_m, hk_n, hk_p, Function.comp_def]
      rw [hkm, hkn, hkp]
      generalize Complex.cos (env "a" + env "b" * t ^ kn) ^ (kp - 1) = Q
      generalize Complex.cos (env "a" + env "b" * t ^ kn) ^ kp = P
      generalize Complex.sin (env "a" + env "b" * t ^ kn) = C
      generalize Complex.sin (env "a" + env "b" * t ^ kn) = S
      field_simp
      linear_combination (((kp : _) * Q * C * env "b")) * hkey

theorem rubi535r7_counterexample_real : ¬ rubi535r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi535r7.conditions rubi535r7.body rubi535r7.result rubi535r7.integrals
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have h0 : intValue? ((-2 : ℝ) + 1) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h0' : intValue? ((1 : ℝ) + -1) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have h0'' : intValue? ((1 : ℝ) + -1 * 1) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "e" ∨ s = "p" then 1 else if s = "m" then -2 else 0) (1 : ℝ) ?_ ?_
    (fun h w => w * (((rubi535r7.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "e" ∨ s = "p" then 1 else if s = "m" then -2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi535r7, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, im1, im2]
  · exact Eventually.of_forall fun w => by simp [rubi535r7, Defined, eval, Interp.real, i0, i1, i2, im1, im2]
  · simp only [rubi535r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    simp [List.lookup]
    exact hasDerivAt_mul_const _
  · intro h
    simp [rubi535r7, Defined, eval, Interp.real, i0, i1, i2, im1, im2, h0, h0', h0'', recEnv] at h

theorem rubi535r7_counterexample_complex : ¬ rubi535r7.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi535r7.conditions rubi535r7.body rubi535r7.result rubi535r7.integrals
  have i1 : intValue? (1 : ℂ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℂ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have i0 : intValue? (0 : ℂ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have h0 : intValue? ((-2 : ℂ) + 1) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have h0' : intValue? ((1 : ℂ) + -1) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have h0'' : intValue? ((1 : ℂ) + -1 * 1) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "e" ∨ s = "p" then 1 else if s = "m" then -2 else 0) (1 : ℂ) ?_ ?_
    (fun h w => w * (((rubi535r7.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "e" ∨ s = "p" then 1 else if s = "m" then -2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp [rubi535r7, Cond.Holds, Defined, eval, Interp.complex, i0, i1, i2, im1, im2, Ne.symm Complex.I_ne_zero]
  · exact Eventually.of_forall fun w => by simp [rubi535r7, Defined, eval, Interp.complex, i0, i1, i2, im1, im2, Ne.symm Complex.I_ne_zero]
  · simp only [rubi535r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    simp [List.lookup]
    exact hasDerivAt_mul_const _
  · intro h
    simp [rubi535r7, Defined, eval, Interp.complex, i0, i1, i2, im1, im2, h0, h0', h0'', recEnv] at h

theorem rubi33r9_real : rubi33r9.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi33r9.conditions rubi33r9.body rubi33r9.result rubi33r9.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi33r9, Defined, eval, Interp.real, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi33r9, Defined, eval, Interp.real, hk_n, hk_p] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p1 : intValue? (env "p" + -1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p1' : intValue? (env "p" + -1 * 1) = some (kp - 1) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp0 : 0 < kp := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi33r9])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkp] at h; simp [Interp.real] at h; exact_mod_cast h
  have hK : env "e" * env "f" - env "d" * env "g" ≠ 0 := by
    have h := hc (.ne (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int 0)) (by simp [rubi33r9])
    simp [Cond.Holds, Defined, eval, Interp.real] at h
    intro h0; apply h; linear_combination h0
  have hK' : env "e" * env "f" + -(env "d" * env "g") ≠ 0 := by intro h; apply hK; linear_combination h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi33r9, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi33r9, Defined, eval, Interp.real, i2, im1, hk_n, hk_p, p1, p1'] at hw ⊢
    have : ¬ kp - 1 < 0 := by omega
    have : ¬ kp < 1 := by omega
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi33r9, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, hk_p] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi33r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi33r9, Defined, eval, Interp.real, i2, im1, hk_n, hk_p] at ht
    simp [rubi33r9, eval, Interp.real, i2, im1, hk_n, hk_p, p1, p1'] at hΦ
    obtain ⟨⟨⟨hpos0, hpos⟩, -⟩, hfg⟩ := ht
    have hor : (env "d" + env "e" * t) ≠ 0 ∨ 0 ≤ kn := by
      by_cases h : kn < 0
      · exact Or.inl (hpos0 h)
      · exact Or.inr (by omega)
    have hne : env "c" * (env "d" + env "e" * t) ^ kn ≠ 0 := hpos.ne'
    have hU : HasDerivAt (fun v : ℝ => env "d" + env "e" * v) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    have hL := (Real.hasDerivAt_log hne).comp t (((hasDerivAt_zpow kn _ hor).comp t hU).const_mul (env "c"))
    have hkey : (env "d" + env "e" * t) * ((env "c" * (env "d" + env "e" * t) ^ kn)⁻¹ * (env "c" * ((kn : ℝ) * (env "d" + env "e" * t) ^ (kn - 1) * env "e"))) = kn * env "e" := by
      rcases eq_or_ne (env "d" + env "e" * t) 0 with h0 | h0
      · have h1 : (env "d" + env "e" * t) ^ kn ≠ 0 := fun h => hne (by rw [h, mul_zero])
        have hk0 : kn = 0 := by
          by_contra hk; rw [h0] at h1; exact h1 (zero_zpow kn hk)
        subst hk0; simp
      · have hc0 : env "c" ≠ 0 := fun h => hne (by rw [h, zero_mul])
        rw [zpow_sub_one₀ h0]
        field_simp
    obtain ⟨Q, hQ, hkQ⟩ : ∃ Q : ℝ, (env "c" * (env "d" + env "e" * t) ^ kn)⁻¹ * (env "c" * ((kn : ℝ) * (env "d" + env "e" * t) ^ (kn - 1) * env "e")) = Q ∧ (env "d" + env "e" * t) * Q = kn * env "e" :=
      ⟨_, rfl, hkey⟩
    rw [hQ] at hL
    have hA := (hL.const_mul (env "b")).const_add (env "a")
    have hAp := (hasDerivAt_zpow kp _ (Or.inr hp0.le)).comp t hA
    have hW : HasDerivAt (fun v : ℝ => (env "e" * env "f" + -(env "d" * env "g")) * (env "f" + env "g" * v)) ((env "e" * env "f" + -(env "d" * env "g")) * env "g") t := by
      simpa using (((hasDerivAt_id t).const_mul (env "g")).const_add (env "f")).const_mul (env "e" * env "f" + -(env "d" * env "g"))
    have hWi := hW.inv (mul_ne_zero hK' hfg)
    have hF0 := ((hU.mul hAp).mul hWi).add (hΦ.const_mul (-(env "b" * env "e" * env "n" * env "p") * (env "e" * env "f" + -(env "d" * env "g"))⁻¹))
    convert hF0 using 1
    · funext v; simp [rubi33r9, eval, recEnv, Interp.real, i2, im1, hk_n, hk_p, p1, p1', Function.comp_def]; try ring
    · simp [rubi33r9, eval, Interp.real, i2, im1, hk_n, hk_p, Function.comp_def]
      rw [hkn, hkp]
      have hP : ∀ k : ℤ, True := fun _ => trivial
      rcases eq_or_ne (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ kn)) 0 with hA0 | hA0
      · rw [hA0]
        rcases eq_or_ne kp 1 with h1 | h1
        · subst h1; simp; field_simp
          rw [show (env "d" + env "e" * t) * Q + -(env "e" * (kn : ℝ)) = 0 by linear_combination hkQ]; simp
        · rw [zero_zpow _ (by omega), zero_zpow _ (by omega)]; simp
      · rw [zpow_sub_one₀ hA0]
        generalize (env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ kn)) ^ kp = P
        generalize env "a" + env "b" * Real.log (env "c" * (env "d" + env "e" * t) ^ kn) = A at *
        field_simp
        have hK2 : env "f" * env "e" + -(env "g" * env "d") ≠ 0 := by intro h; apply hK; linear_combination h
        rw [eq_div_iff hK2]
        linear_combination (-(P * (env "f" + env "g" * t) * (kp : ℝ) * env "b")) * hkQ

end OSR.IntegrationRec161
