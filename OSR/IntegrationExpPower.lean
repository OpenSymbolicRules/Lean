import OSR.Calculus

open OSR OSR.Calculus Filter Topology
namespace OSR.IntegrationExpPower

private abbrev v (s : String) : Expr := .var s
private abbrev add (a b : Expr) : Expr := .app2 .add a b
private abbrev mul (a b : Expr) : Expr := .app2 .mul a b
private abbrev pow (a b : Expr) : Expr := .pow a b
private abbrev inv (a : Expr) : Expr := pow a (.int (-1))
private abbrev body : Expr := pow (pow (v "F") (mul (v "c")
  (add (v "a") (mul (v "b") (v "x"))))) (v "n")

/-- RUBI 4.17.3.0 (pinned source), 2.3 #1, with its original independence condition. -/
def rubi23r1 : CRule where
  id := "integration.rubi_2_3_r1"
  legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:1"
  shape := .antideriv; x := "x"
  body := body
  result := mul body (inv (mul (mul (mul (v "b") (v "c")) (v "n")) (.app1 .ln (v "F"))))
  independent := ["F", "a", "b", "c", "n"]
  priority := 810
  description := "RUBI 2.3 #1: nested exponential with linear exponent"
  provenance := { method := .derived, sources := [
    { name := "OpenSymbolicRules/Integration", locator := "rubi:2 Exponentials/2.3 Miscellaneous exponentials:1", revision := some "f84ed2a81702836c019e647e0a586b8d576ae7c6", license := some "MIT" },
    { name := "Rubi", locator := "2 Exponentials/2.3 Miscellaneous exponentials.m#1", revision := some "61e9c18ea248061cd83c67882f7c91a73cef912d", license := some "MIT" }] }

/-- At F=2, a=b=0, c=n=1 the integrand is defined but the result divides by zero. -/
theorem rubi23r1_counterexample_real : ¬ rubi23r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi23r1.conditions rubi23r1.body rubi23r1.result
  let env : String → ℝ := fun s => if s = "F" then 2 else if s = "c" ∨ s = "n" then 1 else 0
  refine not_antiderivHoldsUnder env 0 ?_ ?_ ?_
  · intro c hc
    simp [rubi23r1] at hc
  · filter_upwards with w
    have h0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
    have h1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
    simp [rubi23r1, body, pow, mul, add, v, Defined, eval, Interp.real,
      env, Function.update, h0, h1]
  · have h0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
    have h1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
    have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
    simp [rubi23r1, body, pow, inv, mul, add, v, Defined, eval, Interp.real,
      env, Function.update, h0, h1, hm1]

private abbrev body8 : Expr := pow (v "F")
  (add (v "a") (mul (v "b") (add (v "c") (mul (v "d") (v "x")))))

/-- RUBI 2.3 #8 with the original independence condition. -/
def rubi23r8 : CRule where
  id := "integration.rubi_2_3_r8"
  legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:8"
  shape := .antideriv; x := "x"
  body := body8
  result := mul body8 (inv (mul (mul (v "b") (v "d")) (.app1 .ln (v "F"))))
  independent := ["F", "a", "b", "c", "d"]
  priority := 880
  description := "RUBI 2.3 #8: exponential with affine exponent"
  provenance := { method := .derived, sources := [
    { name := "OpenSymbolicRules/Integration", locator := "rubi:2 Exponentials/2.3 Miscellaneous exponentials:8", revision := some "f84ed2a81702836c019e647e0a586b8d576ae7c6", license := some "MIT" },
    { name := "Rubi", locator := "2 Exponentials/2.3 Miscellaneous exponentials.m#8", revision := some "61e9c18ea248061cd83c67882f7c91a73cef912d", license := some "MIT" }] }

/-- At F=2, a=b=0, c=d=1 the integrand is defined but the result divides by zero. -/
theorem rubi23r8_counterexample_real : ¬ rubi23r8.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi23r8.conditions rubi23r8.body rubi23r8.result
  let env : String → ℝ := fun s => if s = "F" then 2 else if s = "c" ∨ s = "d" then 1 else 0
  refine not_antiderivHoldsUnder env 0 ?_ ?_ ?_
  · intro c hc
    simp [rubi23r8] at hc
  · filter_upwards with w
    have h0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
    simp [rubi23r8, body8, pow, mul, add, v, Defined, eval, Interp.real,
      env, Function.update, h0]
  · have h0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
    have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
    simp [rubi23r8, body8, pow, inv, mul, add, v, Defined, eval, Interp.real,
      env, Function.update, h0, hm1]

end OSR.IntegrationExpPower
