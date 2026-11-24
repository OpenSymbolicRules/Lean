import OSR.Calculus

open OSR OSR.Calculus Filter Topology
namespace OSR.IntegrationCandidate
private abbrev x : Expr := .var "x"
private abbrev v (s : String) : Expr := .var s
private abbrev add (a b : Expr) : Expr := .app2 .add a b
private abbrev mul (a b : Expr) : Expr := .app2 .mul a b
private abbrev pow (a b : Expr) : Expr := .pow a b
private abbrev inv (a : Expr) : Expr := pow a (.int (-1))
private abbrev sq (a : Expr) : Expr := pow a (.int 2)
private abbrev sqrt (a : Expr) : Expr := .app2 .root a (.int 2)
private abbrev rad : Expr := sqrt (add (v "a") (mul (v "b") (sq x)))
private abbrev arg : Expr := mul (mul (v "c") x) (inv rad)
private abbrev atan : Expr := .app1 .arctan arg

/-- RUBI 5.3.7 #19, with its original equality condition. -/
def rubi537r19 : CRule where
  id := "integration.rubi_5_3_7_r19"
  legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:19"
  shape := .antideriv; x := "x"
  body := mul (.int 1) (inv (mul rad atan))
  result := mul (mul (.int 1) (inv (v "c"))) (.app1 .ln atan)
  independent := ["a", "b", "c"]
  conditions := [.eq (add (v "b") (sq (v "c"))) (.int 0)]
  priority := 73110
  description := "RUBI 5.3.7 #19: logarithm of arctangent"
  provenance := { method := .derived, sources := [
    { name := "OpenSymbolicRules/Integration", locator := "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:19", revision := some "441af08fa2c31283f3f8084d4a46e417d87744ab", license := some "MIT" },
    { name := "Rubi", locator := "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#19", revision := some "61e9c18ea248061cd83c67882f7c91a73cef912d", license := some "MIT" }] }

/-- The original rule fails over the reals at a=2, b=-1, c=1 and x=-1. -/
theorem rubi537r19_counterexample_real : ¬ rubi537r19.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi537r19.conditions rubi537r19.body rubi537r19.result
  let env : String → ℝ := fun s => if s = "a" then 2 else if s = "b" then -1 else if s = "c" then 1 else 0
  refine not_antiderivHoldsUnder env (-1) ?_ ?_ ?_
  · intro c hc
    simp only [rubi537r19, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
    norm_num [Cond.Holds, Defined, eval, Interp.real, env, h2]
  · filter_upwards [isOpen_Ioo.mem_nhds (show (-5/4 : ℝ) < -1 ∧ (-1 : ℝ) < -3/4 by norm_num)] with w hw
    have hwlo : (-5/4 : ℝ) < w := hw.1
    have hwhi : w < (-3/4 : ℝ) := hw.2
    have hm : (w + 5/4) * (w + 3/4) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hpos : 0 < 2 - w ^ 2 := by nlinarith
    have hw0 : w ≠ 0 := by linarith [hw.2]
    have hs : Real.sqrt (2-w^2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
    have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
    have hsa : Real.sqrt (2 + -w^2) ≠ 0 := by simpa [sub_eq_add_neg] using hs
    simp [rubi537r19, rad, arg, atan, inv, sq, mul, add, x, v, Defined, eval, Interp.real, env, Function.update, h2, hm1, hw0, hsa, show w ^ 2 ≤ 2 by linarith [hpos]]
  · have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
    have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
    simp [rubi537r19, rad, arg, atan, inv, sq, mul, add, x, v, Defined, eval, Interp.real, env, Function.update, h2, hm1]

end OSR.IntegrationCandidate
