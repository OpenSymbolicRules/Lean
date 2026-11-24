import OSR.Calculus
open OSR OSR.Calculus Filter Topology
namespace OSR.IntegrationAtanh
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
private abbrev atanh : Expr := .app1 .arctanh arg

def rubi737r19 : CRule where
  id := "integration.rubi_7_3_7_r19"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:19"
  shape := .antideriv; x := "x"
  body := mul (.int 1) (inv (mul rad atanh))
  result := mul (mul (.int 1) (inv (v "c"))) (.app1 .ln atanh)
  independent := ["a", "b", "c"]
  conditions := [.eq (v "b") (sq (v "c"))]
  priority := 73130
  description := "RUBI 7.3.7 #19: logarithm of inverse hyperbolic tangent"
  provenance := { method := .derived, sources := [
    { name := "OpenSymbolicRules/Integration", locator := "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:19", revision := some "be375cfd62c2ef990b0207f863123d1f83e8e929", license := some "MIT" },
    { name := "Rubi", locator := "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#19", revision := some "61e9c18ea248061cd83c67882f7c91a73cef912d", license := some "MIT" }] }

/-- The real rule fails at a=3, b=1, c=1 and x=-1. -/
theorem rubi737r19_counterexample_real : ¬ rubi737r19.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi737r19.conditions rubi737r19.body rubi737r19.result
  let env : String → ℝ := fun s => if s = "a" then 3 else if s = "b" then 1 else if s = "c" then 1 else 0
  refine not_antiderivHoldsUnder env (-1) ?_ ?_ ?_
  · intro c hc
    simp only [rubi737r19, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
    norm_num [Cond.Holds, Defined, eval, Interp.real, env, h2]
  · filter_upwards [isOpen_Ioo.mem_nhds (show (-5/4 : ℝ) < -1 ∧ (-1 : ℝ) < -3/4 by norm_num)] with w hw
    have hwneg : w < 0 := by linarith [hw.2]
    have hpos : 0 < 3 + w ^ 2 := by positivity
    have hspos : 0 < Real.sqrt (3+w^2) := Real.sqrt_pos.2 hpos
    have hsq := Real.sq_sqrt hpos.le
    have hgt : -w < Real.sqrt (3+w^2) := by nlinarith
    have hargneg : w * (Real.sqrt (3+w^2))⁻¹ < 0 := mul_neg_of_neg_of_pos hwneg (inv_pos.mpr hspos)
    have harglower : -1 < w * (Real.sqrt (3+w^2))⁻¹ := by
      have hh : -1 * Real.sqrt (3+w^2) < w := by linarith
      have hd := (lt_div_iff₀ hspos).2 hh
      simpa [div_eq_mul_inv] using hd
    have hargupper : w * (Real.sqrt (3+w^2))⁻¹ < 1 := by linarith
    have hatneg : Real.artanh (w * (Real.sqrt (3+w^2))⁻¹) < 0 := Real.artanh_neg ⟨harglower,hargneg⟩
    have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
    have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
    simp [rubi737r19, rad, arg, atanh, inv, sq, mul, add, x, v, Defined, eval, Interp.real, env, Function.update, h2, hm1, hpos.le, hspos.ne', harglower, hargupper, ne_of_lt hatneg]
  · have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
    have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
    simp [rubi737r19, rad, arg, atanh, inv, sq, mul, add, x, v, Defined, eval, Interp.real, env, Function.update, h2, hm1]
    have hn : Real.artanh (-(1/2 : ℝ)) < 0 := Real.artanh_neg (by norm_num)
    norm_num at *
    exact hn.le
end OSR.IntegrationAtanh
