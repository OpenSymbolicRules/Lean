import OSR.Calculus
open Filter Topology

namespace OSR.IntegrationAcosh

theorem arcosh_derivative (a b t : ℝ) (ha : 0 < a) (hu : a < b*t) :
    HasDerivAt (fun z : ℝ => Real.arcosh (b*z/a) / b)
      (1 / (Real.sqrt (a+b*t) * Real.sqrt (-a+b*t))) t := by
  have hb : b ≠ 0 := by intro h; simp [h] at hu; linarith
  have ha0 : a ≠ 0 := ne_of_gt ha
  have h1 : 1 < b*t/a := (lt_div_iff₀ ha).2 (by linarith)
  have hp : 0 < a + b*t := by linarith
  have hq : 0 < -a + b*t := by linarith
  have hr : 0 < (b*t/a)^2 - 1 := by nlinarith
  have hU : 0 < Real.sqrt (a+b*t) := Real.sqrt_pos.2 hp
  have hV : 0 < Real.sqrt (-a+b*t) := Real.sqrt_pos.2 hq
  have hW : 0 < Real.sqrt ((b*t/a)^2-1) := Real.sqrt_pos.2 hr
  have hsq : (a * Real.sqrt ((b*t/a)^2-1))^2 =
      (Real.sqrt (a+b*t) * Real.sqrt (-a+b*t))^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hr.le, Real.sq_sqrt hp.le, Real.sq_sqrt hq.le]
    field_simp; ring
  have hrad : a * Real.sqrt ((b*t/a)^2-1) = Real.sqrt (a+b*t) * Real.sqrt (-a+b*t) := by
    nlinarith [mul_pos ha hW, mul_pos hU hV]
  have hlin : HasDerivAt (fun z : ℝ => b*z/a) (b/a) t := by
    simpa using ((hasDerivAt_id t).const_mul b).div_const a
  have hval : (Real.sqrt ((b*t/a)^2-1))⁻¹ * (b/a) / b =
      1 / (Real.sqrt (a+b*t) * Real.sqrt (-a+b*t)) := by
    rw [← hrad]
    field_simp [ha0, hb, ne_of_gt hW]
  have h := ((Real.hasDerivAt_arcosh h1).comp t hlin).div_const b
  convert h using 1
  · funext z
    rfl
  · exact hval.symm


open OSR OSR.Calculus
private abbrev x : Expr := .var "x"
private abbrev v (s : String) : Expr := .var s
private abbrev add (a b : Expr) : Expr := .app2 .add a b
private abbrev mul (a b : Expr) : Expr := .app2 .mul a b
private abbrev inv (a : Expr) : Expr := .pow a (.int (-1))
private abbrev sqrt (a : Expr) : Expr := .app2 .root a (.int 2)

def rubi1112r21 : CRule where
  id := "integration.rubi_1_1_1_2_r21"
  legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:21"
  shape := .antideriv; x := "x"
  body := mul (.int 1) (inv (mul (sqrt (add (v "a") (mul (v "b") x))) (sqrt (add (v "c") (mul (v "d") x)))))
  result := mul (.app1 .arccosh (mul (mul (v "b") x) (inv (v "a")))) (inv (v "b"))
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (add (v "a") (v "c")) (.int 0), .eq (add (v "b") (mul (.int (-1)) (v "d"))) (.int 0), .gt (v "a") (.int 0)]
  priority := 73120
  description := "RUBI 1.1.1.2 #21: product of square roots"
  provenance := { method := .derived, sources := [
    { name := "OpenSymbolicRules/Integration", locator := "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:21", revision := some "be375cfd62c2ef990b0207f863123d1f83e8e929", license := some "MIT" },
    { name := "Rubi", locator := "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.m#21", revision := some "61e9c18ea248061cd83c67882f7c91a73cef912d", license := some "MIT" }] }

theorem rubi1112r21_real : rubi1112r21.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi1112r21.conditions rubi1112r21.body rubi1112r21.result
  intro env hc t hF
  have h2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have hm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hD (w : ℝ) : Defined Interp.real (Function.update env "x" w) rubi1112r21.body ↔
      0 ≤ env "a" + env "b" * w ∧ 0 ≤ env "c" + env "d" * w ∧
      Real.sqrt (env "a" + env "b" * w) * Real.sqrt (env "c" + env "d" * w) ≠ 0 := by
    simp [rubi1112r21, sqrt, inv, add, mul, x, v, Defined, eval, Interp.real, h2, hm1, Function.update]
    tauto
  have ha : 0 < env "a" := by
    have h := hc (.gt (v "a") (.int 0)) (by simp [rubi1112r21])
    simpa [Cond.Holds, Defined, eval, Interp.real, v] using h
  have hac : env "c" = -env "a" := by
    have h := hc (.eq (add (v "a") (v "c")) (.int 0)) (by simp [rubi1112r21, add, v])
    simp [Cond.Holds, Defined, eval] at h
    linarith
  have hbd : env "d" = env "b" := by
    have h := hc (.eq (add (v "b") (mul (.int (-1)) (v "d"))) (.int 0)) (by simp [rubi1112r21, add, mul, v])
    simp [Cond.Holds, Defined, eval] at h
    linarith
  have hFpos (w : ℝ) (hFw : Defined Interp.real (Function.update env "x" w) rubi1112r21.body) :
      env "a" < env "b" * w := by
    have hw := (hD w).1 hFw
    have hne : Real.sqrt (env "c" + env "d" * w) ≠ 0 := (mul_ne_zero_iff.mp hw.2.2).2
    have hp : 0 < env "c" + env "d" * w := by
      by_contra hn
      have hz : env "c" + env "d" * w = 0 := le_antisymm (not_lt.mp hn) hw.2.1
      simp [hz] at hne
    rw [hac, hbd] at hp
    linarith
  have hu : env "a" < env "b" * t := hFpos t hF.self_of_nhds
  have hb : env "b" ≠ 0 := by intro h; simp [h] at hu; linarith
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    have hw' := hFpos w hw
    have harg : 1 ≤ env "b" * w / env "a" := le_of_lt ((lt_div_iff₀ ha).2 (by linarith))
    simp [rubi1112r21, sqrt, inv, add, mul, x, v, Defined, eval, Interp.real, hm1, Function.update, ha.ne', hb]
    simpa [div_eq_mul_inv] using harg
  · have h := arcosh_derivative (env "a") (env "b") t ha hu
    simpa [rubi1112r21, sqrt, inv, add, mul, x, v, eval, Interp.real, h2, hm1, Function.update, hac, hbd, div_eq_mul_inv] using h
end OSR.IntegrationAcosh
