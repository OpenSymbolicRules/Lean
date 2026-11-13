import OSR.Calculus
import OSR.IntegrationRec3

/-!
# Integration (RUBI)

First migration from `OpenSymbolicRules/Integration` at commit
`f84ed2a81702836c019e647e0a586b8d576ae7c6` (RUBI 4.16.1, 6,257 rules).

The migration started with nine rules selected by a syntactic inventory:
their only conditions are `FreeQ` and, once the outer `Int` is removed, they use only
heads of the registry.  A rule `Int[F, x] := G` becomes the calculus rule
`int(λx. F) ⟶ λx. G` (`calculus1#int`, shape `antideriv`), whose statement is
`OSR.Calculus.AntiderivHolds`: wherever `F` is defined on a neighbourhood of
`t`, `G` is defined on a neighbourhood of `t` and has derivative `F` at `t`.

Encoding conventions, applied to the converted v0.1 terms without
simplification:

* an n-ary `Multiply` or `Add` is a left-nested chain;
* `Power[u, -1]` stays a power with exponent `-1`, not a division;
* an optional wildcard (`c.`, `n.`, …) is an ordinary metavariable: the v1
  rule matches only the explicit form, not the instances with RUBI's default
  value;
* `FreeQ[{…}, x]` becomes the `independent` constraint of each listed
  metavariable.

The catalogue now also covers conditional and recursive antiderivative
rules, with declarations and per-domain proofs or refutations in
`OSR.IntegrationRec`, `OSR.IntegrationRec2` and `OSR.IntegrationRec3`.
Rules outside the fragment are reported in `notMigrated`; see
`docs/integration.md` for the scope and results of each batch.
-/

namespace OSR.Integration

open OSR OSR.Calculus OSR.IntegrationRec OSR.IntegrationRec2 OSR.IntegrationRec3 Filter Topology

private abbrev x : Expr := .var "x"
private abbrev v (n : String) : Expr := .var n
private abbrev ln (e : Expr) : Expr := .app1 .ln e
private abbrev add (a b : Expr) : Expr := .app2 .add a b
private abbrev mul (a b : Expr) : Expr := .app2 .mul a b
private abbrev inv (e : Expr) : Expr := .pow e (.int (-1))

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

/-- Provenance: the converted v0.1 rule and the RUBI source it came from. -/
private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

private def linear : String := "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.1 (a+b x)^m"
private def logPow : String := "rubi:3 Logarithms/3.1.1 (a+b log(c x^n))^p"
private def logMono : String := "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p"
private def logMisc : String := "rubi:3 Logarithms/3.5 Miscellaneous logarithms"
private def simplification : String := "rubi:9 Miscellaneous/9.1 Integrand simplification rules"

/-- `c ln(c x^n)` as converted: `Log[c x^n]`. -/
private abbrev logCxn (c n : String) : Expr := ln (mul (v c) (.pow x (v n)))

/-! ## Rules -/

/-- `Int[1/x, x] := Log[x]`, converted as `1 · x^(-1)`. -/
def reciprocal : CRule where
  id := "integration.reciprocal"; legacyId := some s!"{linear}:1"; shape := .antideriv
  x := "x"; body := mul (.int 1) (inv x); result := ln x; priority := 10
  description := "Antiderivative of 1/x"
  provenance := migrated s!"{linear}:1" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.1 (a+b x)^m.m#1"

/-- `Int[Log[c x^n], x] := x Log[c x^n] - n x`. -/
def logMonomial : CRule where
  id := "integration.log_monomial"; legacyId := some s!"{logPow}:1"; shape := .antideriv
  x := "x"; body := logCxn "c" "n"
  result := add (mul x (logCxn "c" "n")) (mul (mul (.int (-1)) (v "n")) x)
  independent := ["c", "n"]; priority := 20
  description := "Antiderivative of log(c x^n)"
  provenance := migrated s!"{logPow}:1" "3 Logarithms/3.1.1 (a+b log(c x^n))^p.m#1"

/-- `Int[(a + b Log[c x^n])/x, x] := (a + b Log[c x^n])^2/(2 b n)`. -/
def logLinearOverX : CRule where
  id := "integration.log_linear_over_x"; legacyId := some s!"{logMono}:1"; shape := .antideriv
  x := "x"; body := mul (add (v "a") (mul (v "b") (logCxn "c" "n"))) (inv x)
  result := mul (.pow (add (v "a") (mul (v "b") (logCxn "c" "n"))) (.int 2))
    (inv (mul (mul (.int 2) (v "b")) (v "n")))
  independent := ["a", "b", "c", "n"]; priority := 30
  description := "Antiderivative of (a + b log(c x^n))/x"
  provenance := migrated s!"{logMono}:1" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#1"

/-- `log(d x^n)`. -/
private abbrev logDxn : Expr := logCxn "d" "n"

/-- `a + b log(c log(d x^n)^p)`. -/
private abbrev logLogLinear : Expr :=
  add (v "a") (mul (v "b") (ln (mul (v "c") (.pow logDxn (v "p")))))

/-- `Int[(a + b Log[c Log[d x^n]^p])/x, x] :=
Log[d x^n] (a + b Log[c Log[d x^n]^p])/n - b p Log[x]`. -/
def logLogOverX : CRule where
  id := "integration.log_log_over_x"; legacyId := some s!"{logMisc}:2"; shape := .antideriv
  x := "x"; body := mul logLogLinear (inv x)
  result := add (mul (mul logDxn logLogLinear) (inv (v "n")))
    (mul (mul (mul (.int (-1)) (v "b")) (v "p")) (ln x))
  independent := ["a", "b", "c", "d", "n", "p"]; priority := 40
  description := "Antiderivative of (a + b log(c log(d x^n)^p))/x"
  provenance := migrated s!"{logMisc}:2" "3 Logarithms/3.5 Miscellaneous logarithms.m#2"

/-- `Int[a, x] := a x` for `a` free of `x`. -/
def constant : CRule where
  id := "integration.constant"; legacyId := some s!"{simplification}:8"; shape := .antideriv
  x := "x"; body := v "a"; result := mul (v "a") x
  independent := ["a"]; priority := 50
  description := "Antiderivative of a constant"
  provenance := migrated s!"{simplification}:8" "9 Miscellaneous/9.1 Integrand simplification rules.m#8"

/-- `Int[a (b + c x), x] := a (b + c x)^2/(2 c)`. -/
def constTimesLinear : CRule where
  id := "integration.constant_times_linear"; legacyId := some s!"{simplification}:9"
  shape := .antideriv; x := "x"
  body := mul (v "a") (add (v "b") (mul (v "c") x))
  result := mul (mul (v "a") (.pow (add (v "b") (mul (v "c") x)) (.int 2)))
    (inv (mul (.int 2) (v "c")))
  independent := ["a", "b", "c"]; priority := 60
  description := "Antiderivative of a constant times a linear function"
  provenance := migrated s!"{simplification}:9" "9 Miscellaneous/9.1 Integrand simplification rules.m#9"

/-! ### Rules with conditions

`NeQ[a, b]` becomes the condition `a ≠ b` (`relation1#neq`), read
semantically: both sides are defined and their values differ. -/

private def trigLog : String := "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p"

private abbrev sin (e : Expr) : Expr := .app1 .sin e
private abbrev cos (e : Expr) : Expr := .app1 .cos e
private abbrev sq (e : Expr) : Expr := .pow e (.int 2)
private abbrev succ (n : String) : Expr := add (v n) (.int 1)
/-- `m ≠ -1`. -/
private abbrev neMinusOne (m : String) : Cond := .ne (v m) (.int (-1))

/-- `Int[x^m, x] := x^(m+1)/(m+1)` for `m ≠ -1`. -/
def power : CRule where
  id := "integration.power"; legacyId := some s!"{linear}:2"; shape := .antideriv
  x := "x"; body := .pow x (v "m")
  result := mul (.pow x (succ "m")) (inv (succ "m"))
  independent := ["m"]; conditions := [neMinusOne "m"]; priority := 70
  description := "Power rule for antiderivatives"
  provenance := migrated s!"{linear}:2" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.1 (a+b x)^m.m#2"

/-- `Int[(a + b x)^m, x] := (a + b x)^(m+1)/(b (m+1))` for `m ≠ -1`. -/
def linearPower : CRule where
  id := "integration.linear_power"; legacyId := some s!"{linear}:4"; shape := .antideriv
  x := "x"; body := .pow (add (v "a") (mul (v "b") x)) (v "m")
  result := mul (.pow (add (v "a") (mul (v "b") x)) (succ "m")) (inv (mul (v "b") (succ "m")))
  independent := ["a", "b", "m"]; conditions := [neMinusOne "m"]; priority := 80
  description := "Antiderivative of a power of a linear function"
  provenance := migrated s!"{linear}:4" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.1 (a+b x)^m.m#4"

/-- `a + b log(c x^n)`. -/
private abbrev logLinear : Expr := add (v "a") (mul (v "b") (logCxn "c" "n"))

/-- `Int[(d x)^m (a + b Log[c x^n]), x] := (d x)^(m+1) (a + b Log[c x^n])/(d (m+1))
- b n (d x)^(m+1)/(d (m+1)^2)` for `m ≠ -1`. -/
def powerLogLinear : CRule where
  id := "integration.power_log_linear"; legacyId := some s!"{logMono}:4"; shape := .antideriv
  x := "x"; body := mul (.pow (mul (v "d") x) (v "m")) logLinear
  result := add (mul (mul (.pow (mul (v "d") x) (succ "m")) logLinear) (inv (mul (v "d") (succ "m"))))
    (mul (mul (mul (mul (.int (-1)) (v "b")) (v "n")) (.pow (mul (v "d") x) (succ "m")))
      (inv (mul (v "d") (sq (succ "m")))))
  independent := ["a", "b", "c", "d", "m", "n"]; conditions := [neMinusOne "m"]; priority := 90
  description := "Antiderivative of (d x)^m (a + b log(c x^n))"
  provenance := migrated s!"{logMono}:4" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#4"

/-- `d (a + b log(c x^n))`. -/
private abbrev trigArg : Expr := mul (v "d") logLinear

/-- `b^2 d^2 n^2 + 1`. -/
private abbrev trigDen : Expr := add (mul (mul (sq (v "b")) (sq (v "d"))) (sq (v "n"))) (.int 1)

/-- `Int[Sin[d (a + b Log[c x^n])], x] := x Sin[…]/(b^2 d^2 n^2 + 1)
- b d n x Cos[…]/(b^2 d^2 n^2 + 1)` for `b^2 d^2 n^2 + 1 ≠ 0`. -/
def sinLog : CRule where
  id := "integration.sin_log"; legacyId := some s!"{trigLog}:1"; shape := .antideriv
  x := "x"; body := sin trigArg
  result := add (mul (mul x (sin trigArg)) (inv trigDen))
    (mul (mul (mul (mul (mul (mul (.int (-1)) (v "b")) (v "d")) (v "n")) x) (cos trigArg))
      (inv trigDen))
  independent := ["a", "b", "c", "d", "n"]; conditions := [.ne trigDen (.int 0)]; priority := 100
  description := "Antiderivative of sin(d (a + b log(c x^n)))"
  provenance := migrated s!"{trigLog}:1" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#1"

/-- `Int[Cos[d (a + b Log[c x^n])], x] := x Cos[…]/(b^2 d^2 n^2 + 1)
+ b d n x Sin[…]/(b^2 d^2 n^2 + 1)` for `b^2 d^2 n^2 + 1 ≠ 0`. -/
def cosLog : CRule where
  id := "integration.cos_log"; legacyId := some s!"{trigLog}:2"; shape := .antideriv
  x := "x"; body := cos trigArg
  result := add (mul (mul x (cos trigArg)) (inv trigDen))
    (mul (mul (mul (mul (mul (v "b") (v "d")) (v "n")) x) (sin trigArg)) (inv trigDen))
  independent := ["a", "b", "c", "d", "n"]; conditions := [.ne trigDen (.int 0)]; priority := 110
  description := "Antiderivative of cos(d (a + b log(c x^n)))"
  provenance := migrated s!"{trigLog}:2" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#2"

/-- `(e x)^(m+1)`. -/
private abbrev ex1 : Expr := .pow (mul (v "e") x) (succ "m")
/-- `b^2 d^2 e n^2 + e (m+1)^2`. -/
private abbrev powTrigDen : Expr :=
  add (mul (mul (mul (sq (v "b")) (sq (v "d"))) (v "e")) (sq (v "n"))) (mul (v "e") (sq (succ "m")))
/-- `b^2 d^2 n^2 + (m+1)^2 ≠ 0`. -/
private abbrev powTrigCond : Cond :=
  .ne (add (mul (mul (sq (v "b")) (sq (v "d"))) (sq (v "n"))) (sq (succ "m"))) (.int 0)

/-- `Int[(e x)^m Sin[d (a + b Log[c x^n])], x]`. -/
def powSinLog : CRule where
  id := "integration.power_sin_log"; legacyId := some s!"{trigLog}:11"; shape := .antideriv
  x := "x"; body := mul (.pow (mul (v "e") x) (v "m")) (sin trigArg)
  result := add (mul (mul (mul (succ "m") ex1) (sin trigArg)) (inv powTrigDen))
    (mul (mul (mul (mul (mul (mul (.int (-1)) (v "b")) (v "d")) (v "n")) ex1) (cos trigArg))
      (inv powTrigDen))
  independent := ["a", "b", "c", "d", "e", "m", "n"]; conditions := [powTrigCond]; priority := 120
  description := "Antiderivative of (e x)^m sin(d (a + b log(c x^n)))"
  provenance := migrated s!"{trigLog}:11" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#11"

/-- `Int[(e x)^m Cos[d (a + b Log[c x^n])], x]`. -/
def powCosLog : CRule where
  id := "integration.power_cos_log"; legacyId := some s!"{trigLog}:12"; shape := .antideriv
  x := "x"; body := mul (.pow (mul (v "e") x) (v "m")) (cos trigArg)
  result := add (mul (mul (mul (succ "m") ex1) (cos trigArg)) (inv powTrigDen))
    (mul (mul (mul (mul (mul (v "b") (v "d")) (v "n")) ex1) (sin trigArg)) (inv powTrigDen))
  independent := ["a", "b", "c", "d", "e", "m", "n"]; conditions := [powTrigCond]; priority := 130
  description := "Antiderivative of (e x)^m cos(d (a + b log(c x^n)))"
  provenance := migrated s!"{trigLog}:12" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#12"

/-- v0.1 rules of the inventory outside the fragment, with the reason. -/
def notMigrated : List (String × String) := [
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:10",
    "the integrand raises a + c x^2 to the exponent 3/2; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:2 Exponentials/2.3 Miscellaneous exponentials:1",
    "the integrand F^(c (a + b x)) is a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:2 Exponentials/2.3 Miscellaneous exponentials:8",
    "the integrand F^(a + b (c + d x)) is a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:6",
    "the integrand raises a + b x + c x^2 to the exponent 3/2; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:9",
    "the integrand raises a + b x + c x^2 to the exponent 3/2; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:1",
    "the integrand F^(c (a + b x)) sin(d + e x) is a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:2",
    "the integrand F^(c (a + b x)) cos(d + e x) is a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:2 Exponentials/2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p:2",
    "the integrand contains F^(…), a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:2 Exponentials/2.3 Miscellaneous exponentials:25",
    "the integrand contains F^(…), a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:2 Exponentials/2.3 Miscellaneous exponentials:34",
    "the integrand contains F^(…), a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:2 Exponentials/2.3 Miscellaneous exponentials:43",
    "the integrand contains F^(…), a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:2 Exponentials/2.3 Miscellaneous exponentials:59",
    "the integrand contains F^(…), a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:2 Exponentials/2.3 Miscellaneous exponentials:60",
    "the integrand contains F^(…), a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:2 Exponentials/2.3 Miscellaneous exponentials:73",
    "the integrand contains F^(…), a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only")]

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem ax : ("a" : String) ≠ "x" := by decide
private theorem bx : ("b" : String) ≠ "x" := by decide
private theorem cx : ("c" : String) ≠ "x" := by decide
private theorem dx : ("d" : String) ≠ "x" := by decide
private theorem nx : ("n" : String) ≠ "x" := by decide
private theorem px : ("p" : String) ≠ "x" := by decide

private theorem toInt?_zero (I : Interp 𝕜) : I.toInt? (0 : 𝕜) = some 0 :=
  (I.toInt?_eq _ _).2 (by simp)

/-- `∫ a = a x` in any interpretation. -/
theorem constant_holds (I : Interp 𝕜) : AntiderivHolds I "x" constant.body constant.result := by
  intro env t _
  simp only [constant, Defined, eval, Function.update_self, Function.update_apply, ax, ite_false,
    and_self, Filter.eventually_true, true_and]
  exact ((hasDerivAt_id' t).const_mul (env "a")).congr_deriv (mul_one _)

theorem constant_real : constant.Holds .real :=
  antiderivHoldsUnder_nil.2 (constant_holds Interp.real)

theorem constant_complex : constant.Holds .complex :=
  antiderivHoldsUnder_nil.2 (constant_holds Interp.complex)

/-- **Counterexample.**  At `c = 0` the integrand `a (b + c x)` is defined
everywhere, but `(2 c)^(-1)` is not. -/
theorem constTimesLinear_not (I : Interp 𝕜) :
    ¬ AntiderivHolds I "x" constTimesLinear.body constTimesLinear.result := by
  refine not_antiderivHolds (fun _ => 0) 0 (Eventually.of_forall fun _ => ?_) ?_
  · simp [constTimesLinear, Defined]
  · intro h
    simp only [constTimesLinear, Defined, eval, Interp.toInt?_cast] at h
    simp at h

theorem constTimesLinear_counterexample_real : ¬ constTimesLinear.Holds .real :=
  fun h => constTimesLinear_not Interp.real (antiderivHoldsUnder_nil.1 h)

theorem constTimesLinear_counterexample_complex : ¬ constTimesLinear.Holds .complex :=
  fun h => constTimesLinear_not Interp.complex (antiderivHoldsUnder_nil.1 h)

/-- **Counterexample.**  Near `-1`, `1 · x^(-1)` is defined, but `ln(-1)` is
not (`transc1#ln` is defined on the positive reals). -/
theorem reciprocal_counterexample_real : ¬ reciprocal.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" [] reciprocal.body reciprocal.result
  rw [antiderivHoldsUnder_nil]
  refine not_antiderivHolds (fun _ => 0) (-1) ?_ ?_
  · filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℝ) ≠ 0)] with v hv
    simp only [reciprocal, Defined, eval, Interp.toInt?_cast]
    simp [Function.update_self, hv]
  · simp [reciprocal, Defined, eval, Interp.real]

/-- **Counterexample** to `∫ (a + b log(c x^n))/x`, for any interpretation in
which `ln` is defined at `1`: at `b = n = 0`, `c = 1`, the integrand is defined
near `1`, but `(2 b n)^(-1)` is not. -/
theorem logLinearOverX_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivHolds I "x" logLinearOverX.body logLinearOverX.result := by
  refine not_antiderivHolds (fun s => if s = "c" then 1 else 0) 1 ?_ ?_
  · filter_upwards [eventually_ne_nhds (one_ne_zero (α := 𝕜))] with v hv
    simp only [logLinearOverX, Defined, eval, Interp.toInt?_cast]
    simp [toInt?_zero, h1, hv]
  · intro h
    simp only [logLinearOverX, Defined, eval, Interp.toInt?_cast] at h
    simp at h

theorem logLinearOverX_counterexample_real : ¬ logLinearOverX.Holds .real :=
  fun h => logLinearOverX_not Interp.real (show (0 : ℝ) < 1 from one_pos) (antiderivHoldsUnder_nil.1 h)

theorem logLinearOverX_counterexample_complex : ¬ logLinearOverX.Holds .complex :=
  fun h => logLinearOverX_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)
    (antiderivHoldsUnder_nil.1 h)

/-- **Counterexample** to the `log log` rule, for any interpretation in which
`ln` is defined at `1`: at `a = b = n = p = 0`, `c = d = 1`, the integrand is
defined near `1`, but `n^(-1)` is not. -/
theorem logLogOverX_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivHolds I "x" logLogOverX.body logLogOverX.result := by
  refine not_antiderivHolds (fun s => if s = "c" ∨ s = "d" then 1 else 0) 1 ?_ ?_
  · filter_upwards [eventually_ne_nhds (one_ne_zero (α := 𝕜))] with v hv
    simp only [logLogOverX, Defined, eval, Interp.toInt?_cast]
    simp [toInt?_zero, h1, hv]
  · intro h
    simp only [logLogOverX, Defined, eval, Interp.toInt?_cast] at h
    simp at h

theorem logLogOverX_counterexample_real : ¬ logLogOverX.Holds .real :=
  fun h => logLogOverX_not Interp.real (show (0 : ℝ) < 1 from one_pos) (antiderivHoldsUnder_nil.1 h)

theorem logLogOverX_counterexample_complex : ¬ logLogOverX.Holds .complex :=
  fun h => logLogOverX_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)
    (antiderivHoldsUnder_nil.1 h)

/-! ### Conditional rules -/

private theorem ex : ("e" : String) ≠ "x" := by decide
private theorem mx : ("m" : String) ≠ "x" := by decide

private theorem toInt?_one (I : Interp 𝕜) : I.toInt? (1 : 𝕜) = some 1 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

/-- `∫ x^m = x^(m+1)/(m+1)` for `m ≠ -1`, in any interpretation.  The
integrand is defined only where `m` takes an integer value. -/
theorem power_holds (I : Interp 𝕜) :
    AntiderivHoldsUnder I "x" power.conditions power.body power.result := by
  intro env hc t hF
  have hm : env "m" ≠ -1 := by
    have h := hc (neMinusOne "m") (by simp [power])
    simpa [Cond.Holds, Defined, eval] using h
  rcases hk : I.toInt? (env "m") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [power, Defined, eval, mx, hk] at h
  have hmk : env "m" = (k : 𝕜) := (I.toInt?_eq _ _).1 hk
  have hk1 : I.toInt? (env "m" + 1) = some (k + 1) :=
    (I.toInt?_eq _ _).2 (by rw [hmk]; push_cast; ring)
  have hm1 : env "m" + 1 ≠ 0 := fun h => hm (by linear_combination h)
  have hD : ∀ w, Defined I (Function.update env "x" w) power.body ↔ (k < 0 → w ≠ 0) := by
    intro w
    simp [power, Defined, eval, mx, hk]
  have hDG : ∀ w, Defined I (Function.update env "x" w) power.result ↔
      (k + 1 < 0 → w ≠ 0) := by
    intro w
    simp [power, Defined, eval, mx, hk1, toInt?_neg_one, hm1]
  have hE : ∀ w, eval I (Function.update env "x" w) power.result =
      w ^ (k + 1) * (env "m" + 1)⁻¹ := by
    intro w
    simp [power, eval, mx, hk1, toInt?_neg_one]
  have hEF : eval I (Function.update env "x" t) power.body = t ^ k := by
    simp [power, eval, mx, hk]
  have ht := (hD t).1 hF.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact (hDG w).2 fun h => (hD w).1 hw (by omega)
  · have hne : t ≠ 0 ∨ 0 ≤ k + 1 := by
      by_cases h : k + 1 < 0
      · exact Or.inl (ht (by omega))
      · exact Or.inr (by omega)
    have hfun : (fun w => eval I (Function.update env "x" w) power.result) =
        fun w => w ^ (k + 1) * (env "m" + 1)⁻¹ := funext hE
    rw [hEF, hfun]
    refine ((hasDerivAt_zpow (k + 1) t hne).mul_const _).congr_deriv ?_
    have h0 : (k : 𝕜) + 1 ≠ 0 := by rw [← hmk]; exact hm1
    rw [add_sub_cancel_right, hmk]
    push_cast
    rw [mul_comm ((k : 𝕜) + 1) (t ^ k), mul_inv_cancel_right₀ h0]

theorem power_real : power.Holds .real := power_holds Interp.real

theorem power_complex : power.Holds .complex := power_holds Interp.complex

/-- **Counterexample** to `∫ (a + b x)^m`: at `a = 1`, `b = m = 0` the
integrand is defined everywhere, but `(b (m + 1))^(-1)` is not. -/
theorem linearPower_not (I : Interp 𝕜) :
    ¬ AntiderivHoldsUnder I "x" linearPower.conditions linearPower.body linearPower.result := by
  refine not_antiderivHoldsUnder (fun s => if s = "a" then 1 else 0) 0 ?_
    (Eventually.of_forall fun _ => ?_) ?_
  · simp [linearPower, Cond.Holds, Defined, eval]
  · simp [linearPower, Defined, eval, toInt?_zero]
  · intro h
    simp only [linearPower, Defined, eval, Interp.toInt?_cast] at h
    simp [toInt?_one] at h

theorem linearPower_counterexample_real : ¬ linearPower.Holds .real :=
  linearPower_not Interp.real

theorem linearPower_counterexample_complex : ¬ linearPower.Holds .complex :=
  linearPower_not Interp.complex

/-- **Counterexample** to `∫ (d x)^m (a + b log(c x^n))`: at `c = 1` and
`a = b = d = m = n = 0` the integrand is defined everywhere, but
`(d (m + 1))^(-1)` is not. -/
theorem powerLogLinear_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivHoldsUnder I "x" powerLogLinear.conditions powerLogLinear.body
      powerLogLinear.result := by
  refine not_antiderivHoldsUnder (fun s => if s = "c" then 1 else 0) 1 ?_
    (Eventually.of_forall fun _ => ?_) ?_
  · simp [powerLogLinear, Cond.Holds, Defined, eval]
  · simp [powerLogLinear, Defined, eval, toInt?_zero, h1]
  · intro h
    simp only [powerLogLinear, Defined, eval, Interp.toInt?_cast] at h
    simp [toInt?_zero, toInt?_one] at h

theorem powerLogLinear_counterexample_real : ¬ powerLogLinear.Holds .real :=
  powerLogLinear_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem powerLogLinear_counterexample_complex : ¬ powerLogLinear.Holds .complex :=
  powerLogLinear_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `∫ (e x)^m sin(d (a + b log(c x^n)))`: at `c = 1`
and the other metavariables `0`, the condition holds and the integrand is
defined everywhere, but the denominator `b^2 d^2 e n^2 + e (m+1)^2` is `0`. -/
theorem powSinLog_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivHoldsUnder I "x" powSinLog.conditions powSinLog.body powSinLog.result := by
  refine not_antiderivHoldsUnder (fun s => if s = "c" then 1 else 0) 1 ?_
    (Eventually.of_forall fun _ => ?_) ?_
  · simp [powSinLog, Cond.Holds, Defined, eval, toInt?_two]
  · simp [powSinLog, Defined, eval, toInt?_zero, h1]
  · intro h
    simp only [powSinLog, Defined, eval, Interp.toInt?_cast] at h
    simp [toInt?_zero, toInt?_one] at h

theorem powSinLog_counterexample_real : ¬ powSinLog.Holds .real :=
  powSinLog_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem powSinLog_counterexample_complex : ¬ powSinLog.Holds .complex :=
  powSinLog_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `∫ (e x)^m cos(d (a + b log(c x^n)))`, as for
`powSinLog`. -/
theorem powCosLog_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivHoldsUnder I "x" powCosLog.conditions powCosLog.body powCosLog.result := by
  refine not_antiderivHoldsUnder (fun s => if s = "c" then 1 else 0) 1 ?_
    (Eventually.of_forall fun _ => ?_) ?_
  · simp [powCosLog, Cond.Holds, Defined, eval, toInt?_two]
  · simp [powCosLog, Defined, eval, toInt?_zero, h1]
  · intro h
    simp only [powCosLog, Defined, eval, Interp.toInt?_cast] at h
    simp [toInt?_zero, toInt?_one] at h

theorem powCosLog_counterexample_real : ¬ powCosLog.Holds .real :=
  powCosLog_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem powCosLog_counterexample_complex : ¬ powCosLog.Holds .complex :=
  powCosLog_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

end Proofs

/-- The integrand of `logMonomial` is defined exactly where `c x^k > 0`, `k`
the integer value of `n`, and `x ≠ 0` if `k < 0`. -/
private theorem logMonomial_defined (env : String → ℝ) {k : ℤ}
    (hk : intValue? (env "n") = some k) (w : ℝ) :
    Defined Interp.real (Function.update env "x" w) logMonomial.body ↔
      (k < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ k := by
  simp [logMonomial, Defined, eval, Interp.real, cx, nx, hk]

theorem logMonomial_real : logMonomial.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" [] logMonomial.body logMonomial.result
  rw [antiderivHoldsUnder_nil]
  intro env t hF
  obtain ⟨k, hk⟩ : ∃ k, intValue? (env "n") = some k := by
    have h := hF.self_of_nhds
    simp only [logMonomial, Defined, eval, Interp.real] at h
    obtain ⟨⟨-, -, -, k, hk, -⟩, -⟩ := h
    simp only [Function.update_apply, nx, ite_false] at hk
    exact ⟨k, hk⟩
  have hn : env "n" = k := (intValue?_eq _ _).1 hk
  have hD := logMonomial_defined env hk
  have hDG : ∀ w, Defined Interp.real (Function.update env "x" w) logMonomial.result ↔
      (k < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ k := by
    intro w
    rw [← hD w]
    simp [logMonomial, Defined]
  have hE : ∀ w, eval Interp.real (Function.update env "x" w) logMonomial.result =
      w * Real.log (env "c" * w ^ k) + -1 * env "n" * w := by
    intro w
    simp [logMonomial, eval, Interp.real, cx, nx, hk]
  have hEF : eval Interp.real (Function.update env "x" t) logMonomial.body =
      Real.log (env "c" * t ^ k) := by
    simp [logMonomial, eval, Interp.real, cx, nx, hk]
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact (hDG w).2 ((hD w).1 hw)
  · obtain ⟨hk0, hpos⟩ := (hD t).1 hF.self_of_nhds
    have hne : t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) logMonomial.result) =
        fun w => w * Real.log (env "c" * w ^ k) + -1 * env "n" * w := funext hE
    rw [hEF, hfun]
    have hlog := ((hasDerivAt_zpow k t hne).const_mul (env "c")).log hpos.ne'
    have h := ((hasDerivAt_id' t).mul hlog).add ((hasDerivAt_id' t).const_mul (-1 * env "n"))
    refine h.congr_deriv ?_
    rw [hn]
    rcases eq_or_ne k 0 with rfl | hk1
    · simp
    · have ht : t ≠ 0 := by
        rcases hne with h | h
        · exact h
        · intro h0
          subst h0
          rw [zero_zpow k hk1, mul_zero] at hpos
          exact lt_irrefl 0 hpos
      have hc : env "c" ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hpos
        exact lt_irrefl 0 hpos
      rw [zpow_sub_one₀ ht]
      field_simp
      ring

private theorem two_real : intValue? (2 : ℝ) = some 2 := by
  simpa using intValue?_intCast (α := ℝ) 2

private theorem negOne_real : intValue? (-1 : ℝ) = some (-1) := by
  simpa using intValue?_intCast (α := ℝ) (-1)

theorem sinLog_real : sinLog.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" sinLog.conditions sinLog.body sinLog.result
  intro env _ t hF
  rcases hk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [sinLog, Defined, eval, Interp.real, nx, hk] at h
  have hn : env "n" = k := (intValue?_eq _ _).1 hk
  have hK : env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + 1 ≠ 0 := by positivity
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) sinLog.body ↔
      (k < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ k := by
    intro w
    simp [sinLog, Defined, eval, Interp.real, cx, nx, hk]
  have hDG : ∀ w, Defined Interp.real (Function.update env "x" w) sinLog.body →
      Defined Interp.real (Function.update env "x" w) sinLog.result := by
    intro w hw
    have h := (hD w).1 hw
    simp [sinLog, Defined, eval, Interp.real, bx, cx, dx, nx, hk, two_real, negOne_real,
      hK]
    exact h
  have hE : ∀ w, eval Interp.real (Function.update env "x" w) sinLog.result =
      w * Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ k))) *
          (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + 1)⁻¹ +
        -1 * env "b" * env "d" * env "n" * w *
          Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ k))) *
          (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + 1)⁻¹ := by
    intro w
    simp [sinLog, eval, Interp.real, ax, bx, cx, dx, nx, hk, two_real, negOne_real]
  have hEF : eval Interp.real (Function.update env "x" t) sinLog.body =
      Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ k))) := by
    simp [sinLog, eval, Interp.real, ax, bx, cx, dx, nx, hk]
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w hw
  · obtain ⟨hk0, hpos⟩ := (hD t).1 hF.self_of_nhds
    have hne : t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    rw [hEF, funext hE]
    have hlog := ((hasDerivAt_zpow k t hne).const_mul (env "c")).log hpos.ne'
    have hU := ((hlog.const_mul (env "b")).const_add (env "a")).const_mul (env "d")
    have h1 := ((hasDerivAt_id' t).mul hU.sin).mul_const
      (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + 1)⁻¹
    have h2 := (((hasDerivAt_id' t).const_mul (-1 * env "b" * env "d" * env "n")).mul
      hU.cos).mul_const (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + 1)⁻¹
    refine (h1.add h2).congr_deriv ?_
    rw [hn] at hK ⊢
    rcases eq_or_ne k 0 with rfl | hk1
    · simp
    · have ht : t ≠ 0 := by
        rcases hne with h | h
        · exact h
        · intro h0
          subst h0
          rw [zero_zpow k hk1, mul_zero] at hpos
          exact lt_irrefl 0 hpos
      have hc : env "c" ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hpos
        exact lt_irrefl 0 hpos
      have hz : t ^ k ≠ 0 := zpow_ne_zero k ht
      rw [zpow_sub_one₀ ht]
      field_simp
      ring

theorem cosLog_real : cosLog.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" cosLog.conditions cosLog.body cosLog.result
  intro env _ t hF
  rcases hk : intValue? (env "n") with _ | k
  · exfalso
    have h := hF.self_of_nhds
    simp [cosLog, Defined, eval, Interp.real, nx, hk] at h
  have hn : env "n" = k := (intValue?_eq _ _).1 hk
  have hK : env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + 1 ≠ 0 := by positivity
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) cosLog.body ↔
      (k < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ k := by
    intro w
    simp [cosLog, Defined, eval, Interp.real, cx, nx, hk]
  have hDG : ∀ w, Defined Interp.real (Function.update env "x" w) cosLog.body →
      Defined Interp.real (Function.update env "x" w) cosLog.result := by
    intro w hw
    have h := (hD w).1 hw
    simp [cosLog, Defined, eval, Interp.real, bx, cx, dx, nx, hk, two_real, negOne_real,
      hK]
    exact h
  have hE : ∀ w, eval Interp.real (Function.update env "x" w) cosLog.result =
      w * Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ k))) *
          (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + 1)⁻¹ +
        env "b" * env "d" * env "n" * w *
          Real.sin (env "d" * (env "a" + env "b" * Real.log (env "c" * w ^ k))) *
          (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + 1)⁻¹ := by
    intro w
    simp [cosLog, eval, Interp.real, ax, bx, cx, dx, nx, hk, two_real, negOne_real]
  have hEF : eval Interp.real (Function.update env "x" t) cosLog.body =
      Real.cos (env "d" * (env "a" + env "b" * Real.log (env "c" * t ^ k))) := by
    simp [cosLog, eval, Interp.real, ax, bx, cx, dx, nx, hk]
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact hDG w hw
  · obtain ⟨hk0, hpos⟩ := (hD t).1 hF.self_of_nhds
    have hne : t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    rw [hEF, funext hE]
    have hlog := ((hasDerivAt_zpow k t hne).const_mul (env "c")).log hpos.ne'
    have hU := ((hlog.const_mul (env "b")).const_add (env "a")).const_mul (env "d")
    have h1 := ((hasDerivAt_id' t).mul hU.cos).mul_const
      (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + 1)⁻¹
    have h2 := (((hasDerivAt_id' t).const_mul (env "b" * env "d" * env "n")).mul
      hU.sin).mul_const (env "b" ^ 2 * env "d" ^ 2 * env "n" ^ 2 + 1)⁻¹
    refine (h1.add h2).congr_deriv ?_
    rw [hn] at hK ⊢
    rcases eq_or_ne k 0 with rfl | hk1
    · simp
    · have ht : t ≠ 0 := by
        rcases hne with h | h
        · exact h
        · intro h0
          subst h0
          rw [zero_zpow k hk1, mul_zero] at hpos
          exact lt_irrefl 0 hpos
      have hc : env "c" ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hpos
        exact lt_irrefl 0 hpos
      have hz : t ^ k ≠ 0 := zpow_ne_zero k ht
      rw [zpow_sub_one₀ ht]
      field_simp
      ring

private def lnComplexFinding : String :=
  "complex: not proved; ln is defined for z ≠ 0, but the principal logarithm is discontinuous across the negative real axis (its branch cut), where the integrand is defined, so the statement is not expected to hold there."

private def optionalFinding (vars : String) (plural : Bool := true) : String :=
  if plural then
    s!"matching: the optional wildcards {vars} of the v0.1 pattern are ordinary metavariables; the v1 rule does not match the instances with RUBI's default values."
  else
    s!"matching: the optional wildcard {vars} of the v0.1 pattern is an ordinary metavariable; the v1 rule does not match the instances with RUBI's default value."

private def neqFinding (cond : String) : String :=
  s!"conditions: RUBI's {cond} becomes a relation1#neq condition, read semantically (both sides defined, values different); Mathematica's NeQ tests that the difference is not possibly zero. The reference rewriter does not apply conditional rules."

private def integerFinding (m : String) : String :=
  s!"exponent: the fragment interprets arith1#power for integer exponents only, so the statement covers the integer values of {m}; for other values the integrand is undefined."

private def condFinding (cs : String) : String :=
  s!"conditions: RUBI's {cs} become OSR v1 conditions (relation1#neq, relation1#gt, set1#in with setname1#Z), read semantically on defined values."

private def recFinding : String :=
  "residual integrals: the result contains Int[…], exported as int(λx. H)(x) (the calculus1#int FMP form); the statement holds for every choice of antiderivatives of the residual integrands. The reference rewriter does not apply this rule."

/-- The Integration catalogue, in v0.1 file order. -/
def catalog : List CEntry := [
  { rule := reciprocal, ruleDecl := ``reciprocal, proofs := [], unproved := [.complex],
    counterexamples := [(.real, ``reciprocal_counterexample_real)],
    findings := [
      "counterexample: near x = -1 the integrand 1 · x^(-1) is defined, but ln(-1) is not, since transc1#ln is defined on the positive reals (Lean theorem reciprocal_counterexample_real). RUBI reads Log as the complex logarithm; a real antiderivative is ln|x|, which is outside the fragment.",
      lnComplexFinding] },
  { rule := logMonomial, ruleDecl := ``logMonomial,
    proofs := [(.real, ``logMonomial_real)], unproved := [.complex],
    findings := [
      "real: n must take an integer value, since the fragment interprets arith1#power for integer exponents only; the statement covers every point near which c x^n > 0.",
      lnComplexFinding, optionalFinding "c. and n."] },
  { rule := logLinearOverX, ruleDecl := ``logLinearOverX, proofs := [],
    counterexamples := [(.real, ``logLinearOverX_counterexample_real),
      (.complex, ``logLinearOverX_counterexample_complex)],
    findings := [
      "counterexample: at b = n = 0 and c = 1 the integrand is defined near x = 1, but (2 b n)^(-1) is not (Lean theorems logLinearOverX_counterexample_real and logLinearOverX_counterexample_complex). The v0.1 rule has only FreeQ conditions. In Mathematica an integrand with a literal b = 0 is simplified before matching, so this instance does not arise there; OSR v1 matching performs no such evaluation. The rule needs the conditions b ≠ 0 and n ≠ 0, which this migration does not add.",
      optionalFinding "a., b., c. and n."] },
  { rule := logLogOverX, ruleDecl := ``logLogOverX, proofs := [],
    counterexamples := [(.real, ``logLogOverX_counterexample_real),
      (.complex, ``logLogOverX_counterexample_complex)],
    findings := [
      "counterexample: at a = b = n = p = 0 and c = d = 1 the integrand is defined near x = 1, but n^(-1) is not (Lean theorems logLogOverX_counterexample_real and logLogOverX_counterexample_complex). The rule needs n ≠ 0, which this migration does not add.",
      "real: even with n ≠ 0, ln x in the result is undefined for x < 0, where the integrand can be defined (n even, d > 0); not proved.",
      optionalFinding "a., b., c., d., n. and p."] },
  { rule := constant, ruleDecl := ``constant,
    proofs := [(.real, ``constant_real), (.complex, ``constant_complex)] },
  { rule := constTimesLinear, ruleDecl := ``constTimesLinear, proofs := [],
    counterexamples := [(.real, ``constTimesLinear_counterexample_real),
      (.complex, ``constTimesLinear_counterexample_complex)],
    findings := [
      "counterexample: at c = 0 the integrand a (b + c x) is defined everywhere, but (2 c)^(-1) is not (Lean theorems constTimesLinear_counterexample_real and constTimesLinear_counterexample_complex). The rule needs c ≠ 0, which this migration does not add.",
      optionalFinding "c." false] },
  { rule := power, ruleDecl := ``power,
    proofs := [(.real, ``power_real), (.complex, ``power_complex)],
    findings := [integerFinding "m", neqFinding "NeQ[m, -1]", optionalFinding "m." false] },
  { rule := linearPower, ruleDecl := ``linearPower, proofs := [],
    counterexamples := [(.real, ``linearPower_counterexample_real),
      (.complex, ``linearPower_counterexample_complex)],
    findings := [
      "counterexample: at a = 1 and b = m = 0 the condition m ≠ -1 holds and the integrand (a + b x)^m is defined everywhere, but (b (m + 1))^(-1) is not (Lean theorems linearPower_counterexample_real and linearPower_counterexample_complex). The rule needs b ≠ 0, which this migration does not add.",
      neqFinding "NeQ[m, -1]", optionalFinding "a. and b."] },
  { rule := powerLogLinear, ruleDecl := ``powerLogLinear, proofs := [],
    counterexamples := [(.real, ``powerLogLinear_counterexample_real),
      (.complex, ``powerLogLinear_counterexample_complex)],
    findings := [
      "counterexample: at c = 1 and a = b = d = m = n = 0 the condition m ≠ -1 holds and the integrand is defined everywhere, but (d (m + 1))^(-1) is not (Lean theorems powerLogLinear_counterexample_real and powerLogLinear_counterexample_complex). The rule needs d ≠ 0, which this migration does not add.",
      neqFinding "NeQ[m, -1]", optionalFinding "a., b., c., d., m. and n."] },
  { rule := sinLog, ruleDecl := ``sinLog,
    proofs := [(.real, ``sinLog_real)], unproved := [.complex],
    findings := [
      "real: the condition b^2 d^2 n^2 + 1 ≠ 0 always holds; n must take an integer value, and the statement covers every point near which c x^n > 0.",
      lnComplexFinding, neqFinding "NeQ[b^2 d^2 n^2 + 1, 0]",
      optionalFinding "a., b., c., d. and n."] },
  { rule := cosLog, ruleDecl := ``cosLog,
    proofs := [(.real, ``cosLog_real)], unproved := [.complex],
    findings := [
      "real: the condition b^2 d^2 n^2 + 1 ≠ 0 always holds; n must take an integer value, and the statement covers every point near which c x^n > 0.",
      lnComplexFinding, neqFinding "NeQ[b^2 d^2 n^2 + 1, 0]",
      optionalFinding "a., b., c., d. and n."] },
  { rule := powSinLog, ruleDecl := ``powSinLog, proofs := [],
    counterexamples := [(.real, ``powSinLog_counterexample_real),
      (.complex, ``powSinLog_counterexample_complex)],
    findings := [
      "counterexample: at c = 1 and the other metavariables 0 the condition b^2 d^2 n^2 + (m + 1)^2 ≠ 0 holds and the integrand is defined everywhere, but the denominator b^2 d^2 e n^2 + e (m + 1)^2 is 0 (Lean theorems powSinLog_counterexample_real and powSinLog_counterexample_complex). The rule needs e ≠ 0, which this migration does not add.",
      neqFinding "NeQ[b^2 d^2 n^2 + (m + 1)^2, 0]",
      optionalFinding "a., b., c., d., e., m. and n."] },
  { rule := powCosLog, ruleDecl := ``powCosLog, proofs := [],
    counterexamples := [(.real, ``powCosLog_counterexample_real),
      (.complex, ``powCosLog_counterexample_complex)],
    findings := [
      "counterexample: at c = 1 and the other metavariables 0 the condition b^2 d^2 n^2 + (m + 1)^2 ≠ 0 holds and the integrand is defined everywhere, but the denominator b^2 d^2 e n^2 + e (m + 1)^2 is 0 (Lean theorems powCosLog_counterexample_real and powCosLog_counterexample_complex). The rule needs e ≠ 0, which this migration does not add.",
      neqFinding "NeQ[b^2 d^2 n^2 + (m + 1)^2, 0]",
      optionalFinding "a., b., c., d., e., m. and n."] },
  { rule := sinAddSq, ruleDecl := ``sinAddSq,
    proofs := [(.real, ``sinAddSq_real), (.complex, ``sinAddSq_complex)],
    findings := [recFinding, optionalFinding "d., e. and f."] },
  { rule := cosAddSq, ruleDecl := ``cosAddSq,
    proofs := [(.real, ``cosAddSq_real), (.complex, ``cosAddSq_complex)],
    findings := [recFinding, optionalFinding "d., e. and f."] },
  { rule := sinAddPowOverX, ruleDecl := ``sinAddPowOverX,
    proofs := [(.real, ``sinAddPowOverX_real), (.complex, ``sinAddPowOverX_complex)],
    findings := [recFinding, integerFinding "n", optionalFinding "d." false] },
  { rule := cosAddPowOverX, ruleDecl := ``cosAddPowOverX,
    proofs := [(.real, ``cosAddPowOverX_real), (.complex, ``cosAddPowOverX_complex)],
    findings := [recFinding, integerFinding "n", optionalFinding "d." false] },
  { rule := powSinSq, ruleDecl := ``powSinSq,
    proofs := [(.real, ``powSinSq_real), (.complex, ``powSinSq_complex)],
    findings := [recFinding, integerFinding "m and n", optionalFinding "m., a. and b."] },
  { rule := powCosSq, ruleDecl := ``powCosSq,
    proofs := [(.real, ``powCosSq_real), (.complex, ``powCosSq_complex)],
    findings := [recFinding, integerFinding "m and n", optionalFinding "m., a. and b."] },
  { rule := logPowLog, ruleDecl := ``logPowLog, proofs := [],
    counterexamples := [(.real, ``logPowLog_counterexample_real),
      (.complex, ``logPowLog_counterexample_complex)],
    findings := [
      "counterexample: at c = d = 1 and n = p = 0 the integrand log(c log(d x^n)^p) = log 1 is defined everywhere, but the residual integrand 1/log(d x^n) = 1/log 1 is not (Lean theorems logPowLog_counterexample_real and logPowLog_counterexample_complex). Its coefficient -n p vanishes there, but the residual integral is still undefined. The rule needs log(d x^n) ≠ 0 wherever the integrand is defined, which p ≠ 0 ensures; this migration does not add it.",
      recFinding, optionalFinding "c., d., n. and p."] },
  { rule := logLinPow, ruleDecl := ``logLinPow,
    proofs := [(.real, ``logLinPow_real)], unproved := [.complex],
    findings := [
      "conditions: RUBI's GtQ[p, 0] becomes p > 0 (relation1#gt) and IntegerQ[2 p] becomes 2 p ∈ ℤ (set1#in, setname1#Z); the fragment interprets arith1#power for integer exponents only, so the statement covers the integer values of p.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's GtQ[p, 0] only holds for a numeric p, so the v1 rule declares p independent of x, as the statement requires.",
      lnComplexFinding, recFinding, optionalFinding "a., b., c., n. and p."] },
  { rule := sinXLog, ruleDecl := ``sinXLog, proofs := [],
    counterexamples := [(.real, ``sinXLog_counterexample_real),
      (.complex, ``sinXLog_counterexample_complex)],
    findings := [
      "counterexample: at a = 0 and b = 1 the integrand is defined near x = 1, but a^(-1) is not (Lean theorems sinXLog_counterexample_real and sinXLog_counterexample_complex). The rule needs a ≠ 0, which this migration does not add.",
      recFinding, optionalFinding "a. and b."] },
  { rule := cosXLog, ruleDecl := ``cosXLog, proofs := [],
    counterexamples := [(.real, ``cosXLog_counterexample_real),
      (.complex, ``cosXLog_counterexample_complex)],
    findings := [
      "counterexample: at a = 0 and b = 1 the integrand is defined near x = 1, but a^(-1) is not (Lean theorems cosXLog_counterexample_real and cosXLog_counterexample_complex). The rule needs a ≠ 0, which this migration does not add.",
      recFinding, optionalFinding "a. and b."] },
  { rule := linearQuadPow, ruleDecl := ``linearQuadPow, proofs := [],
    counterexamples := [(.real, ``linearQuadPow_counterexample_real),
      (.complex, ``linearQuadPow_counterexample_complex)],
    findings := [
      "counterexample: at a = 1 and the other metavariables 0 the condition p ≠ -1 holds and the integrand is defined everywhere, but (2 c (p + 1))^(-1) is not (Lean theorems linearQuadPow_counterexample_real and linearQuadPow_counterexample_complex). The rule needs c ≠ 0, which this migration does not add.",
      neqFinding "NeQ[p, -1]", recFinding, optionalFinding "e., c. and p."] },
  { rule := pfLinear, ruleDecl := ``pfLinear,
    proofs := [(.real, ``pfLinear_real), (.complex, ``pfLinear_complex)],
    findings := [neqFinding "NeQ[b c - a d, 0]", recFinding, optionalFinding "a., b., c. and d."] },
  { rule := pfPower, ruleDecl := ``pfPower,
    proofs := [(.real, ``pfPower_real), (.complex, ``pfPower_complex)],
    findings := [neqFinding "NeQ[b c - a d, 0]", integerFinding "n", recFinding, optionalFinding "b. and d."] },
  { rule := splitBinomial, ruleDecl := ``splitBinomial,
    proofs := [(.real, ``splitBinomial_real), (.complex, ``splitBinomial_complex)],
    findings := [integerFinding "n, p and q", recFinding, optionalFinding "b., d., f., p. and q."] },
  { rule := splitQuadratic, ruleDecl := ``splitQuadratic,
    proofs := [(.real, ``splitQuadratic_real), (.complex, ``splitQuadratic_complex)],
    findings := [integerFinding "p and q", recFinding, optionalFinding "c., f. and h."] },
  { rule := linSinQuad, ruleDecl := ``linSinQuad, proofs := [],
    counterexamples := [(.real, ``linSinQuad_counterexample_real),
      (.complex, ``linSinQuad_counterexample_complex)],
    findings := [
      "counterexample: at b = e = 1 and the other metavariables 0 the condition 2 c d - b e ≠ 0 holds and the integrand is defined everywhere, but (2 c)^(-1) is not (Lean theorems linSinQuad_counterexample_real and linSinQuad_counterexample_complex). The rule needs c ≠ 0, which this migration does not add.",
      neqFinding "NeQ[2 c d - b e, 0]",
      recFinding, optionalFinding "a., b., c., d. and e."] },
  { rule := linCosQuad, ruleDecl := ``linCosQuad, proofs := [],
    counterexamples := [(.real, ``linCosQuad_counterexample_real),
      (.complex, ``linCosQuad_counterexample_complex)],
    findings := [
      "counterexample: at b = e = 1 and the other metavariables 0 the condition 2 c d - b e ≠ 0 holds and the integrand is defined everywhere, but (2 c)^(-1) is not (Lean theorems linCosQuad_counterexample_real and linCosQuad_counterexample_complex). The rule needs c ≠ 0, which this migration does not add.",
      neqFinding "NeQ[2 c d - b e, 0]",
      recFinding, optionalFinding "a., b., c., d. and e."] },
  { rule := linTrinomPow, ruleDecl := ``linTrinomPow, proofs := [],
    counterexamples := [(.real, ``linTrinomPow_counterexample_real),
      (.complex, ``linTrinomPow_counterexample_complex)],
    findings := [
      "counterexample: at b = e = 1 and the other metavariables 0 the conditions 2 c d - b e ≠ 0 and p ≠ -1 hold and the integrand is defined everywhere, but (2 c (p + 1))^(-1) is not (Lean theorems linTrinomPow_counterexample_real and linTrinomPow_counterexample_complex). The rule needs c ≠ 0, which this migration does not add.",
      neqFinding "NeQ[2 c d - b e, 0] and NeQ[p, -1]",
      recFinding, optionalFinding "a., b., c., d. and e."] },
  { rule := prodOverTrinom, ruleDecl := ``prodOverTrinom, proofs := [],
    counterexamples := [(.real, ``prodOverTrinom_counterexample_real),
      (.complex, ``prodOverTrinom_counterexample_complex)],
    findings := [
      "counterexample: at a = b = 1 and the other metavariables 0 the condition b^2 - 4 a c ≠ 0 holds and the integrand is defined near x = 0, but c^(-1) is not (Lean theorems prodOverTrinom_counterexample_real and prodOverTrinom_counterexample_complex). The rule needs c ≠ 0, which this migration does not add.",
      neqFinding "NeQ[b^2 - 4 a c, 0]",
      recFinding, optionalFinding "a., b., c., d., e. and g."] },
  { rule := prodOverQuad, ruleDecl := ``prodOverQuad, proofs := [],
    counterexamples := [(.real, ``prodOverQuad_counterexample_real),
      (.complex, ``prodOverQuad_counterexample_complex)],
    findings := [
      "counterexample: at a = 1 and the other metavariables 0 the integrand is defined everywhere, but c^(-1) is not (Lean theorems prodOverQuad_counterexample_real and prodOverQuad_counterexample_complex). The rule needs c ≠ 0, which this migration does not add.",
      recFinding, optionalFinding "c., d., e. and g."] },
  { rule := powerRatio, ruleDecl := ``powerRatio, proofs := [],
    counterexamples := [(.real, ``powerRatio_counterexample_real),
      (.complex, ``powerRatio_counterexample_complex)],
    findings := [
      "counterexample: at c = 1 and the other metavariables 0 the integrand is defined everywhere, but d^(-1) is not (Lean theorems powerRatio_counterexample_real and powerRatio_counterexample_complex). The rule needs d ≠ 0, which this migration does not add.",
      recFinding, optionalFinding "b., d. and f."] },
  { rule := logPowBinom, ruleDecl := ``logPowBinom, proofs := [],
    counterexamples := [(.real, ``logPowBinom_counterexample_real),
      (.complex, ``logPowBinom_counterexample_complex)],
    findings := [
      "counterexample: at c = 1 and d = e = n = p = 0 the integrand log 1 is defined everywhere, but the residual integrand x^n/(d + e x^n) is not; its coefficient -e n p vanishes there (Lean theorems logPowBinom_counterexample_real and logPowBinom_counterexample_complex). The rule needs d + e x^n ≠ 0 wherever the integrand is defined, which p ≠ 0 ensures, which this migration does not add.",
      recFinding, optionalFinding "c., e. and p."] },
  { rule := pfLinQuad, ruleDecl := ``pfLinQuad,
    proofs := [(.real, ``pfLinQuad_real), (.complex, ``pfLinQuad_complex)],
    findings := [neqFinding "NeQ[c d^2 + a e^2, 0]", recFinding, optionalFinding "e. and c."] },
  { rule := pfLinTrinom, ruleDecl := ``pfLinTrinom,
    proofs := [(.real, ``pfLinTrinom_real), (.complex, ``pfLinTrinom_complex)],
    findings := [neqFinding "NeQ[b^2 - 4 a c, 0], NeQ[c d^2 - b d e + a e^2, 0] and NeQ[2 c d - b e, 0]", recFinding, optionalFinding "d., e., a., b. and c."] },
  { rule := pfPowerWeighted, ruleDecl := ``pfPowerWeighted,
    proofs := [(.real, ``pfPowerWeighted_real), (.complex, ``pfPowerWeighted_complex)],
    findings := [neqFinding "NeQ[b c - a d, 0]", integerFinding "m and n", recFinding, optionalFinding "e., m., b. and d."] },
  { rule := sinCosDouble, ruleDecl := ``sinCosDouble,
    proofs := [(.real, ``sinCosDouble_real), (.complex, ``sinCosDouble_complex)],
    findings := [integerFinding "m and n", recFinding, optionalFinding "e., f., m., b., c., d. and n."] },
  { rule := pfGeneral, ruleDecl := ``pfGeneral, proofs := [],
    counterexamples := [(.real, ``pfGeneral_counterexample_real),
      (.complex, ``pfGeneral_counterexample_complex)],
    findings := [
      "counterexample: at a = c = 1 and the other metavariables 0 the integrand is defined everywhere, but b c - a d = 0 and (b c - a d)^(-1) is not defined (Lean theorems pfGeneral_counterexample_real and pfGeneral_counterexample_complex). The rule needs b c - a d ≠ 0, which this migration does not add.",
      recFinding, optionalFinding "b. and d."] },
  { rule := linOverLin, ruleDecl := ``linOverLin, proofs := [],
    counterexamples := [(.real, ``linOverLin_counterexample_real),
      (.complex, ``linOverLin_counterexample_complex)],
    findings := [
      "counterexample: at a = 1 and the other metavariables 0 the integrand is defined everywhere, but b^(-1) is not (Lean theorems linOverLin_counterexample_real and linOverLin_counterexample_complex). The rule needs b ≠ 0, which this migration does not add.",
      recFinding, optionalFinding "c., d., e., f., g., h., a. and b."] },
  { rule := sinTrinomSq, ruleDecl := ``sinTrinomSq, proofs := [],
    counterexamples := [(.real, ``sinTrinomSq_counterexample_real),
      (.complex, ``sinTrinomSq_counterexample_complex)],
    findings := [
      "counterexample: at b = 1 and a = c = 0 the condition b^2 - 4 a c ≠ 0 holds and the integrand is defined everywhere, but the residual integrand sin((b + 2 c x)^2/(4 c)) is not (Lean theorems sinTrinomSq_counterexample_real and sinTrinomSq_counterexample_complex). The rule needs c ≠ 0, which this migration does not add.",
      neqFinding "NeQ[b^2 - 4 a c, 0]",
      recFinding, optionalFinding "a., b. and c."] },
  { rule := cosTrinomSq, ruleDecl := ``cosTrinomSq, proofs := [],
    counterexamples := [(.real, ``cosTrinomSq_counterexample_real),
      (.complex, ``cosTrinomSq_counterexample_complex)],
    findings := [
      "counterexample: at b = 1 and a = c = 0 the condition b^2 - 4 a c ≠ 0 holds and the integrand is defined everywhere, but the residual integrand cos((b + 2 c x)^2/(4 c)) is not (Lean theorems cosTrinomSq_counterexample_real and cosTrinomSq_counterexample_complex). The rule needs c ≠ 0, which this migration does not add.",
      neqFinding "NeQ[b^2 - 4 a c, 0]",
      recFinding, optionalFinding "a., b. and c."] },
  { rule := binomRatio, ruleDecl := ``binomRatio, proofs := [],
    counterexamples := [(.real, ``binomRatio_counterexample_real),
      (.complex, ``binomRatio_counterexample_complex)],
    findings := [
      "counterexample: at b = c = 1, n = -1 and a = d = 0 the conditions b c - a d ≠ 0 and n < 0 hold and the integrand is defined near x = 1, but a^(-1) is not (Lean theorems binomRatio_counterexample_real and binomRatio_counterexample_complex). The rule needs a ≠ 0, which this migration does not add.",
      neqFinding "NeQ[b c - a d, 0]",
      "conditions: RUBI's LtQ[n, 0] becomes 0 > n (relation1#gt).",
      recFinding, optionalFinding "d. and b."] },
  { rule := logLogWeighted, ruleDecl := ``logLogWeighted, proofs := [],
    counterexamples := [(.real, ``logLogWeighted_counterexample_real),
      (.complex, ``logLogWeighted_counterexample_complex)],
    findings := [
      "counterexample: at c = d = 1 and the other metavariables 0 the condition m ≠ -1 holds and the integrand is defined everywhere, but the residual integrand (e x)^m/log(d x^n) is not, and neither is (e (m + 1))^(-1) (Lean theorems logLogWeighted_counterexample_real and logLogWeighted_counterexample_complex). The rule needs e ≠ 0 and log(d x^n) ≠ 0 wherever the integrand is defined, which this migration does not add.",
      neqFinding "NeQ[m, -1]",
      recFinding, optionalFinding "e., m., a., b., c., d., n. and p."] },
  { rule := linTwoPow, ruleDecl := ``linTwoPow, proofs := [],
    counterexamples := [(.real, ``linTwoPow_counterexample_real),
      (.complex, ``linTwoPow_counterexample_complex)],
    findings := [
      "counterexample: at c = 1 and the other metavariables 0 the condition n + p + 2 ≠ 0 holds and the integrand is defined everywhere, but (d f (n + p + 2))^(-1) is not (Lean theorems linTwoPow_counterexample_real and linTwoPow_counterexample_complex). The rule needs d ≠ 0 and f ≠ 0, which this migration does not add.",
      neqFinding "NeQ[n + p + 2, 0]",
      recFinding, optionalFinding "a., b., c., d., n., e., f. and p."] },
  { rule := logBinWeighted, ruleDecl := ``logBinWeighted, proofs := [],
    counterexamples := [(.real, ``logBinWeighted_counterexample_real),
      (.complex, ``logBinWeighted_counterexample_complex)],
    findings := [
      "counterexample: at c = 1 and the other metavariables 0 the condition m ≠ -1 holds and the integrand log 1 is defined everywhere, but the residual integrand x^(n-1) (f x)^(m+1)/(d + e x^n) is not, and neither is (f (m + 1))^(-1) (Lean theorems logBinWeighted_counterexample_real and logBinWeighted_counterexample_complex). The rule needs f ≠ 0 and d + e x^n ≠ 0 wherever the integrand is defined, which this migration does not add.",
      neqFinding "NeQ[m, -1]",
      recFinding, optionalFinding "f., m., a., b., c., e. and p."] },
  { rule := binomPowLin, ruleDecl := ``binomPowLin, proofs := [],
    counterexamples := [(.real, ``binomPowLin_counterexample_real),
      (.complex, ``binomPowLin_counterexample_complex)],
    findings := [
      "counterexample: at a = d = e = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but (b e (m + n (p + 1) + 1))^(-1) is not (Lean theorems binomPowLin_counterexample_real and binomPowLin_counterexample_complex). The rule needs needs b ≠ 0 and e ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; NeQ[Add[m, Multiply[n, Add[p, 1]], 1], 0]", optionalFinding "e., m., b., p. and d."] },
  { rule := logPowOverSq, ruleDecl := ``logPowOverSq, proofs := [],
    counterexamples := [(.real, ``logPowOverSq_counterexample_real),
      (.complex, ``logPowOverSq_counterexample_complex)],
    findings := [
      "counterexample: at c = e = p = 1 and the other metavariables 0 the condition p > 0 holds and the integrand is defined near x = 1, but (d (d + e x))^(-1) is not (Lean theorems logPowOverSq_counterexample_real and logPowOverSq_counterexample_complex). The rule needs d ≠ 0, which this migration does not add.",
      recFinding, condFinding "GtQ[p, 0]", optionalFinding "a., b., c., n., p. and e."] },
  { rule := powLogRatio, ruleDecl := ``powLogRatio, proofs := [],
    counterexamples := [(.real, ``powLogRatio_counterexample_real),
      (.complex, ``powLogRatio_counterexample_complex)],
    findings := [
      "counterexample: at b = c = e = f = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but (g (m + 1))^(-1) is not (Lean theorems powLogRatio_counterexample_real and powLogRatio_counterexample_complex). The rule needs g ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; NeQ[m, -1]; NeQ[m, -2]", optionalFinding "f., g., m., A., B., e., a., b., c., d. and n."] },
  { rule := powLogProduct, ruleDecl := ``powLogProduct, proofs := [],
    counterexamples := [(.real, ``powLogProduct_counterexample_real),
      (.complex, ``powLogProduct_counterexample_complex)],
    findings := [
      "counterexample: at b = c = e = f = g = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but (h (m + 1))^(-1) is not (Lean theorems powLogProduct_counterexample_real and powLogProduct_counterexample_complex). The rule needs h ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; NeQ[m, -1]", optionalFinding "g., h., m., e., f., a., b., p., c., d., q. and r."] },
  { rule := powLogProductPow, ruleDecl := ``powLogProductPow, proofs := [],
    counterexamples := [(.real, ``powLogProductPow_counterexample_real),
      (.complex, ``powLogProductPow_counterexample_complex)],
    findings := [
      "counterexample: at b = c = e = f = g = s = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but (h (m + 1))^(-1) is not (Lean theorems powLogProductPow_counterexample_real and powLogProductPow_counterexample_complex). The rule needs h ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; IGtQ[s, 0]; NeQ[m, -1]", optionalFinding "g., h., m., e., f., a., b., p., c., d., q. and r."] },
  { rule := linPowLogLin, ruleDecl := ``linPowLogLin, proofs := [],
    counterexamples := [(.real, ``linPowLogLin_counterexample_real),
      (.complex, ``linPowLogLin_counterexample_complex)],
    findings := [
      "counterexample: at c = e = f = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but (g (q + 1))^(-1) is not (Lean theorems linPowLogLin_counterexample_real and linPowLogLin_counterexample_complex). The rule needs g ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[Multiply[e, f], Multiply[-1, d, g]], 0]; NeQ[q, -1]", optionalFinding "f., g., q., a., b., c., e. and n."] },
  { rule := powLogLogLin, ruleDecl := ``powLogLogLin, proofs := [],
    counterexamples := [(.real, ``powLogLogLin_counterexample_real),
      (.complex, ``powLogLogLin_counterexample_complex)],
    findings := [
      "counterexample: at c = f = 1 and the other metavariables 0 the condition q ≠ -1 holds and the integrand is defined everywhere, but (g (q + 1))^(-1) is not (Lean theorems powLogLogLin_counterexample_real and powLogLogLin_counterexample_complex). The rule needs g ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[q, -1]", optionalFinding "g., q., f., m., a., b., c., e. and n."] },
  { rule := logLogLinOverX, ruleDecl := ``logLogLinOverX, proofs := [],
    counterexamples := [(.real, ``logLogLinOverX_counterexample_real),
      (.complex, ``logLogLinOverX_counterexample_complex)],
    findings := [
      "counterexample: at c = f = 1 and the other metavariables 0 the integrand is defined near x = 1, but (2 m)^(-1) is not (Lean theorems logLogLinOverX_counterexample_real and logLogLinOverX_counterexample_complex). The rule needs m ≠ 0, which this migration does not add.",
      recFinding, optionalFinding "f., m., a., b., c., e. and n."] },
  { rule := logPowLogBinOverX, ruleDecl := ``logPowLogBinOverX, proofs := [],
    counterexamples := [(.real, ``logPowLogBinOverX_counterexample_real),
      (.complex, ``logPowLogBinOverX_counterexample_complex)],
    findings := [
      "counterexample: at c = f = 1 and the other metavariables 0 the condition m ≠ -1 holds and the integrand is defined near x = 1, but (q (m + 1))^(-1) is not (Lean theorems logPowLogBinOverX_counterexample_real and logPowLogBinOverX_counterexample_complex). The rule needs q ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[m, -1]", optionalFinding "f., q., m., a., b., c., e. and p."] },
  { rule := powTwoLogLin, ruleDecl := ``powTwoLogLin, proofs := [],
    counterexamples := [(.real, ``powTwoLogLin_counterexample_real),
      (.complex, ``powTwoLogLin_counterexample_complex)],
    findings := [
      "counterexample: at c = e = 1 and the other metavariables 0 the integrand is defined everywhere, but the residual integrand, which divides by d + e x, is not defined at x = 0 (Lean theorems powTwoLogLin_counterexample_real and powTwoLogLin_counterexample_complex). The rule needs d + e x ≠ 0 wherever the integrand is defined, which n ≠ 0 ensures, which this migration does not add.",
      recFinding, condFinding "NeQ[m, -1]", optionalFinding "m., a., b., c., e., n., f. and g."] },
  { rule := twoLogLin, ruleDecl := ``twoLogLin, proofs := [],
    counterexamples := [(.real, ``twoLogLin_counterexample_real),
      (.complex, ``twoLogLin_counterexample_complex)],
    findings := [
      "counterexample: at c = e = 1 and the other metavariables 0 the integrand is defined everywhere, but the residual integrand, which divides by d + e x, is not defined at x = 0 (Lean theorems twoLogLin_counterexample_real and twoLogLin_counterexample_complex). The rule needs d + e x ≠ 0 wherever the integrand is defined, which n ≠ 0 ensures, which this migration does not add.",
      recFinding, optionalFinding "a., b., c., e., n., f. and g."] },
  { rule := twoLogLinOverX, ruleDecl := ``twoLogLinOverX, proofs := [],
    counterexamples := [(.real, ``twoLogLinOverX_counterexample_real),
      (.complex, ``twoLogLinOverX_counterexample_complex)],
    findings := [
      "counterexample: at c = e = 1, d = -1 and the other metavariables 0 the integrand is defined near x = 1, but the residual integrand, which divides by d + e x, is not defined at x = 1 (Lean theorems twoLogLinOverX_counterexample_real and twoLogLinOverX_counterexample_complex). The rule needs d + e x ≠ 0 wherever the integrand is defined, which n ≠ 0 ensures, which this migration does not add.",
      recFinding, optionalFinding "a., b., c., e., n., f. and g."] },
  { rule := logMonoLogLin, ruleDecl := ``logMonoLogLin, proofs := [],
    counterexamples := [(.real, ``logMonoLogLin_counterexample_real),
      (.complex, ``logMonoLogLin_counterexample_complex)],
    findings := [
      "counterexample: at c = e = f = 1, d = -1 and the other metavariables 0 the integrand is defined everywhere, but the residual integrand x/(d + e x) is not defined at x = 1 (Lean theorems logMonoLogLin_counterexample_real and logMonoLogLin_counterexample_complex). The rule needs d + e x ≠ 0 wherever the integrand is defined, which n ≠ 0 ensures, which this migration does not add.",
      recFinding, optionalFinding "f., m., a., b., c., e. and n."] },
  { rule := logProductPow, ruleDecl := ``logProductPow, proofs := [],
    counterexamples := [(.real, ``logProductPow_counterexample_real),
      (.complex, ``logProductPow_counterexample_complex)],
    findings := [
      "counterexample: at a = d = e = f = p = s = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but b^(-1) is not (Lean theorems logProductPow_counterexample_real and logProductPow_counterexample_complex). The rule needs b ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; NeQ[Add[p, q], 0]; IGtQ[s, 0]; LtQ[s, 4]", optionalFinding "e., f., a., b., p., c., d., q., r. and s."] },
  { rule := logProductOverLin, ruleDecl := ``logProductOverLin, proofs := [],
    counterexamples := [(.real, ``logProductOverLin_counterexample_real),
      (.complex, ``logProductOverLin_counterexample_complex)],
    findings := [
      "counterexample: at b = c = e = f = g = 1 and the other metavariables 0 the condition holds and the integrand is defined everywhere, but h^(-1) is not (Lean theorems logProductOverLin_counterexample_real and logProductOverLin_counterexample_complex). The rule needs h ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]", optionalFinding "e., f., a., b., p., c., d., q., r., g. and h."] },
  { rule := logSqProductOverLin, ruleDecl := ``logSqProductOverLin, proofs := [],
    counterexamples := [(.real, ``logSqProductOverLin_counterexample_real),
      (.complex, ``logSqProductOverLin_counterexample_complex)],
    findings := [
      "counterexample: at b = c = e = f = g = 1 and the other metavariables 0 the condition holds and the integrand is defined everywhere, but h^(-1) is not (Lean theorems logSqProductOverLin_counterexample_real and logSqProductOverLin_counterexample_complex). The rule needs h ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]", optionalFinding "e., f., a., b., p., c., d., q., r., g. and h."] },
  { rule := logRatioOverLin, ruleDecl := ``logRatioOverLin, proofs := [],
    counterexamples := [(.real, ``logRatioOverLin_counterexample_real),
      (.complex, ``logRatioOverLin_counterexample_complex)],
    findings := [
      "counterexample: at b = c = e = f = 1 and the other metavariables 0 the condition holds and the integrand is defined everywhere, but g^(-1) is not (Lean theorems logRatioOverLin_counterexample_real and logRatioOverLin_counterexample_complex). The rule needs g ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]", optionalFinding "A., B., e., a., b., c., d., n., f. and g."] },
  { rule := logLinOverLin, ruleDecl := ``logLinOverLin, proofs := [],
    counterexamples := [(.real, ``logLinOverLin_counterexample_real),
      (.complex, ``logLinOverLin_counterexample_complex)],
    findings := [
      "counterexample: at c = e = f = 1 and the other metavariables 0 the condition holds and the integrand is defined everywhere, but g^(-1) is not (Lean theorems logLinOverLin_counterexample_real and logLinOverLin_counterexample_complex). The rule needs g ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[Multiply[e, f], Multiply[-1, d, g]], 0]", optionalFinding "a., b., c., e., n., f. and g."] },
  { rule := logLinPowOverLin, ruleDecl := ``logLinPowOverLin, proofs := [],
    counterexamples := [(.real, ``logLinPowOverLin_counterexample_real),
      (.complex, ``logLinPowOverLin_counterexample_complex)],
    findings := [
      "counterexample: at c = e = f = 1, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but g^(-1) is not (Lean theorems logLinPowOverLin_counterexample_real and logLinPowOverLin_counterexample_complex). The rule needs g ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[Multiply[e, f], Multiply[-1, d, g]], 0]; IGtQ[p, 1]", optionalFinding "a., b., c., e., n., f. and g."] },
  { rule := powTanSq, ruleDecl := ``powTanSq, proofs := [],
    counterexamples := [(.real, ``powTanSq_counterexample_real),
      (.complex, ``powTanSq_counterexample_complex)],
    findings := [
      "counterexample: at every metavariable 0 the integrand is defined everywhere, but (d n)^(-1) is not (Lean theorems powTanSq_counterexample_real and powTanSq_counterexample_complex). The rule needs d ≠ 0 and n ≠ 0, which this migration does not add.",
      recFinding, optionalFinding "m., c. and d."] },
  { rule := linTanTrinom, ruleDecl := ``linTanTrinom, proofs := [],
    counterexamples := [(.real, ``linTanTrinom_counterexample_real),
      (.complex, ``linTanTrinom_counterexample_complex)],
    findings := [
      "counterexample: at b = e = 1 and the other metavariables 0 the condition 2 c d - b e ≠ 0 holds and the integrand is defined near x = 0, but (2 c)^(-1) is not (Lean theorems linTanTrinom_counterexample_real and linTanTrinom_counterexample_complex). The rule needs c ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]", optionalFinding "d., e., a., b. and c."] },
  { rule := linFour, ruleDecl := ``linFour, proofs := [],
    counterexamples := [(.real, ``linFour_counterexample_real),
      (.complex, ``linFour_counterexample_complex)],
    findings := [
      "counterexample: at every metavariable 0 the conditions m + n + 2 ≠ 0 and m + n + 3 ≠ 0 hold and the integrand is defined everywhere, but (b^2 d^2 (m + n + 2) (m + n + 3))^(-1) is not (Lean theorems linFour_counterexample_real and linFour_counterexample_complex). The rule needs b ≠ 0 and d ≠ 0, which this migration does not add.",
      recFinding, condFinding "NeQ[Add[m, n, 2], 0]; NeQ[Add[m, n, 3], 0]", optionalFinding "a., b., m., c., d., n., f., g. and h."] },
  { rule := splitLogLog, ruleDecl := ``splitLogLog,
    proofs := [(.real, ``splitLogLog_real), (.complex, ``splitLogLog_complex)],
    findings := [recFinding, condFinding "NeQ[Add[Multiply[e, i], Multiply[-1, d, j]], 0]", optionalFinding "a., b., c., e., n., g., h., i., j. and m."] },
  { rule := logLinOverX, ruleDecl := ``logLinOverX, proofs := [], unproved := [.complex],
    counterexamples := [(.real, ``logLinOverX_counterexample_real)],
    findings := [
      "counterexample: at c = d = 1 and the other metavariables 0 the condition c d > 0 holds and the integrand is defined near x = -1, but log x is not defined at -1 (Lean theorem logLinOverX_counterexample_real); RUBI reads Log as the complex logarithm.",
      lnComplexFinding, recFinding, condFinding "GtQ[Multiply[c, d], 0]", optionalFinding "a., b., c. and e."] },
  { rule := logOverLin, ruleDecl := ``logOverLin, proofs := [], unproved := [.complex],
    counterexamples := [(.real, ``logOverLin_counterexample_real)],
    findings := [
      "counterexample: at c = d = 1, e = -1 and the other metavariables 0 the condition -c d/e > 0 holds and the integrand is defined near x = 2, but log(d + e x) = log(-1) is not (Lean theorem logOverLin_counterexample_real); RUBI reads Log as the complex logarithm.",
      lnComplexFinding, recFinding, condFinding "GtQ[Multiply[-1, c, d, Power[e, -1]], 0]", optionalFinding "a., b., c. and e."] },
  { rule := linPowOverQuad, ruleDecl := ``linPowOverQuad,
    proofs := [(.real, ``linPowOverQuad_real), (.complex, ``linPowOverQuad_complex)],
    findings := [recFinding, condFinding "NeQ[c d^2 + a e^2, 0]; LtQ[m, -1]",
      integerFinding "m", optionalFinding "e. and c."] },
  { rule := rubi1113r12, ruleDecl := ``rubi1113r12, proofs := [],
    counterexamples := [(.real, ``rubi1113r12_counterexample_real), (.complex, ``rubi1113r12_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, c = 1, f = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1113r12_counterexample_real and rubi1113r12_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[0, p, 1]",
      optionalFinding "e., f., a., b., c. and d."] },
  { rule := rubi1113r13, ruleDecl := ``rubi1113r13, proofs := [],
    counterexamples := [(.real, ``rubi1113r13_counterexample_real), (.complex, ``rubi1113r13_counterexample_complex)],
    findings := [
      "counterexample: at a = 2, c = 2, f = 2, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1113r13_counterexample_real and rubi1113r13_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "GtQ[p, 1]",
      optionalFinding "e., f., a., b., c. and d."] },
  { rule := rubi1114r38, ruleDecl := ``rubi1114r38, proofs := [],
    counterexamples := [(.real, ``rubi1114r38_counterexample_real), (.complex, ``rubi1114r38_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, c = 1, f = 1, g = 1, h = 1, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1114r38_counterexample_real and rubi1114r38_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[0, p, 1]",
      optionalFinding "e., f., g., h., a., b., c. and d."] },
  { rule := rubi1135r25, ruleDecl := ``rubi1135r25, proofs := [],
    counterexamples := [(.real, ``rubi1135r25_counterexample_real), (.complex, ``rubi1135r25_counterexample_complex)],
    findings := [
      "counterexample: at a = 2, e = 2, f = 2, q = 2, r = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1135r25_counterexample_real and rubi1135r25_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "GtQ[q, 1]",
      optionalFinding "d., f. and b."] },
  { rule := rubi1136r17, ruleDecl := ``rubi1136r17, proofs := [],
    counterexamples := [(.real, ``rubi1136r17_counterexample_real), (.complex, ``rubi1136r17_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, d = 1, f = 1, g = 1, m = 1, n = 1, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1136r17_counterexample_real and rubi1136r17_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[n, 0]",
      optionalFinding "g., m., b., p., d., q. and f."] },
  { rule := rubi1136r18, ruleDecl := ``rubi1136r18, proofs := [],
    counterexamples := [(.real, ``rubi1136r18_counterexample_real), (.complex, ``rubi1136r18_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, d = 1, f = 1, g = 1, m = 1, n = 1, p = 1, q = 1, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1136r18_counterexample_real and rubi1136r18_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n, r are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 0]; IGtQ[r, 0]",
      optionalFinding "g., m., b., p., d., q., f. and r."] },
  { rule := rubi1211r5, ruleDecl := ``rubi1211r5, proofs := [],
    counterexamples := [(.real, ``rubi1211r5_counterexample_real), (.complex, ``rubi1211r5_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1211r5_counterexample_real and rubi1211r5_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; GtQ[p, 0]; IntegerQ[Multiply[4, p]]",
      optionalFinding "a., b. and c."] },
  { rule := rubi1212r20, ruleDecl := ``rubi1212r20, proofs := [],
    counterexamples := [(.real, ``rubi1212r20_counterexample_real), (.complex, ``rubi1212r20_counterexample_complex)],
    findings := [
      "counterexample: at m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1212r20_counterexample_real and rubi1212r20_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IntegerQ[p]",
      optionalFinding "e., m., b., c. and p."] },
  { rule := rubi1213r19, ruleDecl := ``rubi1213r19, proofs := [],
    counterexamples := [(.real, ``rubi1213r19_counterexample_real), (.complex, ``rubi1213r19_counterexample_complex)],
    findings := [
      "counterexample: at f = 1, g = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r19_counterexample_real and rubi1213r19_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IntegerQ[p]",
      optionalFinding "e., m., f., g., b., c. and p."] },
  { rule := rubi21r9, ruleDecl := ``rubi21r9, proofs := [],
    counterexamples := [(.real, ``rubi21r9_counterexample_real), (.complex, ``rubi21r9_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, d = 1, e = 1, f = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi21r9_counterexample_real and rubi21r9_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]",
      optionalFinding "c., d., m., b., g., e., f. and n."] },
  { rule := rubi22r1, ruleDecl := ``rubi22r1, proofs := [],
    counterexamples := [(.real, ``rubi22r1_counterexample_real), (.complex, ``rubi22r1_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, d = 1, e = 1, f = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi22r1_counterexample_real and rubi22r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]",
      optionalFinding "c., d., m., g., e., f., n. and b."] },
  { rule := rubi23r11, ruleDecl := ``rubi23r11, proofs := [],
    counterexamples := [(.real, ``rubi23r11_counterexample_real), (.complex, ``rubi23r11_counterexample_complex)],
    findings := [
      "counterexample: at b = -1, c = -1, n = -1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi23r11_counterexample_real and rubi23r11_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IntegerQ[Multiply[2, Power[n, -1]]]; ILtQ[n, 0]",
      optionalFinding "a., b., c. and d."] },
  { rule := rubi312r5, ruleDecl := ``rubi312r5, proofs := [],
    counterexamples := [(.real, ``rubi312r5_counterexample_real), (.complex, ``rubi312r5_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi312r5_counterexample_real and rubi312r5_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[m, -1]; GtQ[p, 0]",
      optionalFinding "d., m., a., b., c., n. and p."] },
  { rule := rubi313r4, ruleDecl := ``rubi313r4, proofs := [],
    counterexamples := [(.real, ``rubi313r4_counterexample_real), (.complex, ``rubi313r4_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, d = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi313r4_counterexample_real and rubi313r4_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]",
      optionalFinding "a., b., c., n., p. and e."] },
  { rule := rubi314r8, ruleDecl := ``rubi314r8, proofs := [],
    counterexamples := [(.real, ``rubi314r8_counterexample_real), (.complex, ``rubi314r8_counterexample_complex)],
    findings := [
      "counterexample: at c = 2, e = 2, n = 2, p = 2, r = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi314r8_counterexample_real and rubi314r8_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]",
      optionalFinding "a., b., c., n., p., e. and r."] },
  { rule := rubi315r13, ruleDecl := ``rubi315r13, proofs := [],
    counterexamples := [(.real, ``rubi315r13_counterexample_real), (.complex, ``rubi315r13_counterexample_complex)],
    findings := [
      "counterexample: at c = 2, e = 2, n = 2, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi315r13_counterexample_real and rubi315r13_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]",
      optionalFinding "a., b., c., n., p. and e."] },
  { rule := rubi315r14, ruleDecl := ``rubi315r14, proofs := [],
    counterexamples := [(.real, ``rubi315r14_counterexample_real), (.complex, ``rubi315r14_counterexample_complex)],
    findings := [
      "counterexample: at c = 2, e = 2, n = 2, p = 2, r = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi315r14_counterexample_real and rubi315r14_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]",
      optionalFinding "a., b., c., n., p., e. and r."] },
  { rule := rubi315r28, ruleDecl := ``rubi315r28, proofs := [],
    counterexamples := [(.real, ``rubi315r28_counterexample_real), (.complex, ``rubi315r28_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = 1, c = 1, d = 1, e = 1, f = 1, m = 1, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi315r28_counterexample_real and rubi315r28_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; IGtQ[q, 0]; NeQ[m, -1]",
      optionalFinding "g., m., a., b., c., n., p., d., e., f., r. and q."] },
  { rule := rubi315r33, ruleDecl := ``rubi315r33, proofs := [], unproved := [.real],
    counterexamples := [(.complex, ``rubi315r33_counterexample_complex)],
    findings := [
      "counterexample: at c = 2, d = 2, f = 2, m = 2, n = 2, p = 2, r = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorem rubi315r33_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "real: not proved; the counterexample of the other domain was not established over ℝ.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; NeQ[Multiply[d, e], 1]",
      optionalFinding "d., f., m., r., a., b., c., n. and p."] },
  { rule := rubi321r1, ruleDecl := ``rubi321r1, proofs := [],
    counterexamples := [(.real, ``rubi321r1_counterexample_real), (.complex, ``rubi321r1_counterexample_complex)],
    findings := [
      "counterexample: at B = 2, a = 2, d = 2, e = 2, n = 2, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi321r1_counterexample_real and rubi321r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; IGtQ[p, 0]",
      optionalFinding "A., B., e., a., b., c., d., n. and p."] },
  { rule := rubi33r31, ruleDecl := ``rubi33r31, proofs := [],
    counterexamples := [(.real, ``rubi33r31_counterexample_real), (.complex, ``rubi33r31_counterexample_complex)],
    findings := [
      "counterexample: at c = 2, d = 2, e = 2, f = 2, m = 2, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = -1, but the residual integrand 1 is not defined at x = -1 (Lean theorems rubi33r31_counterexample_real and rubi33r31_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]",
      optionalFinding "f., m., a., b., c., e., n. and p."] },
  { rule := rubi33r35, ruleDecl := ``rubi33r35, proofs := [],
    counterexamples := [(.real, ``rubi33r35_counterexample_real), (.complex, ``rubi33r35_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, d = 1, f = 1, g = 1, h = 1, i = 1, j = 1, n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = -1 (Lean theorems rubi33r35_counterexample_real and rubi33r35_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]",
      optionalFinding "a., b., c., e., n., p., f., g., h., i., j. and m."] },
  { rule := rubi34r2, ruleDecl := ``rubi34r2, proofs := [],
    counterexamples := [(.real, ``rubi34r2_counterexample_real), (.complex, ``rubi34r2_counterexample_complex)],
    findings := [
      "counterexample: at c = 2, e = 2, p = 2, q = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi34r2_counterexample_real and rubi34r2_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[q, 0]",
      optionalFinding "a., b., c., e. and p."] },
  { rule := rubi34r9, ruleDecl := ``rubi34r9, proofs := [], unproved := [.complex],
    counterexamples := [(.real, ``rubi34r9_counterexample_real)],
    findings := [
      "counterexample: at c = 2, d = 2, e = 2, m = 2, n = 2, p = 2, q = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorem rubi34r9_counterexample_real). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "complex: not proved; the counterexample of the other domain was not established over ℂ.",
      "independence: n, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[q, 1]; IntegerQ[n]; NeQ[m, -1]",
      optionalFinding "f., m., a., b., c., e. and p."] },
  { rule := rubi4112r33, ruleDecl := ``rubi4112r33, proofs := [],
    counterexamples := [(.real, ``rubi4112r33_counterexample_real), (.complex, ``rubi4112r33_counterexample_complex)],
    findings := [
      "counterexample: at m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r33_counterexample_real and rubi4112r33_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 0]; LtQ[n, Add[m, 1]]",
      optionalFinding "e., m., c. and d."] },
  { rule := rubi4112r34, ruleDecl := ``rubi4112r34, proofs := [],
    counterexamples := [(.real, ``rubi4112r34_counterexample_real), (.complex, ``rubi4112r34_counterexample_complex)],
    findings := [
      "counterexample: at m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r34_counterexample_real and rubi4112r34_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 0]; LtQ[n, Add[m, 1]]",
      optionalFinding "e., m., c. and d."] },
  { rule := rubi4112r83, ruleDecl := ``rubi4112r83, proofs := [],
    counterexamples := [(.real, ``rubi4112r83_counterexample_real), (.complex, ``rubi4112r83_counterexample_complex)],
    findings := [
      "counterexample: at n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r83_counterexample_real and rubi4112r83_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[0, n, Add[m, 1]]; NeQ[p, -1]",
      optionalFinding "m., a., b., n. and p."] },
  { rule := rubi4112r84, ruleDecl := ``rubi4112r84, proofs := [],
    counterexamples := [(.real, ``rubi4112r84_counterexample_real), (.complex, ``rubi4112r84_counterexample_complex)],
    findings := [
      "counterexample: at n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r84_counterexample_real and rubi4112r84_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[0, n, Add[m, 1]]; NeQ[p, -1]",
      optionalFinding "m., a., b., n. and p."] },
  { rule := rubi4113r19, ruleDecl := ``rubi4113r19, proofs := [],
    counterexamples := [(.real, ``rubi4113r19_counterexample_real), (.complex, ``rubi4113r19_counterexample_complex)],
    findings := [
      "counterexample: at b = 2, e = 2, m = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4113r19_counterexample_real and rubi4113r19_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r20, ruleDecl := ``rubi4113r20, proofs := [],
    counterexamples := [(.real, ``rubi4113r20_counterexample_real), (.complex, ``rubi4113r20_counterexample_complex)],
    findings := [
      "counterexample: at b = 2, e = 2, m = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4113r20_counterexample_real and rubi4113r20_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi476r1, ruleDecl := ``rubi476r1, proofs := [],
    counterexamples := [(.real, ``rubi476r1_counterexample_real), (.complex, ``rubi476r1_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi476r1_counterexample_real and rubi476r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; NeQ[n, -1]",
      optionalFinding "c., d., m., a., b. and n."] },
  { rule := rubi476r16, ruleDecl := ``rubi476r16, proofs := [],
    counterexamples := [(.real, ``rubi476r16_counterexample_real), (.complex, ``rubi476r16_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, f = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi476r16_counterexample_real and rubi476r16_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; NeQ[n, -1]",
      optionalFinding "e., f., m., c., d., b. and n."] },
  { rule := rubi476r17, ruleDecl := ``rubi476r17, proofs := [],
    counterexamples := [(.real, ``rubi476r17_counterexample_real), (.complex, ``rubi476r17_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, f = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi476r17_counterexample_real and rubi476r17_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; NeQ[n, -1]",
      optionalFinding "e., f., m., c., d., b. and n."] },
  { rule := rubi476r2, ruleDecl := ``rubi476r2, proofs := [], unproved := [.complex],
    counterexamples := [(.real, ``rubi476r2_counterexample_real)],
    findings := [
      "counterexample: at d = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorem rubi476r2_counterexample_real). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "complex: not proved; the counterexample of the other domain was not established over ℂ.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; NeQ[n, -1]",
      optionalFinding "c., d., m., a., b. and n."] },
  { rule := rubi478r13, ruleDecl := ``rubi478r13, proofs := [],
    counterexamples := [(.real, ``rubi478r13_counterexample_real), (.complex, ``rubi478r13_counterexample_complex)],
    findings := [
      "counterexample: at b = 2, c = 2, d = 2, m = 2, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi478r13_counterexample_real and rubi478r13_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 1]; NeQ[Add[Multiply[Power[b, 2], Power[d, 2], Power[n, 2], Power[p, 2]], Power[Add[m, 1], 2]], 0]",
      optionalFinding "e., m., d., a., b., c. and n."] },
  { rule := rubi478r14, ruleDecl := ``rubi478r14, proofs := [],
    counterexamples := [(.real, ``rubi478r14_counterexample_real), (.complex, ``rubi478r14_counterexample_complex)],
    findings := [
      "counterexample: at b = 2, c = 2, d = 2, m = 2, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi478r14_counterexample_real and rubi478r14_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 1]; NeQ[Add[Multiply[Power[b, 2], Power[d, 2], Power[n, 2], Power[p, 2]], Power[Add[m, 1], 2]], 0]",
      optionalFinding "e., m., d., a., b., c. and n."] },
  { rule := rubi479r1, ruleDecl := ``rubi479r1, proofs := [],
    counterexamples := [(.real, ``rubi479r1_counterexample_real), (.complex, ``rubi479r1_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, e = 1, f = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi479r1_counterexample_real and rubi479r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]",
      optionalFinding "e., f., m., c., d., n. and b."] },
  { rule := rubi479r11, ruleDecl := ``rubi479r11, proofs := [],
    counterexamples := [(.real, ``rubi479r11_counterexample_real), (.complex, ``rubi479r11_counterexample_complex)],
    findings := [
      "counterexample: at a = 2, e = 2, f = 2, m = 2, n = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi479r11_counterexample_real and rubi479r11_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 1]; NeQ[Add[Power[a, 2], Multiply[-1, Power[b, 2]]], 0]; IGtQ[m, 0]",
      optionalFinding "e., f., m., c., d. and b."] },
  { rule := rubi479r12, ruleDecl := ``rubi479r12, proofs := [],
    counterexamples := [(.real, ``rubi479r12_counterexample_real), (.complex, ``rubi479r12_counterexample_complex)],
    findings := [
      "counterexample: at a = 2, e = 2, f = 2, m = 2, n = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi479r12_counterexample_real and rubi479r12_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 1]; NeQ[Add[Power[a, 2], Multiply[-1, Power[b, 2]]], 0]; IGtQ[m, 0]",
      optionalFinding "e., f., m., c., d. and b."] },
  { rule := rubi479r16, ruleDecl := ``rubi479r16, proofs := [],
    counterexamples := [(.real, ``rubi479r16_counterexample_real), (.complex, ``rubi479r16_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, e = 1, f = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi479r16_counterexample_real and rubi479r16_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]",
      optionalFinding "e., f., m., c., d., n. and b."] },
  { rule := rubi479r2, ruleDecl := ``rubi479r2, proofs := [],
    counterexamples := [(.real, ``rubi479r2_counterexample_real), (.complex, ``rubi479r2_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, e = 1, f = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi479r2_counterexample_real and rubi479r2_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]",
      optionalFinding "e., f., m., c., d., n. and b."] },
  { rule := rubi479r25, ruleDecl := ``rubi479r25, proofs := [],
    counterexamples := [(.real, ``rubi479r25_counterexample_real), (.complex, ``rubi479r25_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, e = 1, f = 1, m = 1, n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi479r25_counterexample_real and rubi479r25_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]; IGtQ[p, 0]",
      optionalFinding "e., f., m., c., d., p., n. and b."] },
  { rule := rubi479r26, ruleDecl := ``rubi479r26, proofs := [],
    counterexamples := [(.real, ``rubi479r26_counterexample_real), (.complex, ``rubi479r26_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, e = 1, f = 1, m = 1, n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi479r26_counterexample_real and rubi479r26_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]; IGtQ[p, 0]",
      optionalFinding "e., f., m., c., d., p., n. and b."] },
  { rule := rubi479r27, ruleDecl := ``rubi479r27, proofs := [],
    counterexamples := [(.real, ``rubi479r27_counterexample_real), (.complex, ``rubi479r27_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, e = 1, f = 1, m = 1, n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi479r27_counterexample_real and rubi479r27_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]; IGtQ[p, 0]",
      optionalFinding "e., f., m., c., d., p., n. and b."] },
  { rule := rubi479r30, ruleDecl := ``rubi479r30, proofs := [],
    counterexamples := [(.real, ``rubi479r30_counterexample_real), (.complex, ``rubi479r30_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, e = 1, f = 1, m = 1, n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi479r30_counterexample_real and rubi479r30_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]; IGtQ[p, 0]",
      optionalFinding "e., f., m., c., d., p., n. and b."] },
  { rule := rubi1224r57, ruleDecl := ``rubi1224r57, proofs := [],
    counterexamples := [(.real, ``rubi1224r57_counterexample_real), (.complex, ``rubi1224r57_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = -1, c = 1, e = -1, f = 1, m = -1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1224r57_counterexample_real and rubi1224r57_counterexample_complex). The isolated converted rule needs an additional condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; GtQ[p, 0]; LtQ[m, 0]",
      optionalFinding "f., a., b., c., p., d. and e."] },
  { rule := rubi1224r58, ruleDecl := ``rubi1224r58, proofs := [],
    counterexamples := [(.real, ``rubi1224r58_counterexample_real), (.complex, ``rubi1224r58_counterexample_complex)],
    findings := [
      "counterexample: at a = -1, c = 1, e = -1, f = 1, m = -1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1224r58_counterexample_real and rubi1224r58_counterexample_complex). The isolated converted rule needs an additional condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "GtQ[p, 0]; LtQ[m, 0]",
      optionalFinding "f., c., p., d. and e."] },
  { rule := rubi21r10, ruleDecl := ``rubi21r10, proofs := [],
    counterexamples := [(.real, ``rubi21r10_counterexample_real), (.complex, ``rubi21r10_counterexample_complex)],
    findings := [
      "counterexample: at F = 1, b = -1, c = 1, d = -1, e = 1, g = -1, m = 1, p = -1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi21r10_counterexample_real and rubi21r10_counterexample_complex). The isolated converted rule needs an additional condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "ILtQ[p, 0]; IGtQ[m, 0]",
      optionalFinding "c., d., m., b., g., e., f. and n."] },
  { rule := rubi4112r45, ruleDecl := ``rubi4112r45, proofs := [],
    counterexamples := [(.real, ``rubi4112r45_counterexample_real), (.complex, ``rubi4112r45_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, m = 2, n = 1, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r45_counterexample_real and rubi4112r45_counterexample_complex). The isolated converted rule needs an additional condition that this migration does not add.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "GtQ[p, 1]; IGtQ[n, 0]; IGtQ[m, Add[Multiply[2, n], Multiply[-1, 1]]]",
      optionalFinding "m., a. and b."] },
  { rule := rubi4112r46, ruleDecl := ``rubi4112r46, proofs := [],
    counterexamples := [(.real, ``rubi4112r46_counterexample_real), (.complex, ``rubi4112r46_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, m = 2, n = 1, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r46_counterexample_real and rubi4112r46_counterexample_complex). The isolated converted rule needs an additional condition that this migration does not add.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "GtQ[p, 1]; IGtQ[n, 0]; IGtQ[m, Add[Multiply[2, n], Multiply[-1, 1]]]",
      optionalFinding "m., a. and b."] }
]

/-- Every catalogue rule is well formed: recursive rules by `recOk`, the
others by `wellFormed`. -/
theorem catalog_wellFormed : ∀ e ∈ catalog,
    (if e.rule.shape == .antiderivRec then e.rule.recOk else e.rule.wellFormed) = true := by
  intro e he
  simp only [catalog, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end OSR.Integration
