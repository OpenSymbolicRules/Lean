import OSR.Calculus
import OSR.IntegrationRec48
import OSR.IntegrationNum1
import OSR.IntegrationRec75
import OSR.IntegrationRec74
import OSR.IntegrationRec73
import OSR.IntegrationRec72
import OSR.IntegrationRec71
import OSR.IntegrationRec70
import OSR.IntegrationRec69
import OSR.IntegrationRec68
import OSR.IntegrationRec67
import OSR.IntegrationRec66
import OSR.IntegrationRec65
import OSR.IntegrationRec64
import OSR.IntegrationRec63
import OSR.IntegrationRec62
import OSR.IntegrationRec61
import OSR.IntegrationRec60
import OSR.IntegrationRec59
import OSR.IntegrationRec58
import OSR.IntegrationRec57
import OSR.IntegrationRec56
import OSR.IntegrationRec55
import OSR.IntegrationRec54
import OSR.IntegrationRec53
import OSR.IntegrationRec52
import OSR.IntegrationRec51
import OSR.IntegrationRec50
import OSR.IntegrationRec49

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

open OSR OSR.Calculus OSR.IntegrationRec OSR.IntegrationRec2 OSR.IntegrationRec3
  OSR.IntegrationRec4 OSR.IntegrationRec5 OSR.IntegrationRec6
  OSR.IntegrationRec7 OSR.IntegrationRec8 OSR.IntegrationRec9
  OSR.IntegrationRec10 OSR.IntegrationRec11 OSR.IntegrationRec12
  OSR.IntegrationRec13 OSR.IntegrationRec14 OSR.IntegrationRec15 OSR.IntegrationRec16
  OSR.IntegrationRec17 OSR.IntegrationRec18 OSR.IntegrationRec19
  OSR.IntegrationRec20 OSR.IntegrationRec21
  OSR.IntegrationRec22 OSR.IntegrationRec23
  OSR.IntegrationRec24 OSR.IntegrationRec25
  OSR.IntegrationRec26 OSR.IntegrationRec27
  OSR.IntegrationRec28 OSR.IntegrationRec29
  OSR.IntegrationRec30 OSR.IntegrationRec31
  OSR.IntegrationRec32 OSR.IntegrationRec33
  OSR.IntegrationRec34 OSR.IntegrationRec35
  OSR.IntegrationRec36 OSR.IntegrationRec37
  OSR.IntegrationRec38 OSR.IntegrationRec39 OSR.IntegrationRec40
  OSR.IntegrationRec41 OSR.IntegrationRec42
  OSR.IntegrationRec43 OSR.IntegrationRec44
  OSR.IntegrationRec45 OSR.IntegrationRec46
  OSR.IntegrationRec47 OSR.IntegrationRec48 OSR.IntegrationRec49 OSR.IntegrationNum1 OSR.IntegrationRec50 OSR.IntegrationRec51 OSR.IntegrationRec52 OSR.IntegrationRec53 OSR.IntegrationRec54 OSR.IntegrationRec55 OSR.IntegrationRec56 OSR.IntegrationRec57 OSR.IntegrationRec58 OSR.IntegrationRec59 OSR.IntegrationRec60 OSR.IntegrationRec61 OSR.IntegrationRec62 OSR.IntegrationRec63 OSR.IntegrationRec64 OSR.IntegrationRec65 OSR.IntegrationRec66 OSR.IntegrationNum1 OSR.IntegrationRec67 OSR.IntegrationRec68 OSR.IntegrationRec69 OSR.IntegrationRec70 OSR.IntegrationRec71 OSR.IntegrationRec72 OSR.IntegrationRec73 OSR.IntegrationRec74 OSR.IntegrationRec75 OSR.IntegrationFindings Filter Topology

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
    "the integrand contains F^(…), a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:5",
    "RUBI's condition IGtQ[Add[m, Multiply[1, Power[2, -1]]], 0] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:6",
    "the integrand has an exponent with denominator 2; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:7",
    "RUBI's condition ILtQ[Add[m, Multiply[3, Power[2, -1]]], 0] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:18",
    "RUBI's condition IGtQ[Add[m, Multiply[1, Power[2, -1]]], 0] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:26",
    "the integrand has an exponent with denominator 2; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:31",
    "the integrand has an exponent with denominator 2; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:37",
    "the integrand has an exponent with denominator 2; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.8 P(x) (c x)^m (a+b x^n)^p:1",
    "the integrand has an exponent with denominator 2; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.8 P(x) (c x)^m (a+b x^n)^p:2",
    "the integrand has an exponent with denominator 2; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:78",
    "the integrand has an exponent with denominator 2; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:79",
    "the integrand has an exponent with denominator 2; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:84",
    "the integrand has an exponent with denominator 2; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:85",
    "the integrand has an exponent with denominator 2; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.1 (a+b x^2+c x^4)^p:1",
    "RUBI's condition IntegerQ[Add[p, Multiply[-1, 1, Power[2, -1]]]] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:32",
    "RUBI's condition IGtQ[Add[p, Multiply[1, Power[2, -1]]], 0] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:33",
    "RUBI's condition IGtQ[Add[p, Multiply[1, Power[2, -1]]], 0] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:37",
    "RUBI's condition ILtQ[Add[p, Multiply[1, Power[2, -1]]], 0] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:38",
    "RUBI's condition ILtQ[Add[p, Multiply[1, Power[2, -1]]], 0] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p:5",
    "RUBI's condition IntegerQ[Add[p, Multiply[1, Power[2, -1]]]] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p:6",
    "RUBI's condition IntegerQ[Add[p, Multiply[1, Power[2, -1]]]] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.6 P(x) (d x)^m (a+b x^n+c x^(2 n))^p:9",
    "RUBI's condition EqQ[q, Multiply[n, Power[2, -1]]] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.6 P(x) (d x)^m (a+b x^n+c x^(2 n))^p:10",
    "RUBI's condition EqQ[q, Multiply[n, Power[2, -1]]] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.4 Improper/1.2.4.2 (d x)^m (a x^q+b x^n+c x^(2 n-q))^p:5",
    "RUBI's condition EqQ[m, Multiply[3, Add[n, Multiply[-1, 1]], Power[2, -1]]] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.4 Improper/1.2.4.2 (d x)^m (a x^q+b x^n+c x^(2 n-q))^p:6",
    "RUBI's condition EqQ[m, Multiply[Add[Multiply[3, n], Multiply[-1, 1]], Power[2, -1]]] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:9",
    "the integrand has an exponent with denominator 2; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:15",
    "RUBI's condition IntegerQ[Add[q, Multiply[-1, 1, Power[2, -1]]]] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined"),
  ("rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:11",
    "RUBI's condition IntegerQ[Add[q, Multiply[-1, 1, Power[2, -1]]]] forces a half-integer exponent; the fragment interprets arith1#power for integer exponents only, so the integrand is nowhere defined")]

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

/-! ## Counterexamples over ℂ at the branch cut of `log` -/

section Witness
variable {α : Type} [Field α] [CharZero α]
private theorem ivc0 : intValue? (0 : α) = some 0 := by simpa using intValue?_intCast (α := α) 0
private theorem ivc1 : intValue? (1 : α) = some 1 := by simpa using intValue?_intCast (α := α) 1
private theorem ivc2 : intValue? (2 : α) = some 2 := by simpa using intValue?_intCast (α := α) 2
private theorem ivcm1 : intValue? (-1 : α) = some (-1) := by
  simpa using intValue?_intCast (α := α) (-1)
end Witness

/-- **Counterexample** to `∫ 1/x = log x` over ℂ, at the cut: near `x = -1`
the integrand is defined, but `log` is not continuous at `-1`. -/
theorem reciprocal_counterexample_complex : ¬ reciprocal.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" [] reciprocal.body reciprocal.result
  rw [antiderivHoldsUnder_nil]
  intro h
  have hF : ∀ᶠ v in 𝓝 (-1 : ℂ), Defined Interp.complex (Function.update (fun _ => 0) "x" v)
      reciprocal.body := by
    filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [reciprocal, Defined, eval, Interp.complex, ivcm1, hv]
  have hc := (h (fun _ => 0) (-1) hF).2.continuousAt
  apply not_continuous_clog (fun _ l => l) (by fun_prop) (by
    intro h; have := congrArg Complex.im h; simp at this; linarith [Real.pi_pos])
  convert hc using 1
  funext w
  simp [reciprocal, eval, Interp.complex]

/-- **Counterexample** to `∫ log(c xⁿ) = x log(c xⁿ) - n x` over ℂ, at
`c = n = 1` and `x = -1`. -/
theorem logMonomial_counterexample_complex : ¬ logMonomial.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" [] logMonomial.body logMonomial.result
  rw [antiderivHoldsUnder_nil]
  intro h
  have hF : ∀ᶠ v in 𝓝 (-1 : ℂ), Defined Interp.complex
      (Function.update (fun s => if s = "c" ∨ s = "n" then 1 else 0) "x" v) logMonomial.body := by
    filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [logMonomial, Defined, eval, Interp.complex, ivc1, hv]
  have hc := (h _ (-1) hF).2.continuousAt
  apply not_continuous_clog (fun w l => w * l - w) (by fun_prop) (by
    intro h; have := congrArg Complex.im h; simp at this; linarith [Real.pi_pos])
  convert hc using 1
  funext w
  simp [logMonomial, eval, Interp.complex, ivc1]
  ring

private theorem csin_pi_I : Complex.sin (Real.pi * Complex.I) ≠ 0 := by
  rw [Complex.sin_mul_I, ← Complex.ofReal_sinh]
  exact mul_ne_zero (by exact_mod_cast (Real.sinh_pos_iff.2 Real.pi_pos).ne') Complex.I_ne_zero

/-- **Counterexample** over ℂ to `∫ sin(d (a + b log(c xⁿ)))`, at `a = 0`,
`b = c = d = n = 1` and `x = -1`. -/
theorem sinLog_counterexample_complex : ¬ sinLog.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" sinLog.conditions sinLog.body sinLog.result
  intro h
  have hF : ∀ᶠ v in 𝓝 (-1 : ℂ), Defined Interp.complex
      (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) "x" v)
      sinLog.body := by
    filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [sinLog, Defined, eval, Interp.complex, ivc1, hv]
  have hc := (h _ (by simp [sinLog, Cond.Holds, Defined, eval, Interp.complex, ivc2]) (-1) hF).2.continuousAt
  apply not_continuous_clog (fun w l => w * Complex.sin l * 2⁻¹ - w * Complex.cos l * 2⁻¹)
    (by fun_prop) (by
      intro h
      apply csin_pi_I
      simp [Complex.sin_neg, Complex.cos_neg] at h
      linear_combination -h)
  convert hc using 1
  funext w
  simp [sinLog, eval, Interp.complex, ivc1, ivc2, ivcm1]
  ring

/-- **Counterexample** over ℂ to `∫ cos(d (a + b log(c xⁿ)))`, at the same
point. -/
theorem cosLog_counterexample_complex : ¬ cosLog.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" cosLog.conditions cosLog.body cosLog.result
  intro h
  have hF : ∀ᶠ v in 𝓝 (-1 : ℂ), Defined Interp.complex
      (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) "x" v)
      cosLog.body := by
    filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0)] with v hv
    simp [cosLog, Defined, eval, Interp.complex, ivc1, hv]
  have hc := (h _ (by simp [cosLog, Cond.Holds, Defined, eval, Interp.complex, ivc2]) (-1) hF).2.continuousAt
  apply not_continuous_clog (fun w l => w * Complex.cos l * 2⁻¹ + w * Complex.sin l * 2⁻¹)
    (by fun_prop) (by
      intro h
      apply csin_pi_I
      simp [Complex.sin_neg, Complex.cos_neg] at h
      linear_combination -h)
  convert hc using 1
  funext w
  simp [cosLog, eval, Interp.complex, ivc1, ivc2, ivcm1]
  ring


/-- The Integration catalogue, in v0.1 file order: part 1. -/
def catalogPart1 : List CEntry := [
  { rule := reciprocal, ruleDecl := ``reciprocal, proofs := [],
    counterexamples := [(.real, ``reciprocal_counterexample_real), (.complex, ``reciprocal_counterexample_complex)],
    findings := [
      "counterexample: near x = -1 the integrand 1 · x^(-1) is defined, but ln(-1) is not, since transc1#ln is defined on the positive reals (Lean theorem reciprocal_counterexample_real). RUBI reads Log as the complex logarithm; a real antiderivative is ln|x|, which is outside the fragment.",
      "complex: counterexample at the branch cut of the principal logarithm: near x = -1 the integrand is defined, but the result is log x, and log is not continuous at -1 (it tends to -π i from below while log(-1) = π i), so the result has no derivative there (Lean theorem reciprocal_counterexample_complex)."] },
  { rule := logMonomial, ruleDecl := ``logMonomial,
    proofs := [(.real, ``logMonomial_real)],
    counterexamples := [(.complex, ``logMonomial_counterexample_complex)],
    findings := [
      "real: n must take an integer value, since the fragment interprets arith1#power for integer exponents only; the statement covers every point near which c x^n > 0.",
      "complex: counterexample at the branch cut of the principal logarithm: at c = n = 1 the integrand log x is defined near x = -1, but the result x log x - x is not continuous at -1 (Lean theorem logMonomial_counterexample_complex).", optionalFinding "c. and n."] },
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
    proofs := [(.real, ``sinLog_real)],
    counterexamples := [(.complex, ``sinLog_counterexample_complex)],
    findings := [
      "real: the condition b^2 d^2 n^2 + 1 ≠ 0 always holds; n must take an integer value, and the statement covers every point near which c x^n > 0.",
      "complex: counterexample at the branch cut of the principal logarithm: at a = 0, b = c = d = n = 1 the integrand sin(log x) is defined near x = -1, but the result (x sin(log x) - x cos(log x))/2 jumps across the cut, by sin(π i) = i sinh π ≠ 0 (Lean theorem sinLog_counterexample_complex).", neqFinding "NeQ[b^2 d^2 n^2 + 1, 0]",
      optionalFinding "a., b., c., d. and n."] },
  { rule := cosLog, ruleDecl := ``cosLog,
    proofs := [(.real, ``cosLog_real)],
    counterexamples := [(.complex, ``cosLog_counterexample_complex)],
    findings := [
      "real: the condition b^2 d^2 n^2 + 1 ≠ 0 always holds; n must take an integer value, and the statement covers every point near which c x^n > 0.",
      "complex: counterexample at the branch cut of the principal logarithm: at a = 0, b = c = d = n = 1 the integrand cos(log x) is defined near x = -1, but the result (x cos(log x) + x sin(log x))/2 jumps across the cut (Lean theorem cosLog_counterexample_complex).", neqFinding "NeQ[b^2 d^2 n^2 + 1, 0]",
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
    proofs := [(.real, ``logLinPow_real)],
    counterexamples := [(.complex, ``logLinPow_counterexample_complex)],
    findings := [
      "conditions: RUBI's GtQ[p, 0] becomes p > 0 (relation1#gt) and IntegerQ[2 p] becomes 2 p ∈ ℤ (set1#in, setname1#Z); the fragment interprets arith1#power for integer exponents only, so the statement covers the integer values of p.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's GtQ[p, 0] only holds for a numeric p, so the v1 rule declares p independent of x, as the statement requires.",
      "complex: counterexample at the branch cut of the principal logarithm: at a = 0, b = c = n = p = 1 the integrand log x is defined near x = -1, but the result x log x - Φ(x) jumps across the cut for every continuous Φ (Lean theorem logLinPow_counterexample_complex).", recFinding, optionalFinding "a., b., c., n. and p."] },
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
  { rule := logLinOverX, ruleDecl := ``logLinOverX, proofs := [],
    counterexamples := [(.real, ``logLinOverX_counterexample_real), (.complex, ``logLinOverX_counterexample_complex)],
    findings := [
      "counterexample: at c = d = 1 and the other metavariables 0 the condition c d > 0 holds and the integrand is defined near x = -1, but log x is not defined at -1 (Lean theorem logLinOverX_counterexample_real); RUBI reads Log as the complex logarithm.",
      "complex: counterexample at the branch cut of the principal logarithm: at a = c = d = 1 and the other metavariables 0 the integrand 1/x is defined near x = -1, but the result is log x (Lean theorem logLinOverX_counterexample_complex).", recFinding, condFinding "GtQ[Multiply[c, d], 0]", optionalFinding "a., b., c. and e."] },
  { rule := logOverLin, ruleDecl := ``logOverLin, proofs := [],
    counterexamples := [(.real, ``logOverLin_counterexample_real), (.complex, ``logOverLin_counterexample_complex)],
    findings := [
      "counterexample: at c = d = 1, e = -1 and the other metavariables 0 the condition -c d/e > 0 holds and the integrand is defined near x = 2, but log(d + e x) = log(-1) is not (Lean theorem logOverLin_counterexample_real); RUBI reads Log as the complex logarithm.",
      "complex: counterexample at the branch cut of the principal logarithm: at a = c = d = 1, e = -1 and the other metavariables 0 the condition -c d/e > 0 holds and the integrand 1/(1 - x) is defined near x = 2, but the result -log(1 - x) is not continuous at x = 2 (Lean theorem logOverLin_counterexample_complex).", recFinding, condFinding "GtQ[Multiply[-1, c, d, Power[e, -1]], 0]", optionalFinding "a., b., c. and e."] },
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
  { rule := rubi315r33, ruleDecl := ``rubi315r33, proofs := [],
    counterexamples := [(.real, ``rubi315r33_counterexample_real), (.complex, ``rubi315r33_counterexample_complex)],
    findings := [
      "counterexample: at c = 2, d = 2, f = 2, m = 2, n = 2, p = 2, r = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi315r33_counterexample_real and rubi315r33_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
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
  { rule := rubi34r9, ruleDecl := ``rubi34r9, proofs := [],
    counterexamples := [(.real, ``rubi34r9_counterexample_real), (.complex, ``rubi34r9_counterexample_complex)],
    findings := [
      "counterexample: at c = 2, d = 2, e = 2, m = 2, n = 2, p = 2, q = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi34r9_counterexample_real and rubi34r9_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
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
      optionalFinding "m., a., b., n. and p."] }
]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem catalogPart1_wellFormed : ∀ e ∈ catalogPart1,
    (if e.rule.shape == .antiderivRec then e.rule.recOk else e.rule.wellFormed) = true := by
  intro e he
  simp only [catalogPart1, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The Integration catalogue, in v0.1 file order: part 2. -/
def catalogPart2 : List CEntry := [
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
  { rule := rubi476r2, ruleDecl := ``rubi476r2, proofs := [],
    counterexamples := [(.real, ``rubi476r2_counterexample_real), (.complex, ``rubi476r2_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi476r2_counterexample_real and rubi476r2_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
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
      optionalFinding "m., a. and b."] },
  { rule := binomNegPow, ruleDecl := ``binomNegPow,
    proofs := [(.real, ``binomNegPow_real), (.complex, ``binomNegPow_complex)],
    findings := [
      "independence: n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding, condFinding "LtQ[n, 0]; IntegerQ[p]", optionalFinding "b." false] },
  { rule := binomPowSin, ruleDecl := ``binomPowSin,
    proofs := [(.real, ``binomPowSin_real), (.complex, ``binomPowSin_complex)],
    findings := [
      "independence: n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding, condFinding "ILtQ[p, 0]; ILtQ[n, 0]", optionalFinding "b., c. and d."] },
  { rule := binomPowCos, ruleDecl := ``binomPowCos,
    proofs := [(.real, ``binomPowCos_real), (.complex, ``binomPowCos_complex)],
    findings := [
      "independence: n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding, condFinding "ILtQ[p, 0]; ILtQ[n, 0]", optionalFinding "b., c. and d."] },
  { rule := monoBinomPowSin, ruleDecl := ``monoBinomPowSin,
    proofs := [(.real, ``monoBinomPowSin_real), (.complex, ``monoBinomPowSin_complex)],
    findings := [
      "independence: n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding, condFinding "ILtQ[p, 0]; ILtQ[n, 0]", optionalFinding "m., b., c. and d."] },
  { rule := monoBinomPowCos, ruleDecl := ``monoBinomPowCos,
    proofs := [(.real, ``monoBinomPowCos_real), (.complex, ``monoBinomPowCos_complex)],
    findings := [
      "independence: n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding, condFinding "ILtQ[p, 0]; ILtQ[n, 0]", optionalFinding "m., b., c. and d."] },
  { rule := rubi1113r14, ruleDecl := ``rubi1113r14, proofs := [],
    counterexamples := [(.real, ``rubi1113r14_counterexample_real), (.complex, ``rubi1113r14_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, c = -2, e = 1, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1113r14_counterexample_real and rubi1113r14_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]",
      optionalFinding "e., f., a., b., c. and d."] },
  { rule := rubi1114r3, ruleDecl := ``rubi1114r3, proofs := [],
    counterexamples := [(.real, ``rubi1114r3_counterexample_real), (.complex, ``rubi1114r3_counterexample_complex)],
    findings := [
      "counterexample: at a = -2, c = -2, e = -2, f = -2, g = -2, h = -2, m = -2, n = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1114r3_counterexample_real and rubi1114r3_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[m, -1]; LtQ[n, -1]",
      optionalFinding "a., b., c., d., f., g. and h."] },
  { rule := rubi1135r24, ruleDecl := ``rubi1135r24, proofs := [],
    counterexamples := [(.real, ``rubi1135r24_counterexample_real), (.complex, ``rubi1135r24_counterexample_complex)],
    findings := [
      "counterexample: at a = -2, c = 2, e = -2, f = 2, q = -2, r = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1135r24_counterexample_real and rubi1135r24_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: q, r are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[q, -1]; GtQ[r, 1]",
      optionalFinding "d., f. and b."] },
  { rule := rubi1135r26, ruleDecl := ``rubi1135r26, proofs := [],
    counterexamples := [(.real, ``rubi1135r26_counterexample_real), (.complex, ``rubi1135r26_counterexample_complex)],
    findings := [
      "counterexample: at a = -2, c = 1, e = -2, f = 1, q = -2, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1135r26_counterexample_real and rubi1135r26_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[q, -1]",
      optionalFinding "d., f. and b."] },
  { rule := rubi1212r12, ruleDecl := ``rubi1212r12, proofs := [],
    counterexamples := [(.real, ``rubi1212r12_counterexample_real), (.complex, ``rubi1212r12_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, d = -2, e = 1, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1212r12_counterexample_real and rubi1212r12_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]; NeQ[p, Multiply[-3, Power[2, -1]]]",
      optionalFinding "e. and c."] },
  { rule := rubi1213r15, ruleDecl := ``rubi1213r15, proofs := [],
    counterexamples := [(.real, ``rubi1213r15_counterexample_real), (.complex, ``rubi1213r15_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, d = -2, e = 1, f = -2, g = 1, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1213r15_counterexample_real and rubi1213r15_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; LtQ[p, -1]",
      optionalFinding "d., e., f., g., a., b. and c."] },
  { rule := rubi1213r16, ruleDecl := ``rubi1213r16, proofs := [],
    counterexamples := [(.real, ``rubi1213r16_counterexample_real), (.complex, ``rubi1213r16_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, d = -2, e = 1, f = -2, g = 1, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r16_counterexample_real and rubi1213r16_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]",
      optionalFinding "d., e., f., g. and c."] },
  { rule := rubi1222r17, ruleDecl := ``rubi1222r17, proofs := [],
    counterexamples := [(.real, ``rubi1222r17_counterexample_real), (.complex, ``rubi1222r17_counterexample_complex)],
    findings := [
      "counterexample: at b = -2, d = 1, m = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1222r17_counterexample_real and rubi1222r17_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; LtQ[m, -1]",
      optionalFinding "d., b. and c."] },
  { rule := rubi1224r55, ruleDecl := ``rubi1224r55, proofs := [],
    counterexamples := [(.real, ``rubi1224r55_counterexample_real), (.complex, ``rubi1224r55_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = -3, c = 1, e = -3, f = 1, m = -3, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1224r55_counterexample_real and rubi1224r55_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; GtQ[p, 0]; LtQ[m, -2]",
      optionalFinding "f., a., b., c., p., d. and e."] },
  { rule := rubi1224r56, ruleDecl := ``rubi1224r56, proofs := [],
    counterexamples := [(.real, ``rubi1224r56_counterexample_real), (.complex, ``rubi1224r56_counterexample_complex)],
    findings := [
      "counterexample: at a = -3, c = 1, e = -3, f = 1, m = -3, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1224r56_counterexample_real and rubi1224r56_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "GtQ[p, 0]; LtQ[m, -2]",
      optionalFinding "f., c., p., d. and e."] },
  { rule := rubi1224r59, ruleDecl := ``rubi1224r59, proofs := [],
    counterexamples := [(.real, ``rubi1224r59_counterexample_real), (.complex, ``rubi1224r59_counterexample_complex)],
    findings := [
      "counterexample: at b = -2, e = 3, f = -2, m = 3, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1224r59_counterexample_real and rubi1224r59_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; LtQ[p, -1]; GtQ[m, 2]",
      optionalFinding "f., m., a., b., c., d. and e."] },
  { rule := rubi1224r60, ruleDecl := ``rubi1224r60, proofs := [],
    counterexamples := [(.real, ``rubi1224r60_counterexample_real), (.complex, ``rubi1224r60_counterexample_complex)],
    findings := [
      "counterexample: at a = -2, d = 3, f = -2, m = 3, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1224r60_counterexample_real and rubi1224r60_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]; GtQ[m, 2]",
      optionalFinding "f., m., c., d. and e."] },
  { rule := rubi1224r61, ruleDecl := ``rubi1224r61, proofs := [],
    counterexamples := [(.real, ``rubi1224r61_counterexample_real), (.complex, ``rubi1224r61_counterexample_complex)],
    findings := [
      "counterexample: at b = -2, e = 1, f = -2, m = 1, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1224r61_counterexample_real and rubi1224r61_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; LtQ[p, -1]; GtQ[m, 0]",
      optionalFinding "f., m., a., b., c., d. and e."] },
  { rule := rubi1224r62, ruleDecl := ``rubi1224r62, proofs := [],
    counterexamples := [(.real, ``rubi1224r62_counterexample_real), (.complex, ``rubi1224r62_counterexample_complex)],
    findings := [
      "counterexample: at a = -2, d = 1, f = -2, m = 1, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1224r62_counterexample_real and rubi1224r62_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]; GtQ[m, 0]",
      optionalFinding "f., m., c., d. and e."] },
  { rule := rubi23r24, ruleDecl := ``rubi23r24, proofs := [],
    counterexamples := [(.real, ``rubi23r24_counterexample_real), (.complex, ``rubi23r24_counterexample_complex)],
    findings := [
      "counterexample: at F = 3, a = -2, c = 3, d = -2, e = 3, m = -2, n = 3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi23r24_counterexample_real and rubi23r24_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[d, e], Multiply[-1, c, f]], 0]; IGtQ[n, 2]; LtQ[m, -1]",
      optionalFinding "e., f., a., b., c. and d."] },
  { rule := rubi312r6, ruleDecl := ``rubi312r6, proofs := [],
    counterexamples := [(.real, ``rubi312r6_counterexample_real), (.complex, ``rubi312r6_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = -2, c = 1, d = -2, m = 1, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi312r6_counterexample_real and rubi312r6_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[m, -1]; LtQ[p, -1]",
      optionalFinding "d., m., a., b., c. and n."] },
  { rule := rubi313r10, ruleDecl := ``rubi313r10, proofs := [],
    counterexamples := [(.real, ``rubi313r10_counterexample_real), (.complex, ``rubi313r10_counterexample_complex)],
    findings := [
      "counterexample: at a = 2, b = -2, c = 2, e = -2, n = 2, q = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi313r10_counterexample_real and rubi313r10_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[q, -1]",
      optionalFinding "e., a., b., c. and n."] },
  { rule := rubi313r7, ruleDecl := ``rubi313r7, proofs := [],
    counterexamples := [(.real, ``rubi313r7_counterexample_real), (.complex, ``rubi313r7_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = -2, c = 1, d = -2, e = 1, p = -2, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi313r7_counterexample_real and rubi313r7_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]; GtQ[q, 0]",
      optionalFinding "e., q., a., b., c. and n."] },
  { rule := rubi314r12, ruleDecl := ``rubi314r12, proofs := [],
    counterexamples := [(.real, ``rubi314r12_counterexample_real), (.complex, ``rubi314r12_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = -2, c = 1, d = -2, m = 1, q = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi314r12_counterexample_real and rubi314r12_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "ILtQ[q, -1]; GtQ[m, 0]",
      optionalFinding "f., m., e., q., a., b., c. and n."] },
  { rule := rubi314r13, ruleDecl := ``rubi314r13, proofs := [],
    counterexamples := [(.real, ``rubi314r13_counterexample_real), (.complex, ``rubi314r13_counterexample_complex)],
    findings := [
      "counterexample: at a = 2, b = -2, c = 2, e = -2, f = 2, m = -2, n = 2, q = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi314r13_counterexample_real and rubi314r13_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "ILtQ[q, -1]; ILtQ[m, 0]",
      optionalFinding "f., m., e., q., a., b., c. and n."] },
  { rule := rubi314r18, ruleDecl := ``rubi314r18, proofs := [],
    counterexamples := [(.real, ``rubi314r18_counterexample_real), (.complex, ``rubi314r18_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = -2, c = 1, e = -2, p = 1, q = -2, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi314r18_counterexample_real and rubi314r18_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; ILtQ[q, -1]",
      optionalFinding "e., r., a., b., c., n. and p."] },
  { rule := rubi315r17, ruleDecl := ``rubi315r17, proofs := [],
    counterexamples := [(.real, ``rubi315r17_counterexample_real), (.complex, ``rubi315r17_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = -2, c = 1, e = -2, p = 1, q = -2, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi315r17_counterexample_real and rubi315r17_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; ILtQ[q, -1]",
      optionalFinding "e., r., a., b., c., n. and p."] },
  { rule := rubi315r8, ruleDecl := ``rubi315r8, proofs := [],
    counterexamples := [(.real, ``rubi315r8_counterexample_real), (.complex, ``rubi315r8_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = -2, c = 1, d = -2, m = 1, q = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi315r8_counterexample_real and rubi315r8_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "ILtQ[q, -1]; GtQ[m, 0]",
      optionalFinding "f., m., e., q., a., b., c. and n."] },
  { rule := rubi315r9, ruleDecl := ``rubi315r9, proofs := [],
    counterexamples := [(.real, ``rubi315r9_counterexample_real), (.complex, ``rubi315r9_counterexample_complex)],
    findings := [
      "counterexample: at a = 2, b = -2, c = 2, e = -2, f = 2, m = -2, n = 2, q = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi315r9_counterexample_real and rubi315r9_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "ILtQ[q, -1]; ILtQ[m, 0]",
      optionalFinding "f., m., e., q., a., b., c. and n."] },
  { rule := rubi4111r3, ruleDecl := ``rubi4111r3, proofs := [],
    counterexamples := [(.real, ``rubi4111r3_counterexample_real), (.complex, ``rubi4111r3_counterexample_complex)],
    findings := [
      "counterexample: at a = -2, c = 3, d = -2, n = 3, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4111r3_counterexample_real and rubi4111r3_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "ILtQ[p, -1]; IGtQ[n, 2]",
      optionalFinding "b., c. and d."] },
  { rule := rubi4111r4, ruleDecl := ``rubi4111r4, proofs := [],
    counterexamples := [(.real, ``rubi4111r4_counterexample_real), (.complex, ``rubi4111r4_counterexample_complex)],
    findings := [
      "counterexample: at a = -2, c = 3, d = -2, n = 3, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4111r4_counterexample_real and rubi4111r4_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "ILtQ[p, -1]; IGtQ[n, 2]",
      optionalFinding "b., c. and d."] },
  { rule := rubi4113r21, ruleDecl := ``rubi4113r21, proofs := [],
    counterexamples := [(.real, ``rubi4113r21_counterexample_real), (.complex, ``rubi4113r21_counterexample_complex)],
    findings := [
      "counterexample: at a = -2, b = 1, c = -2, d = 1, m = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4113r21_counterexample_real and rubi4113r21_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r22, ruleDecl := ``rubi4113r22, proofs := [],
    counterexamples := [(.real, ``rubi4113r22_counterexample_real), (.complex, ``rubi4113r22_counterexample_complex)],
    findings := [
      "counterexample: at a = -2, b = 1, c = -2, d = 1, m = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4113r22_counterexample_real and rubi4113r22_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] }
,
  { rule := rubi1221r5, ruleDecl := ``rubi1221r5, proofs := [],
    counterexamples := [(.real, ``rubi1221r5_counterexample_real), (.complex, ``rubi1221r5_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1221r5_counterexample_real and rubi1221r5_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; LtQ[p, -1]; IntegerQ[Multiply[2, p]]",
      optionalFinding "b. and c."] },
  { rule := rubi311r3, ruleDecl := ``rubi311r3, proofs := [],
    counterexamples := [(.real, ``rubi311r3_counterexample_real), (.complex, ``rubi311r3_counterexample_complex)],
    findings := [
      "counterexample: at b = 2, c = 2, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi311r3_counterexample_real and rubi311r3_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]; IntegerQ[Multiply[2, p]]",
      optionalFinding "a., b., c. and n."] },
  { rule := rubi314r17, ruleDecl := ``rubi314r17, proofs := [],
    counterexamples := [(.real, ``rubi314r17_counterexample_real), (.complex, ``rubi314r17_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, e = 1, p = 1, q = -3 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi314r17_counterexample_real and rubi314r17_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; LtQ[q, -1]; IntegerQ[Multiply[2, q]]",
      optionalFinding "e., a., b., c., n. and p."] },
  { rule := rubi314r9, ruleDecl := ``rubi314r9, proofs := [],
    counterexamples := [(.real, ``rubi314r9_counterexample_real), (.complex, ``rubi314r9_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, e = 1, m = -3, p = 1, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi314r9_counterexample_real and rubi314r9_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; IGtQ[r, 0]; ILtQ[m, -1]",
      optionalFinding "m., a., b., c., n., p., e. and r."] },
  { rule := rubi315r16, ruleDecl := ``rubi315r16, proofs := [],
    counterexamples := [(.real, ``rubi315r16_counterexample_real), (.complex, ``rubi315r16_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, e = 1, p = 1, q = -3 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi315r16_counterexample_real and rubi315r16_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; LtQ[q, -1]; IntegerQ[Multiply[2, q]]",
      optionalFinding "e., a., b., c., n. and p."] },
  { rule := rubi33r12, ruleDecl := ``rubi33r12, proofs := [],
    counterexamples := [(.real, ``rubi33r12_counterexample_real), (.complex, ``rubi33r12_counterexample_complex)],
    findings := [
      "counterexample: at b = 2, c = 2, e = 2, f = 2, g = 2, p = -3, q = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi33r12_counterexample_real and rubi33r12_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[e, f], Multiply[-1, d, g]], 0]; LtQ[p, -1]; GtQ[q, 0]",
      optionalFinding "f., g., q., a., b., c., e. and n."] },
  { rule := rubi23r23, ruleDecl := ``rubi23r23, proofs := [],
    counterexamples := [(.real, ``rubi23r23_counterexample_real), (.complex, ``rubi23r23_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, c = 1, d = 1, e = 1, m = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi23r23_counterexample_real and rubi23r23_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[d, e], Multiply[-1, c, f]], 0]; LtQ[m, -1]",
      optionalFinding "e., f., a., b., c. and d."] },
  { rule := rubi23r26, ruleDecl := ``rubi23r26, proofs := [],
    counterexamples := [(.real, ``rubi23r26_counterexample_real), (.complex, ``rubi23r26_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = 1, c = 1, f = 1, m = -3 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi23r26_counterexample_real and rubi23r26_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[d, e], Multiply[-1, c, f]], 0]; ILtQ[m, -1]",
      optionalFinding "e., f., a., b., c. and d."] },
  { rule := rubi23r35, ruleDecl := ``rubi23r35, proofs := [],
    counterexamples := [(.real, ``rubi23r35_counterexample_real), (.complex, ``rubi23r35_counterexample_complex)],
    findings := [
      "counterexample: at F = 1, a = 1, b = 1, d = 1, e = 1, g = 1, m = -3 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi23r35_counterexample_real and rubi23r35_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; NeQ[Add[Multiply[d, g], Multiply[-1, c, h]], 0]; ILtQ[m, -1]",
      optionalFinding "g., h., e., f., a., b., c. and d."] },
  { rule := powLinLogOverX, ruleDecl := ``powLinLogOverX,
    proofs := [(.real, ``powLinLogOverX_real), (.complex, ``powLinLogOverX_complex)],
    findings := [
      "independence: p and q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding, condFinding "IGtQ[p, 0]; GtQ[q, 0]; IntegerQ[Multiply[2, q]]", optionalFinding "e., q., a., b., c., n. and p."] },
  { rule := powSinPowBack, ruleDecl := ``powSinPowBack,
    proofs := [(.real, ``powSinPowBack_real), (.complex, ``powSinPowBack_complex)],
    findings := [
      "independence: m and n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding, condFinding "IGtQ[n, 0]; LtQ[m, -1]", optionalFinding "e., c. and d."] },
  { rule := powCosPowBack, ruleDecl := ``powCosPowBack,
    proofs := [(.real, ``powCosPowBack_real), (.complex, ``powCosPowBack_complex)],
    findings := [
      "independence: m and n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding, condFinding "IGtQ[n, 0]; LtQ[m, -1]", optionalFinding "e., c. and d."] },
  { rule := powOverTrigSq, ruleDecl := ``powOverTrigSq,
    proofs := [(.real, ``powOverTrigSq_real), (.complex, ``powOverTrigSq_complex)],
    findings := [
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding, condFinding "IGtQ[m, 0]; NeQ[Add[a, b], 0]; NeQ[Add[a, c], 0]", optionalFinding "f., g., m., a., b., d., e. and c."] },
  { rule := logPowLogPow, ruleDecl := ``logPowLogPow,
    proofs := [(.real, ``logPowLogPow_real)],
    counterexamples := [(.complex, ``logPowLogPow_counterexample_complex)],
    findings := [
      "independence: p and q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding, condFinding "IGtQ[p, 0]; IGtQ[q, 0]",
      optionalFinding "a., b., c., n., p., d., e., f., r. and q.", "complex: counterexample at the branch cut of the principal logarithm: at a = e = 0 and b = c = n = p = d = f = r = q = 1 the integrand log x is defined near x = -1, but the result x log x - Φ(x) jumps across the cut (Lean theorem logPowLogPow_counterexample_complex)."] },
  { rule := quadPowLog, ruleDecl := ``quadPowLog,
    proofs := [(.real, ``quadPowLog_real)],
    counterexamples := [(.complex, ``quadPowLog_counterexample_complex)],
    findings := [
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding, condFinding "GtQ[q, 0]",
      optionalFinding "e., q., a., b., c. and n.", "complex: counterexample at the branch cut of the principal logarithm: at d = q = b = c = n = 1 and the other metavariables 0 the integrand log x is defined near x = -1, but the result contains x log x/3 and jumps across the cut (Lean theorem quadPowLog_counterexample_complex)."] },
  { rule := powLinLogOverX2, ruleDecl := ``powLinLogOverX2,
    proofs := [(.real, ``powLinLogOverX2_real), (.complex, ``powLinLogOverX2_complex)],
    findings := [
      "independence: p and q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding, condFinding "IGtQ[p, 0]; GtQ[q, 0]; IntegerQ[Multiply[2, q]]", optionalFinding "e., q., a., b., c., n. and p."] },
  { rule := sinPowLog, ruleDecl := ``sinPowLog,
    proofs := [(.real, ``sinPowLog_real)],
    counterexamples := [(.complex, ``sinPowLog_counterexample_complex)],
    findings := [
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding, condFinding "IGtQ[p, 1]; NeQ[Add[Multiply[Power[b, 2], Power[d, 2], Power[n, 2], Power[p, 2]], 1], 0]", optionalFinding "d., a., b., c. and n.", "complex: counterexample at the branch cut of the principal logarithm: at p = 2, b = c = d = n = 1, a = 0 the integrand sin²(log x) is defined near x = -1, but the result jumps by 4 cos(π i) sin(π i)/5 ≠ 0 across the cut (Lean theorem sinPowLog_counterexample_complex)."] },
  { rule := cosPowLog, ruleDecl := ``cosPowLog,
    proofs := [(.real, ``cosPowLog_real)],
    counterexamples := [(.complex, ``cosPowLog_counterexample_complex)],
    findings := [
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding, condFinding "IGtQ[p, 1]; NeQ[Add[Multiply[Power[b, 2], Power[d, 2], Power[n, 2], Power[p, 2]], 1], 0]", optionalFinding "d., a., b., c. and n.", "complex: counterexample at the branch cut of the principal logarithm: at p = 2, b = c = d = n = 1, a = 0 the integrand cos²(log x) is defined near x = -1, but the result jumps by 4 cos(π i) sin(π i)/5 ≠ 0 across the cut (Lean theorem cosPowLog_counterexample_complex)."] },
  { rule := powSinPowReduce, ruleDecl := ``powSinPowReduce,
    proofs := [(.real, ``powSinPowReduce_real), (.complex, ``powSinPowReduce_complex)],
    findings := [
      "independence: m, n and p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding, condFinding "GtQ[p, 1]; IGtQ[n, 0]; ILtQ[m, Add[Multiply[-2, n], 1]]; NeQ[Add[m, n, 1], 0]", optionalFinding "m., a. and b."] },
  { rule := powCosPowReduce, ruleDecl := ``powCosPowReduce,
    proofs := [(.real, ``powCosPowReduce_real), (.complex, ``powCosPowReduce_complex)],
    findings := [
      "independence: m, n and p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding, condFinding "GtQ[p, 1]; IGtQ[n, 0]; ILtQ[m, Add[Multiply[-2, n], 1]]; NeQ[Add[m, n, 1], 0]", optionalFinding "m., a. and b."] },
  { rule := rubi4112r53, ruleDecl := ``rubi4112r53, proofs := [],
    counterexamples := [(.real, ``rubi4112r53_counterexample_real), (.complex, ``rubi4112r53_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, m = 2, n = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r53_counterexample_real and rubi4112r53_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]; NeQ[p, -2]; IGtQ[n, 0]; IGtQ[m, Add[Multiply[2, n], Multiply[-1, 1]]]",
      optionalFinding "m., a. and b."] },
  { rule := rubi4112r54, ruleDecl := ``rubi4112r54, proofs := [],
    counterexamples := [(.real, ``rubi4112r54_counterexample_real), (.complex, ``rubi4112r54_counterexample_complex)],
    findings := [
      "counterexample: at m = 2, n = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r54_counterexample_real and rubi4112r54_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]; NeQ[p, -2]; IGtQ[n, 0]; IGtQ[m, Add[Multiply[2, n], Multiply[-1, 1]]]",
      optionalFinding "m., a. and b."] },
  { rule := quadPowReduce, ruleDecl := ``quadPowReduce,
    proofs := [(.real, ``quadPowReduce_real), (.complex, ``quadPowReduce_complex)],
    findings := [
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding, condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; LtQ[p, -1]; NeQ[p, Multiply[-3, Power[2, -1]]]; IntegerQ[Multiply[4, p]]", optionalFinding "a., b. and c."] },
  { rule := linQuadPowReduce, ruleDecl := ``linQuadPowReduce,
    proofs := [(.real, ``linQuadPowReduce_real), (.complex, ``linQuadPowReduce_complex)],
    findings := [
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding, condFinding "NeQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; LtQ[p, -1]; NeQ[p, Multiply[-3, Power[2, -1]]]", optionalFinding "d., e., a., b. and c."] },
  { rule := rubi1222r19, ruleDecl := ``rubi1222r19, proofs := [],
    counterexamples := [(.real, ``rubi1222r19_counterexample_real), (.complex, ``rubi1222r19_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = 1, d = 1, m = 4 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1222r19_counterexample_real and rubi1222r19_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; GtQ[m, 3]",
      optionalFinding "d., b. and c."] },
  { rule := rubi314r11, ruleDecl := ``rubi314r11, proofs := [],
    counterexamples := [(.real, ``rubi314r11_counterexample_real), (.complex, ``rubi314r11_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, c = 1, d = 1, m = 1, p = 1, q = -4 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi314r11_counterexample_real and rubi314r11_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "ILtQ[Add[m, q, 2], 0]; IGtQ[p, 0]; LtQ[q, -1]; GtQ[m, 0]",
      optionalFinding "f., m., e., a., b., c., n. and p."] },
  { rule := quartPowReduce, ruleDecl := ``quartPowReduce,
    proofs := [(.real, ``quartPowReduce_real), (.complex, ``quartPowReduce_complex)],
    findings := [
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding, condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; GtQ[p, 0]; IntegerQ[Multiply[2, p]]", optionalFinding "b. and c."] },
  { rule := rubi1112r1, ruleDecl := ``rubi1112r1, proofs := [],
    counterexamples := [(.real, ``rubi1112r1_counterexample_real), (.complex, ``rubi1112r1_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, m = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1112r1_counterexample_real and rubi1112r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a, d], Multiply[-1, b, c, Add[m, 2]]], 0]",
      optionalFinding "b., m. and d."] },
  { rule := rubi1113r2, ruleDecl := ``rubi1113r2, proofs := [],
    counterexamples := [(.real, ``rubi1113r2_counterexample_real), (.complex, ``rubi1113r2_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, e = 1, f = 1, n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1113r2_counterexample_real and rubi1113r2_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[n, p, 2], 0]; EqQ[Add[Multiply[a, d, f, Add[n, p, 2]], Multiply[-1, b, Add[Multiply[d, e, Add[n, 1]], Multiply[c, f, Add[p, 1]]]]], 0]",
      optionalFinding "a., b., c., d., n., e., f. and p."] },
  { rule := rubi1113r53, ruleDecl := ``rubi1113r53, proofs := [],
    counterexamples := [(.real, ``rubi1113r53_counterexample_real), (.complex, ``rubi1113r53_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, d = 1, e = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1113r53_counterexample_real and rubi1113r53_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "IGtQ[Add[m, n], 0]; EqQ[Add[Multiply[2, b, d, e], Multiply[-1, f, Add[Multiply[b, c], Multiply[a, d]]]], 0]",
      optionalFinding "a., b., c., d., e. and f."] },
  { rule := rubi1113r9, ruleDecl := ``rubi1113r9, proofs := [],
    counterexamples := [(.real, ``rubi1113r9_counterexample_real), (.complex, ``rubi1113r9_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, e = 1, f = 1, n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1113r9_counterexample_real and rubi1113r9_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[n, p, 2], 0]; NeQ[Add[n, p, 3], 0]; EqQ[Add[Multiply[d, f, Add[n, p, 2], Add[Multiply[Power[a, 2], d, f, Add[n, p, 3]], Multiply[-1, b, Add[Multiply[b, c, e], Multiply[a, Add[Multiply[d, e, Add[n, 1]], Multiply[c, f, Add[p, 1]]]]]]]], Multiply[-1, b, Add[Multiply[d, e, Add[n, 1]], Multiply[c, f, Add[p, 1]]], Add[Multiply[a, d, f, Add[n, p, 4]], Multiply[-1, b, Add[Multiply[d, e, Add[n, 2]], Multiply[c, f, Add[p, 2]]]]]]], 0]",
      optionalFinding "a., b., c., d., n., e., f. and p."] },
  { rule := rubi1117r6, ruleDecl := ``rubi1117r6, proofs := [],
    counterexamples := [(.real, ``rubi1117r6_counterexample_real), (.complex, ``rubi1117r6_counterexample_complex)],
    findings := [
      "counterexample: at b2 = 1, m = 1, n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1117r6_counterexample_real and rubi1117r6_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a2, b1], Multiply[a1, b2]], 0]; EqQ[Add[m, Multiply[-1, 2, n], 1], 0]; NeQ[p, -1]",
      optionalFinding "m., b1., n. and b2."] },
  { rule := rubi1131r3, ruleDecl := ``rubi1131r3, proofs := [],
    counterexamples := [(.real, ``rubi1131r3_counterexample_real), (.complex, ``rubi1131r3_counterexample_complex)],
    findings := [
      "counterexample: at n = -1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1131r3_counterexample_real and rubi1131r3_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[1, Power[n, -1]], p, 1], 0]",
      optionalFinding "b." false] },
  { rule := rubi1132r3, ruleDecl := ``rubi1132r3, proofs := [],
    counterexamples := [(.real, ``rubi1132r3_counterexample_real), (.complex, ``rubi1132r3_counterexample_complex)],
    findings := [
      "counterexample: at n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1132r3_counterexample_real and rubi1132r3_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[m, Add[n, Multiply[-1, 1]]]; NeQ[p, -1]",
      optionalFinding "m. and b."] },
  { rule := rubi1132r4, ruleDecl := ``rubi1132r4, proofs := [],
    counterexamples := [(.real, ``rubi1132r4_counterexample_real), (.complex, ``rubi1132r4_counterexample_complex)],
    findings := [
      "counterexample: at b2 = 1, m = 1, n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1132r4_counterexample_real and rubi1132r4_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a2, b1], Multiply[a1, b2]], 0]; EqQ[m, Add[Multiply[2, n], Multiply[-1, 1]]]; NeQ[p, -1]",
      optionalFinding "m., b1., n. and b2."] },
  { rule := rubi1132r6, ruleDecl := ``rubi1132r6, proofs := [],
    counterexamples := [(.real, ``rubi1132r6_counterexample_real), (.complex, ``rubi1132r6_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, n = 1, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1132r6_counterexample_real and rubi1132r6_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[Add[m, 1], Power[n, -1]], p, 1], 0]; NeQ[m, -1]",
      optionalFinding "c., m. and b."] },
  { rule := rubi1132r7, ruleDecl := ``rubi1132r7, proofs := [],
    counterexamples := [(.real, ``rubi1132r7_counterexample_real), (.complex, ``rubi1132r7_counterexample_complex)],
    findings := [
      "counterexample: at a1 = 1, a2 = 1, m = 1, n = 1, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1132r7_counterexample_real and rubi1132r7_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a2, b1], Multiply[a1, b2]], 0]; EqQ[Add[Multiply[Add[m, 1], Power[Multiply[2, n], -1]], p, 1], 0]; NeQ[m, -1]",
      optionalFinding "c., m., b1. and b2."] },
  { rule := rubi1133r10, ruleDecl := ``rubi1133r10, proofs := [],
    counterexamples := [(.real, ``rubi1133r10_counterexample_real), (.complex, ``rubi1133r10_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, n = -1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1133r10_counterexample_real and rubi1133r10_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[a, d], Multiply[-1, b, c, Add[Multiply[n, Add[p, 1]], 1]]], 0]",
      optionalFinding "b., p. and d."] },
  { rule := rubi1133r18, ruleDecl := ``rubi1133r18, proofs := [],
    counterexamples := [(.real, ``rubi1133r18_counterexample_real), (.complex, ``rubi1133r18_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1133r18_counterexample_real and rubi1133r18_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[n, Add[p, Multiply[-1, 1]]], 1], 0]; IntegerQ[n]",
      optionalFinding "b. and d."] },
  { rule := rubi1133r5, ruleDecl := ``rubi1133r5, proofs := [],
    counterexamples := [(.real, ``rubi1133r5_counterexample_real), (.complex, ``rubi1133r5_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, n = 1, p = -3, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1133r5_counterexample_real and rubi1133r5_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[n, Add[p, q, 1]], 1], 0]; GtQ[q, 0]; NeQ[p, -1]",
      optionalFinding "b., d. and q."] },
  { rule := rubi1133r8, ruleDecl := ``rubi1133r8, proofs := [],
    counterexamples := [(.real, ``rubi1133r8_counterexample_real), (.complex, ``rubi1133r8_counterexample_complex)],
    findings := [
      "counterexample: at b = -1, c = -1, n = -1, q = -1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1133r8_counterexample_real and rubi1133r8_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[n, Add[p, q, 2]], 1], 0]; EqQ[Add[Multiply[a, d, Add[p, 1]], Multiply[b, c, Add[q, 1]]], 0]",
      optionalFinding "b. and d."] },
  { rule := rubi1134r14, ruleDecl := ``rubi1134r14, proofs := [],
    counterexamples := [(.real, ``rubi1134r14_counterexample_real), (.complex, ``rubi1134r14_counterexample_complex)],
    findings := [
      "counterexample: at a = 2, b = 1, c = 1, d = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1134r14_counterexample_real and rubi1134r14_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[a, d, Add[m, 1]], Multiply[-1, b, c, Add[m, Multiply[n, Add[p, 1]], 1]]], 0]; NeQ[m, -1]",
      optionalFinding "e., m., b., p. and d."] },
  { rule := rubi1134r17, ruleDecl := ``rubi1134r17, proofs := [],
    counterexamples := [(.real, ``rubi1134r17_counterexample_real), (.complex, ``rubi1134r17_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, d = 1, m = 1, n = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1134r17_counterexample_real and rubi1134r17_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[m, Multiply[n, Add[p, 1]], 1], 0]; NeQ[m, -1]",
      optionalFinding "e., m., b., p. and d."] },
  { rule := rubi1137r5, ruleDecl := ``rubi1137r5, proofs := [],
    counterexamples := [(.real, ``rubi1137r5_counterexample_real), (.complex, ``rubi1137r5_counterexample_complex)],
    findings := [
      "counterexample: at a = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1137r5_counterexample_real and rubi1137r5_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a, Power[B, 3]], Multiply[-1, b, Power[A, 3]]], 0]",
      optionalFinding "B. and b."] }
]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem catalogPart2_wellFormed : ∀ e ∈ catalogPart2,
    (if e.rule.shape == .antiderivRec then e.rule.recOk else e.rule.wellFormed) = true := by
  intro e he
  simp only [catalogPart2, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The Integration catalogue, in v0.1 file order: part 3. -/
def catalogPart3 : List CEntry := [
  { rule := rubi1211r1, ruleDecl := ``rubi1211r1, proofs := [],
    counterexamples := [(.real, ``rubi1211r1_counterexample_real), (.complex, ``rubi1211r1_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1211r1_counterexample_real and rubi1211r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; LtQ[p, -1]",
      optionalFinding "b. and c."] },
  { rule := rubi1211r3, ruleDecl := ``rubi1211r3, proofs := [],
    counterexamples := [(.real, ``rubi1211r3_counterexample_real), (.complex, ``rubi1211r3_counterexample_complex)],
    findings := [
      "counterexample: at p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1211r3_counterexample_real and rubi1211r3_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; NeQ[p, Multiply[-1, Power[2, -1]]]",
      optionalFinding "b. and c."] },
  { rule := rubi1212r1, ruleDecl := ``rubi1212r1, proofs := [],
    counterexamples := [(.real, ``rubi1212r1_counterexample_real), (.complex, ``rubi1212r1_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, e = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1212r1_counterexample_real and rubi1212r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., m., a., b., c. and p."] },
  { rule := rubi1212r102, ruleDecl := ``rubi1212r102, proofs := [],
    counterexamples := [(.real, ``rubi1212r102_counterexample_real), (.complex, ``rubi1212r102_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, e = 1, m = 1, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1212r102_counterexample_real and rubi1212r102_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; EqQ[Add[m, Multiply[2, p], 3], 0]; LtQ[p, -1]",
      optionalFinding "e. and c."] },
  { rule := rubi1212r104, ruleDecl := ``rubi1212r104, proofs := [],
    counterexamples := [(.real, ``rubi1212r104_counterexample_real), (.complex, ``rubi1212r104_counterexample_complex)],
    findings := [
      "counterexample: at c = -1, d = -1, m = -1, p = -1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1212r104_counterexample_real and rubi1212r104_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; EqQ[Add[m, Multiply[2, p], 3], 0]",
      optionalFinding "e. and c."] },
  { rule := rubi1212r39, ruleDecl := ``rubi1212r39, proofs := [],
    counterexamples := [(.real, ``rubi1212r39_counterexample_real), (.complex, ``rubi1212r39_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, d = 1, m = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1212r39_counterexample_real and rubi1212r39_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; LtQ[p, -1]; LtQ[0, m, 1]; IntegerQ[Multiply[2, p]]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi1212r4, ruleDecl := ``rubi1212r4, proofs := [],
    counterexamples := [(.real, ``rubi1212r4_counterexample_real), (.complex, ``rubi1212r4_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1212r4_counterexample_real and rubi1212r4_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; NeQ[p, -1]",
      optionalFinding "e., a., b., c. and p."] },
  { rule := rubi1212r40, ruleDecl := ``rubi1212r40, proofs := [],
    counterexamples := [(.real, ``rubi1212r40_counterexample_real), (.complex, ``rubi1212r40_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, m = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1212r40_counterexample_real and rubi1212r40_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; LtQ[p, -1]; LtQ[0, m, 1]; IntegerQ[Multiply[2, p]]",
      optionalFinding "e. and c."] },
  { rule := rubi1212r41, ruleDecl := ``rubi1212r41, proofs := [],
    counterexamples := [(.real, ``rubi1212r41_counterexample_real), (.complex, ``rubi1212r41_counterexample_complex)],
    findings := [
      "counterexample: at b = 2, e = 2, m = 2, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1212r41_counterexample_real and rubi1212r41_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; LtQ[p, -1]; GtQ[m, 1]; IntegerQ[Multiply[2, p]]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi1212r42, ruleDecl := ``rubi1212r42, proofs := [],
    counterexamples := [(.real, ``rubi1212r42_counterexample_real), (.complex, ``rubi1212r42_counterexample_complex)],
    findings := [
      "counterexample: at a = 2, m = 2, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1212r42_counterexample_real and rubi1212r42_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; LtQ[p, -1]; GtQ[m, 1]; IntegerQ[Multiply[2, p]]",
      optionalFinding "e. and c."] },
  { rule := rubi1212r43, ruleDecl := ``rubi1212r43, proofs := [],
    counterexamples := [(.real, ``rubi1212r43_counterexample_real), (.complex, ``rubi1212r43_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, e = 1, m = 2, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1212r43_counterexample_real and rubi1212r43_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; GtQ[m, 1]; NeQ[Add[m, Multiply[2, p], 1], 0]; IntegerQ[Multiply[2, p]]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi1212r44, ruleDecl := ``rubi1212r44, proofs := [],
    counterexamples := [(.real, ``rubi1212r44_counterexample_real), (.complex, ``rubi1212r44_counterexample_complex)],
    findings := [
      "counterexample: at e = 1, m = 2, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1212r44_counterexample_real and rubi1212r44_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; GtQ[m, 1]; NeQ[Add[m, Multiply[2, p], 1], 0]; IntegerQ[Multiply[2, p]]",
      optionalFinding "e. and c."] },
  { rule := rubi1212r45, ruleDecl := ``rubi1212r45, proofs := [],
    counterexamples := [(.real, ``rubi1212r45_counterexample_real), (.complex, ``rubi1212r45_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, d = 1, m = -3, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1212r45_counterexample_real and rubi1212r45_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; LtQ[m, 0]; NeQ[Add[m, p, 1], 0]; IntegerQ[Multiply[2, p]]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi1212r46, ruleDecl := ``rubi1212r46, proofs := [],
    counterexamples := [(.real, ``rubi1212r46_counterexample_real), (.complex, ``rubi1212r46_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, m = -3, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1212r46_counterexample_real and rubi1212r46_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; LtQ[m, 0]; NeQ[Add[m, p, 1], 0]; IntegerQ[Multiply[2, p]]",
      optionalFinding "e. and c."] },
  { rule := rubi1212r5, ruleDecl := ``rubi1212r5, proofs := [],
    counterexamples := [(.real, ``rubi1212r5_counterexample_real), (.complex, ``rubi1212r5_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, e = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1212r5_counterexample_real and rubi1212r5_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; IGtQ[p, 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]",
      optionalFinding "e., a., b., c. and p."] },
  { rule := rubi1212r55, ruleDecl := ``rubi1212r55, proofs := [],
    counterexamples := [(.real, ``rubi1212r55_counterexample_real), (.complex, ``rubi1212r55_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = 1, d = 1, m = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1212r55_counterexample_real and rubi1212r55_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; EqQ[Add[m, Multiply[2, p], 3], 0]; NeQ[p, -1]",
      optionalFinding "e., a., b., c. and p."] },
  { rule := rubi1213r1, ruleDecl := ``rubi1213r1, proofs := [],
    counterexamples := [(.real, ``rubi1213r1_counterexample_real), (.complex, ``rubi1213r1_counterexample_complex)],
    findings := [
      "counterexample: at f = 1, g = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r1_counterexample_real and rubi1213r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[b, g, Add[m, p, 1]], Multiply[-1, c, f, Add[m, Multiply[2, p], 2]]], 0]; NeQ[Add[m, Multiply[2, p], 2], 0]",
      optionalFinding "e., m., g., b., c. and p."] },
  { rule := rubi1213r13, ruleDecl := ``rubi1213r13, proofs := [],
    counterexamples := [(.real, ``rubi1213r13_counterexample_real), (.complex, ``rubi1213r13_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, d = 1, f = 1, g = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r13_counterexample_real and rubi1213r13_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[Power[b, 2], e, g, Add[p, 2]], Multiply[-1, 2, a, c, e, g], Multiply[c, Add[Multiply[2, c, d, f], Multiply[-1, b, Add[Multiply[e, f], Multiply[d, g]]]], Add[Multiply[2, p], 3]]], 0]; NeQ[p, -1]",
      optionalFinding "d., e., f., g., a., b. and c."] },
  { rule := rubi1213r14, ruleDecl := ``rubi1213r14, proofs := [],
    counterexamples := [(.real, ``rubi1213r14_counterexample_real), (.complex, ``rubi1213r14_counterexample_complex)],
    findings := [
      "counterexample: at e = 1, f = 1, g = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r14_counterexample_real and rubi1213r14_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a, e, g], Multiply[-1, c, d, f, Add[Multiply[2, p], 3]]], 0]; NeQ[p, -1]",
      optionalFinding "d., e., f., g. and c."] },
  { rule := rubi1213r20, ruleDecl := ``rubi1213r20, proofs := [],
    counterexamples := [(.real, ``rubi1213r20_counterexample_real), (.complex, ``rubi1213r20_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, e = 1, f = 1, g = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1213r20_counterexample_real and rubi1213r20_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., f., g., a., b., c. and p."] },
  { rule := rubi1213r24, ruleDecl := ``rubi1213r24, proofs := [],
    counterexamples := [(.real, ``rubi1213r24_counterexample_real), (.complex, ``rubi1213r24_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, d = 1, f = 1, g = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r24_counterexample_real and rubi1213r24_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; EqQ[Add[Multiply[m, Add[Multiply[g, Add[Multiply[c, d], Multiply[-1, b, e]]], Multiply[c, e, f]]], Multiply[e, Add[p, 1], Add[Multiply[2, c, f], Multiply[-1, b, g]]]], 0]",
      optionalFinding "d., e., f., g., a., b. and c."] },
  { rule := rubi1213r25, ruleDecl := ``rubi1213r25, proofs := [],
    counterexamples := [(.real, ``rubi1213r25_counterexample_real), (.complex, ``rubi1213r25_counterexample_complex)],
    findings := [
      "counterexample: at d = -3, e = 1, f = 1, g = 1, m = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r25_counterexample_real and rubi1213r25_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; EqQ[Add[Multiply[m, Add[Multiply[d, g], Multiply[e, f]]], Multiply[2, e, f, Add[p, 1]]], 0]",
      optionalFinding "e., f., g. and c."] },
  { rule := rubi1213r26, ruleDecl := ``rubi1213r26, proofs := [],
    counterexamples := [(.real, ``rubi1213r26_counterexample_real), (.complex, ``rubi1213r26_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, e = 1, f = 1, g = 1, m = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1213r26_counterexample_real and rubi1213r26_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; LtQ[p, -1]; GtQ[m, 0]",
      optionalFinding "d., e., f., g., a., b. and c."] },
  { rule := rubi1213r27, ruleDecl := ``rubi1213r27, proofs := [],
    counterexamples := [(.real, ``rubi1213r27_counterexample_real), (.complex, ``rubi1213r27_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, f = 1, g = 1, m = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r27_counterexample_real and rubi1213r27_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; LtQ[p, -1]; GtQ[m, 0]",
      optionalFinding "d., e., f., g. and c."] },
  { rule := rubi1213r33, ruleDecl := ``rubi1213r33, proofs := [],
    counterexamples := [(.real, ``rubi1213r33_counterexample_real), (.complex, ``rubi1213r33_counterexample_complex)],
    findings := [
      "counterexample: at e = 1, f = 1, g = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r33_counterexample_real and rubi1213r33_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; NeQ[Add[m, Multiply[2, p], 2], 0]; NeQ[m, 2]",
      optionalFinding "e., f., g. and c."] },
  { rule := rubi1213r35, ruleDecl := ``rubi1213r35, proofs := [],
    counterexamples := [(.real, ``rubi1213r35_counterexample_real), (.complex, ``rubi1213r35_counterexample_complex)],
    findings := [
      "counterexample: at g = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r35_counterexample_real and rubi1213r35_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a, Power[g, 2]], Multiply[Power[f, 2], c]], 0]",
      optionalFinding "g. and c."] },
  { rule := rubi1213r36, ruleDecl := ``rubi1213r36, proofs := [],
    counterexamples := [(.real, ``rubi1213r36_counterexample_real), (.complex, ``rubi1213r36_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, d = 1, e = 1, g = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1213r36_counterexample_real and rubi1213r36_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[f, 2]], Multiply[-1, b, f, g], Multiply[a, Power[g, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., f., g., a., b., c. and p."] },
  { rule := rubi1213r5, ruleDecl := ``rubi1213r5, proofs := [],
    counterexamples := [(.real, ``rubi1213r5_counterexample_real), (.complex, ``rubi1213r5_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, e = 1, f = 1, g = 1, m = 1, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r5_counterexample_real and rubi1213r5_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[m, Multiply[2, p], 3], 0]; EqQ[Add[Multiply[2, c, f], Multiply[-1, b, g]], 0]",
      optionalFinding "d., e., m., g., b., c. and p."] },
  { rule := rubi1213r6, ruleDecl := ``rubi1213r6, proofs := [],
    counterexamples := [(.real, ``rubi1213r6_counterexample_real), (.complex, ``rubi1213r6_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, e = 1, f = 1, g = 1, m = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r6_counterexample_real and rubi1213r6_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, f], Multiply[-1, b, g]], 0]; LtQ[p, -1]; GtQ[m, 0]",
      optionalFinding "d., e., m., f., g., a., b. and c."] },
  { rule := rubi1213r7, ruleDecl := ``rubi1213r7, proofs := [],
    counterexamples := [(.real, ``rubi1213r7_counterexample_real), (.complex, ``rubi1213r7_counterexample_complex)],
    findings := [
      "counterexample: at c = -1, d = -1, f = -1, g = -1, m = -1, p = -1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1213r7_counterexample_real and rubi1213r7_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[m, Multiply[2, p], 3], 0]; NeQ[Add[Multiply[2, c, f], Multiply[-1, b, g]], 0]; NeQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]",
      optionalFinding "d., e., m., f., g., b. and c."] },
  { rule := rubi1214r1, ruleDecl := ``rubi1214r1, proofs := [],
    counterexamples := [(.real, ``rubi1214r1_counterexample_real), (.complex, ``rubi1214r1_counterexample_complex)],
    findings := [
      "counterexample: at f = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1214r1_counterexample_real and rubi1214r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, f, Add[m, 2]], Multiply[-1, b, g, Add[m, n, 3]]], 0]; NeQ[Add[m, n, 3], 0]",
      optionalFinding "m., g., n., b. and c."] },
  { rule := rubi1214r65, ruleDecl := ``rubi1214r65, proofs := [],
    counterexamples := [(.real, ``rubi1214r65_counterexample_real), (.complex, ``rubi1214r65_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1214r65_counterexample_real and rubi1214r65_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[b, e, Add[m, p, 2]], Multiply[2, c, d, Add[p, 1]]], 0]; EqQ[Add[Multiply[b, d, Add[p, 1]], Multiply[a, e, Add[m, 1]]], 0]; NeQ[Add[m, Multiply[2, p], 3], 0]",
      optionalFinding "d., e., m., a., b., c. and p."] },
  { rule := rubi1214r66, ruleDecl := ``rubi1214r66, proofs := [],
    counterexamples := [(.real, ``rubi1214r66_counterexample_real), (.complex, ``rubi1214r66_counterexample_complex)],
    findings := [
      "counterexample: at e = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1214r66_counterexample_real and rubi1214r66_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Multiply[d, Add[p, 1]], 0]; EqQ[Multiply[a, Add[m, 1]], 0]; NeQ[Add[m, Multiply[2, p], 3], 0]",
      optionalFinding "d., e., m., a., c. and p."] },
  { rule := rubi1216r10, ruleDecl := ``rubi1216r10, proofs := [],
    counterexamples := [(.real, ``rubi1216r10_counterexample_real), (.complex, ``rubi1216r10_counterexample_complex)],
    findings := [
      "counterexample: at f = 1, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1216r10_counterexample_real and rubi1216r10_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[e, 2]], Multiply[a, Power[f, 2]]], 0]; IntegerQ[p]",
      optionalFinding "c., e. and f."] },
  { rule := rubi1216r5, ruleDecl := ``rubi1216r5, proofs := [],
    counterexamples := [(.real, ``rubi1216r5_counterexample_real), (.complex, ``rubi1216r5_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, f = 1, g = 1, h = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1216r5_counterexample_real and rubi1216r5_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[g, 2]], Multiply[-1, b, g, h], Multiply[a, Power[h, 2]]], 0]; EqQ[Add[Multiply[Power[c, 2], d, Power[g, 2]], Multiply[-1, a, c, e, g, h], Multiply[Power[a, 2], f, Power[h, 2]]], 0]; IntegerQ[m]",
      optionalFinding "h., m., b., c., d., e. and f."] },
  { rule := rubi1216r6, ruleDecl := ``rubi1216r6, proofs := [],
    counterexamples := [(.real, ``rubi1216r6_counterexample_real), (.complex, ``rubi1216r6_counterexample_complex)],
    findings := [
      "counterexample: at e = 1, f = 1, g = 1, h = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1216r6_counterexample_real and rubi1216r6_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[g, 2]], Multiply[a, Power[h, 2]]], 0]; EqQ[Add[Multiply[Power[c, 2], d, Power[g, 2]], Multiply[-1, a, c, e, g, h], Multiply[Power[a, 2], f, Power[h, 2]]], 0]; IntegerQ[m]",
      optionalFinding "h., m., c., d., e. and f."] },
  { rule := rubi1216r7, ruleDecl := ``rubi1216r7, proofs := [],
    counterexamples := [(.real, ``rubi1216r7_counterexample_real), (.complex, ``rubi1216r7_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, f = 1, g = 1, h = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1216r7_counterexample_real and rubi1216r7_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[g, 2]], Multiply[-1, b, g, h], Multiply[a, Power[h, 2]]], 0]; EqQ[Add[Multiply[Power[c, 2], d, Power[g, 2]], Multiply[Power[a, 2], f, Power[h, 2]]], 0]; IntegerQ[m]",
      optionalFinding "h., m., b., c., d. and f."] },
  { rule := rubi1216r8, ruleDecl := ``rubi1216r8, proofs := [],
    counterexamples := [(.real, ``rubi1216r8_counterexample_real), (.complex, ``rubi1216r8_counterexample_complex)],
    findings := [
      "counterexample: at f = 1, g = 1, h = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1216r8_counterexample_real and rubi1216r8_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[g, 2]], Multiply[a, Power[h, 2]]], 0]; EqQ[Add[Multiply[Power[c, 2], d, Power[g, 2]], Multiply[Power[a, 2], f, Power[h, 2]]], 0]; IntegerQ[m]",
      optionalFinding "h., m., c., d. and f."] },
  { rule := rubi1216r9, ruleDecl := ``rubi1216r9, proofs := [],
    counterexamples := [(.real, ``rubi1216r9_counterexample_real), (.complex, ``rubi1216r9_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, f = 1, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1216r9_counterexample_real and rubi1216r9_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[e, 2]], Multiply[-1, b, e, f], Multiply[a, Power[f, 2]]], 0]; IntegerQ[p]",
      optionalFinding "a., b., c., e. and f."] },
  { rule := rubi1223r7, ruleDecl := ``rubi1223r7, proofs := [],
    counterexamples := [(.real, ``rubi1223r7_counterexample_real), (.complex, ``rubi1223r7_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, e = 1, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1223r7_counterexample_real and rubi1223r7_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., q., b., c. and p."] },
  { rule := rubi1223r8, ruleDecl := ``rubi1223r8, proofs := [],
    counterexamples := [(.real, ``rubi1223r8_counterexample_real), (.complex, ``rubi1223r8_counterexample_complex)],
    findings := [
      "counterexample: at e = 1, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1223r8_counterexample_real and rubi1223r8_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., q., c. and p."] },
  { rule := rubi1224r11, ruleDecl := ``rubi1224r11, proofs := [],
    counterexamples := [(.real, ``rubi1224r11_counterexample_real), (.complex, ``rubi1224r11_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, e = 1, f = 1, m = 1, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1224r11_counterexample_real and rubi1224r11_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "f., m., e., q., b., c. and p."] },
  { rule := rubi1224r12, ruleDecl := ``rubi1224r12, proofs := [],
    counterexamples := [(.real, ``rubi1224r12_counterexample_real), (.complex, ``rubi1224r12_counterexample_complex)],
    findings := [
      "counterexample: at e = 1, f = 1, m = 1, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1224r12_counterexample_real and rubi1224r12_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "f., m., e., q., c. and p."] },
  { rule := rubi131r4, ruleDecl := ``rubi131r4, proofs := [],
    counterexamples := [(.real, ``rubi131r4_counterexample_real), (.complex, ``rubi131r4_counterexample_complex)],
    findings := [
      "counterexample: at p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi131r4_counterexample_real and rubi131r4_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[4, Power[b, 3]], Multiply[27, Power[a, 2], d]], 0]; IntegerQ[p]",
      optionalFinding "a., b. and d."] },
  { rule := rubi132r1, ruleDecl := ``rubi132r1, proofs := [],
    counterexamples := [(.real, ``rubi132r1_counterexample_real), (.complex, ``rubi132r1_counterexample_complex)],
    findings := [
      "counterexample: at e = 1, f = 1, m = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi132r1_counterexample_real and rubi132r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[4, Power[b, 3]], Multiply[27, Power[a, 2], d]], 0]; IntegerQ[p]",
      optionalFinding "e., f., m., b., d. and p."] },
  { rule := rubi23r32, ruleDecl := ``rubi23r32, proofs := [],
    counterexamples := [(.real, ``rubi23r32_counterexample_real), (.complex, ``rubi23r32_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, c = 1, e = 1, f = 1, g = 1, h = 1, m = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi23r32_counterexample_real and rubi23r32_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]",
      optionalFinding "g., h., m., e., f., a., b., c. and d."] },
  { rule := rubi23r33, ruleDecl := ``rubi23r33, proofs := [],
    counterexamples := [(.real, ``rubi23r33_counterexample_real), (.complex, ``rubi23r33_counterexample_complex)],
    findings := [
      "counterexample: at F = 1, a = 1, b = 1, c = 1, e = 1, g = 1, m = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi23r33_counterexample_real and rubi23r33_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[d, g], Multiply[-1, c, h]], 0]",
      optionalFinding "g., h., m., e., f., a., b., c. and d."] },
  { rule := rubi23r39, ruleDecl := ``rubi23r39, proofs := [],
    counterexamples := [(.real, ``rubi23r39_counterexample_real), (.complex, ``rubi23r39_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, d = 1, e = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi23r39_counterexample_real and rubi23r39_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi23r40, ruleDecl := ``rubi23r40, proofs := [],
    counterexamples := [(.real, ``rubi23r40_counterexample_real), (.complex, ``rubi23r40_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, d = 1, e = 1, m = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi23r40_counterexample_real and rubi23r40_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi23r42, ruleDecl := ``rubi23r42, proofs := [],
    counterexamples := [(.real, ``rubi23r42_counterexample_real), (.complex, ``rubi23r42_counterexample_complex)],
    findings := [
      "counterexample: at F = 1, a = 1, d = 1, m = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi23r42_counterexample_real and rubi23r42_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi23r54, ruleDecl := ``rubi23r54, proofs := [],
    counterexamples := [(.real, ``rubi23r54_counterexample_real), (.complex, ``rubi23r54_counterexample_complex)],
    findings := [
      "counterexample: at F = 1, G = 1, H = 1, a = 1, b = 1, c = 1, e = 1, f = 1, h = 1, p = 1, r = 1, t = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi23r54_counterexample_real and rubi23r54_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[d, e, p, Log[F]], Multiply[g, h, Log[G]]], 0]; IntegerQ[p]",
      optionalFinding "h., f., g., t., r., s., b., e., c., d. and p."] },
  { rule := rubi23r76, ruleDecl := ``rubi23r76, proofs := [],
    counterexamples := [(.real, ``rubi23r76_counterexample_real), (.complex, ``rubi23r76_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, d = 1, e = 1, f = 1, g = 1, h = 1, m = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi23r76_counterexample_real and rubi23r76_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[e, g], Multiply[-1, d, h]], 0]",
      optionalFinding "g., h., m., f., a., b., c., d., e. and n."] },
  { rule := rubi312r3, ruleDecl := ``rubi312r3, proofs := [],
    counterexamples := [(.real, ``rubi312r3_counterexample_real), (.complex, ``rubi312r3_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, m = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi312r3_counterexample_real and rubi312r3_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[m, -1]; EqQ[Add[Multiply[a, Add[m, 1]], Multiply[-1, b, n]], 0]",
      optionalFinding "d., m., a., b., c. and n."] },
  { rule := rubi313r1, ruleDecl := ``rubi313r1, proofs := [],
    counterexamples := [(.real, ``rubi313r1_counterexample_real), (.complex, ``rubi313r1_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, e = 1, q = -2, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi313r1_counterexample_real and rubi313r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[r, Add[q, 1]], 1], 0]",
      optionalFinding "e., r., a., b., c. and n."] },
  { rule := rubi314r10, ruleDecl := ``rubi314r10, proofs := [],
    counterexamples := [(.real, ``rubi314r10_counterexample_real), (.complex, ``rubi314r10_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = 1, c = 1, d = 1, m = 1, p = 1, q = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi314r10_counterexample_real and rubi314r10_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[m, q, 2], 0]; IGtQ[p, 0]; LtQ[q, -1]",
      optionalFinding "f., m., e., a., b., c., n. and p."] },
  { rule := rubi314r2, ruleDecl := ``rubi314r2, proofs := [],
    counterexamples := [(.real, ``rubi314r2_counterexample_real), (.complex, ``rubi314r2_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = 1, c = 1, d = 1, m = 1, q = -3, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi314r2_counterexample_real and rubi314r2_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[m, Multiply[r, Add[q, 1]], 1], 0]; NeQ[m, -1]",
      optionalFinding "f., m., e., r., a., b., c. and n."] },
  { rule := rubi314r22, ruleDecl := ``rubi314r22, proofs := [],
    counterexamples := [(.real, ``rubi314r22_counterexample_real), (.complex, ``rubi314r22_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, d = 1, f = 1, g = 1, m = 1, p = 1, q = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 0 (Lean theorems rubi314r22_counterexample_real and rubi314r22_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[e, f], Multiply[-1, d, g]], 0]; EqQ[Add[m, q, 2], 0]; IGtQ[p, 0]; LtQ[q, -1]",
      optionalFinding "g., m., e., a., b., c., n. and p."] },
  { rule := rubi315r3, ruleDecl := ``rubi315r3, proofs := [],
    counterexamples := [(.real, ``rubi315r3_counterexample_real), (.complex, ``rubi315r3_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = 1, c = 1, d = 1, m = 1, q = -3, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi315r3_counterexample_real and rubi315r3_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[m, Multiply[r, Add[q, 1]], 1], 0]; NeQ[m, -1]",
      optionalFinding "f., m., e., r., a., b., c. and n."] },
  { rule := rubi321r9, ruleDecl := ``rubi321r9, proofs := [],
    counterexamples := [(.real, ``rubi321r9_counterexample_real), (.complex, ``rubi321r9_counterexample_complex)],
    findings := [
      "counterexample: at A = 1, B = 1, a = 1, b = 1, c = 1, e = 1, f = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi321r9_counterexample_real and rubi321r9_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[d, f], Multiply[-1, c, g]], 0]",
      optionalFinding "A., B., e., a., b., c., d., n., f. and g."] },
  { rule := rubi322r1, ruleDecl := ``rubi322r1, proofs := [],
    counterexamples := [(.real, ``rubi322r1_counterexample_real), (.complex, ``rubi322r1_counterexample_complex)],
    findings := [
      "counterexample: at A = 1, B = 1, a = 1, b = 1, c = 1, e = 1, f = 1, g = 1, h = 1, m = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi322r1_counterexample_real and rubi322r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[b, f], Multiply[-1, a, g]], 0]; EqQ[Add[Multiply[d, h], Multiply[-1, c, i]], 0]; IGtQ[m, -2]",
      optionalFinding "f., g., m., h., i., A., B., e., a., b., c., d. and n."] },
  { rule := rubi322r16, ruleDecl := ``rubi322r16, proofs := [],
    counterexamples := [(.real, ``rubi322r16_counterexample_real), (.complex, ``rubi322r16_counterexample_complex)],
    findings := [
      "counterexample: at A = 1, B = 1, a = 1, c = 1, e = 1, f = 1, g = 1, m = 1, n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi322r16_counterexample_real and rubi322r16_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[b, d, f], Multiply[-1, a, c, h]], 0]; EqQ[Add[Multiply[b, d, g], Multiply[-1, h, Add[Multiply[b, c], Multiply[a, d]]]], 0]; IntegerQ[m]",
      optionalFinding "f., g., h., m., A., B., e., a., b., c., d., n. and p."] },
  { rule := rubi323r5, ruleDecl := ``rubi323r5, proofs := [],
    counterexamples := [(.real, ``rubi323r5_counterexample_real), (.complex, ``rubi323r5_counterexample_complex)],
    findings := [
      "counterexample: at a = -1, c = -1, d = -1, e = 1, f = -1, g = -1, p = -1, r = -1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorem rubi323r5_counterexample_real). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "complex: counterexample at the branch cut of the principal logarithm: at e = -1, b = c = f = h = p = r = 1 and the other metavariables 0 the integrand log(-x)²/x is defined near x = -1, but the factor log(-x) - log x of the result jumps across the cut; with linear residual antiderivatives such that 2 Φ₂ + Φ₃ = 2 at -1, the result is not continuous there (Lean theorem rubi323r5_counterexample_complex).",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[b, g], Multiply[-1, a, h]], 0]",
      optionalFinding "e., f., a., b., p., c., d., q., r., g. and h."] },
  { rule := rubi323r8, ruleDecl := ``rubi323r8, proofs := [],
    counterexamples := [(.real, ``rubi323r8_counterexample_real), (.complex, ``rubi323r8_counterexample_complex)],
    findings := [
      "counterexample: at a = -3, b = 1, c = 1, d = 1, e = 1, f = 1, g = 1, i = 1, j = 1, m = 1, n = 1, p = 1, q = 1, s = 1, t = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi323r8_counterexample_real and rubi323r8_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[h, j], Multiply[-1, g, k]], 0]; IGtQ[m, 0]",
      optionalFinding "s., t., i., g., h., n., m., e., f., a., b., p., c., d., q., r., j. and k."] },
  { rule := rubi33r22, ruleDecl := ``rubi33r22, proofs := [],
    counterexamples := [(.real, ``rubi33r22_counterexample_real), (.complex, ``rubi33r22_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, d = 1, e = 1, f = 1, g = 1, m = 1, p = 1, q = 1, r = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = -1 (Lean theorems rubi33r22_counterexample_real and rubi33r22_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[m, Add[r, Multiply[-1, 1]]]; NeQ[q, -1]; IGtQ[p, 0]",
      optionalFinding "m., f., g., r., q., a., b., c., e., n. and p."] },
  { rule := rubi33r40, ruleDecl := ``rubi33r40, proofs := [],
    counterexamples := [(.real, ``rubi33r40_counterexample_real), (.complex, ``rubi33r40_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, d = 1, f = 1, g = 1, h = 1, i = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = -1, but the residual integrand 1 is not defined at x = -1 (Lean theorem rubi33r40_counterexample_real). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "complex: counterexample at the branch cut of the principal logarithm: at a = f = c = d = h = i = 1 and the other metavariables 0 the integrand 1/x is defined near x = -1, but the result is log x (Lean theorem rubi33r40_counterexample_complex).",
      recFinding,
      condFinding "EqQ[Add[Multiply[e, i], Multiply[-1, d, j]], 0]",
      optionalFinding "a., b., c., e., n., f., g., h., i., j. and m."] },
  { rule := rubi35r14, ruleDecl := ``rubi35r14, proofs := [],
    counterexamples := [(.real, ``rubi35r14_counterexample_real), (.complex, ``rubi35r14_counterexample_complex)],
    findings := [
      "counterexample: at b = 2, c = 2, q = 3, r = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi35r14_counterexample_real and rubi35r14_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[r, Add[q, Multiply[-1, 1]]]",
      optionalFinding "c., n., r., a., m. and b."] },
  { rule := rubi35r16, ruleDecl := ``rubi35r16, proofs := [],
    counterexamples := [(.real, ``rubi35r16_counterexample_real), (.complex, ``rubi35r16_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, m = 1, p = 1, q = 2, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi35r16_counterexample_real and rubi35r16_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[r, Add[q, Multiply[-1, 1]]]; NeQ[p, -1]",
      optionalFinding "c., n., r., a., m., b. and p."] },
  { rule := rubi35r17, ruleDecl := ``rubi35r17, proofs := [],
    counterexamples := [(.real, ``rubi35r17_counterexample_real), (.complex, ``rubi35r17_counterexample_complex)],
    findings := [
      "counterexample: at b = 2, c = 2, e = 2, m = 2, q = 3, r = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi35r17_counterexample_real and rubi35r17_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[r, Add[q, Multiply[-1, 1]]]; EqQ[Add[Multiply[a, e, m], Multiply[-1, b, d, n, q]], 0]",
      optionalFinding "d., m., e., c., n., r., a. and b."] },
  { rule := rubi35r19, ruleDecl := ``rubi35r19, proofs := [],
    counterexamples := [(.real, ``rubi35r19_counterexample_real), (.complex, ``rubi35r19_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, c = 1, e = 1, m = 1, q = 2, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi35r19_counterexample_real and rubi35r19_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[r, Add[q, Multiply[-1, 1]]]; NeQ[Add[Multiply[a, e, m], Multiply[-1, b, d, n, q]], 0]",
      optionalFinding "d., m., e., c., n., r., a. and b."] },
  { rule := rubi35r20, ruleDecl := ``rubi35r20, proofs := [],
    counterexamples := [(.real, ``rubi35r20_counterexample_real), (.complex, ``rubi35r20_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, d = 1, e = 1, m = 1, p = 1, q = 2, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi35r20_counterexample_real and rubi35r20_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[r, Add[q, Multiply[-1, 1]]]; NeQ[p, -1]; EqQ[Add[Multiply[a, e, m], Multiply[-1, b, d, n, q]], 0]",
      optionalFinding "d., m., e., c., n., r., a., b. and p."] },
  { rule := rubi35r21, ruleDecl := ``rubi35r21, proofs := [],
    counterexamples := [(.real, ``rubi35r21_counterexample_real), (.complex, ``rubi35r21_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, c = 1, e = 1, m = 1, p = 1, q = 2, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi35r21_counterexample_real and rubi35r21_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[r, Add[q, Multiply[-1, 1]]]; NeQ[p, -1]; NeQ[Add[Multiply[a, e, m], Multiply[-1, b, d, n, q]], 0]",
      optionalFinding "d., m., e., c., n., r., a., b. and p."] },
  { rule := rubi35r22, ruleDecl := ``rubi35r22, proofs := [],
    counterexamples := [(.real, ``rubi35r22_counterexample_real), (.complex, ``rubi35r22_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 2, e = 1, f = 1, m = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi35r22_counterexample_real and rubi35r22_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[e, n], Multiply[d, m]], 0]; EqQ[Add[Multiply[a, f], Multiply[b, d, Add[q, Multiply[-1, 1]]]], 0]",
      optionalFinding "d., m., e., c., n., f., q., a. and b."] },
  { rule := rubi35r23, ruleDecl := ``rubi35r23, proofs := [],
    counterexamples := [(.real, ``rubi35r23_counterexample_real), (.complex, ``rubi35r23_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 2, e = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi35r23_counterexample_real and rubi35r23_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[d, Multiply[e, n, q]], 0]",
      optionalFinding "e., c., n., a. and b."] },
  { rule := rubi4112r43, ruleDecl := ``rubi4112r43, proofs := [],
    counterexamples := [(.real, ``rubi4112r43_counterexample_real), (.complex, ``rubi4112r43_counterexample_complex)],
    findings := [
      "counterexample: at m = 1, n = 1, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r43_counterexample_real and rubi4112r43_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[m, Multiply[-1, 2, n], 1], 0]; GtQ[p, 1]",
      optionalFinding "m., a. and b."] },
  { rule := rubi4112r44, ruleDecl := ``rubi4112r44, proofs := [],
    counterexamples := [(.real, ``rubi4112r44_counterexample_real), (.complex, ``rubi4112r44_counterexample_complex)],
    findings := [
      "counterexample: at m = 1, n = 1, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r44_counterexample_real and rubi4112r44_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[m, Multiply[-1, 2, n], 1], 0]; GtQ[p, 1]",
      optionalFinding "m., a. and b."] },
  { rule := rubi4112r52, ruleDecl := ``rubi4112r52, proofs := [],
    counterexamples := [(.real, ``rubi4112r52_counterexample_real), (.complex, ``rubi4112r52_counterexample_complex)],
    findings := [
      "counterexample: at m = 1, n = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r52_counterexample_real and rubi4112r52_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[m, Multiply[-1, 2, n], 1], 0]; LtQ[p, -1]; NeQ[p, -2]",
      optionalFinding "m., a. and b."] },
  { rule := rubi4112r81, ruleDecl := ``rubi4112r81, proofs := [],
    counterexamples := [(.real, ``rubi4112r81_counterexample_real), (.complex, ``rubi4112r81_counterexample_complex)],
    findings := [
      "counterexample: at n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r81_counterexample_real and rubi4112r81_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[m, Add[n, Multiply[-1, 1]]]; NeQ[p, -1]",
      optionalFinding "m., a., b., n. and p."] },
  { rule := rubi4112r82, ruleDecl := ``rubi4112r82, proofs := [],
    counterexamples := [(.real, ``rubi4112r82_counterexample_real), (.complex, ``rubi4112r82_counterexample_complex)],
    findings := [
      "counterexample: at n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4112r82_counterexample_real and rubi4112r82_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[m, Add[n, Multiply[-1, 1]]]; NeQ[p, -1]",
      optionalFinding "m., a., b., n. and p."] },
  { rule := rubi4113r1, ruleDecl := ``rubi4113r1, proofs := [],
    counterexamples := [(.real, ``rubi4113r1_counterexample_real), (.complex, ``rubi4113r1_counterexample_complex)],
    findings := [
      "counterexample: at every metavariable 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi4113r1_counterexample_real and rubi4113r1_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]",
      optionalFinding "a., b. and c."] },
  { rule := rubi4113r11, ruleDecl := ``rubi4113r11, proofs := [],
    counterexamples := [(.real, ``rubi4113r11_counterexample_real), (.complex, ``rubi4113r11_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4113r11_counterexample_real and rubi4113r11_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]",
      optionalFinding "e., a., b. and c."] },
  { rule := rubi4113r12, ruleDecl := ``rubi4113r12, proofs := [],
    counterexamples := [(.real, ``rubi4113r12_counterexample_real), (.complex, ``rubi4113r12_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4113r12_counterexample_real and rubi4113r12_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]",
      optionalFinding "e., a., b. and c."] },
  { rule := rubi4113r13, ruleDecl := ``rubi4113r13, proofs := [],
    counterexamples := [(.real, ``rubi4113r13_counterexample_real), (.complex, ``rubi4113r13_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, m = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4113r13_counterexample_real and rubi4113r13_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r14, ruleDecl := ``rubi4113r14, proofs := [],
    counterexamples := [(.real, ``rubi4113r14_counterexample_real), (.complex, ``rubi4113r14_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, m = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4113r14_counterexample_real and rubi4113r14_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r15, ruleDecl := ``rubi4113r15, proofs := [],
    counterexamples := [(.real, ``rubi4113r15_counterexample_real), (.complex, ``rubi4113r15_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, d = 1, m = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4113r15_counterexample_real and rubi4113r15_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r16, ruleDecl := ``rubi4113r16, proofs := [],
    counterexamples := [(.real, ``rubi4113r16_counterexample_real), (.complex, ``rubi4113r16_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, d = 1, m = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4113r16_counterexample_real and rubi4113r16_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r2, ruleDecl := ``rubi4113r2, proofs := [],
    counterexamples := [(.real, ``rubi4113r2_counterexample_real), (.complex, ``rubi4113r2_counterexample_complex)],
    findings := [
      "counterexample: at every metavariable 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi4113r2_counterexample_real and rubi4113r2_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]",
      optionalFinding "a., b. and c."] },
  { rule := rubi4312r3, ruleDecl := ``rubi4312r3, proofs := [],
    counterexamples := [(.real, ``rubi4312r3_counterexample_real), (.complex, ``rubi4312r3_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi4312r3_counterexample_real and rubi4312r3_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]",
      optionalFinding "e., a., b. and c."] },
  { rule := rubi477r5, ruleDecl := ``rubi477r5, proofs := [],
    counterexamples := [(.real, ``rubi477r5_counterexample_real), (.complex, ``rubi477r5_counterexample_complex)],
    findings := [
      "counterexample: at F = 1, c = 1, d = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi477r5_counterexample_real and rubi477r5_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[Power[e, 2], Power[Add[n, 2], 2]], Multiply[Power[b, 2], Power[c, 2], Power[Log[F], 2]]], 0]; NeQ[n, -1]; NeQ[n, -2]",
      optionalFinding "c., a., b., d. and e."] },
  { rule := rubi477r6, ruleDecl := ``rubi477r6, proofs := [],
    counterexamples := [(.real, ``rubi477r6_counterexample_real), (.complex, ``rubi477r6_counterexample_complex)],
    findings := [
      "counterexample: at F = 1, c = 1, d = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi477r6_counterexample_real and rubi477r6_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[Power[e, 2], Power[Add[n, 2], 2]], Multiply[Power[b, 2], Power[c, 2], Power[Log[F], 2]]], 0]; NeQ[n, -1]; NeQ[n, -2]",
      optionalFinding "c., a., b., d. and e."] },
  { rule := rubi479r79, ruleDecl := ``rubi479r79, proofs := [],
    counterexamples := [(.real, ``rubi479r79_counterexample_real), (.complex, ``rubi479r79_counterexample_complex)],
    findings := [
      "counterexample: at c = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi479r79_counterexample_real and rubi479r79_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a, c], Multiply[-1, d]], 0]",
      optionalFinding "c., a. and d."] },
  { rule := rubi479r81, ruleDecl := ``rubi479r81, proofs := [],
    counterexamples := [(.real, ``rubi479r81_counterexample_real), (.complex, ``rubi479r81_counterexample_complex)],
    findings := [
      "counterexample: at c = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi479r81_counterexample_real and rubi479r81_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a, c], Multiply[-1, d]], 0]",
      optionalFinding "a., c. and d."] },
  { rule := rubi321r7, ruleDecl := ``rubi321r7, proofs := [],
    counterexamples := [(.real, ``rubi321r7_counterexample_real), (.complex, ``rubi321r7_counterexample_complex)],
    findings := [
      "counterexample: at b = -3, c = -3, e = 2, g = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi321r7_counterexample_real and rubi321r7_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[b, f], Multiply[-1, a, g]], 0]",
      optionalFinding "A., B., e., a., b., c., d., n., f. and g."] },
  { rule := rubi478r47, ruleDecl := ``rubi478r47, proofs := [],
    counterexamples := [(.real, ``rubi478r47_counterexample_real), (.complex, ``rubi478r47_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi478r47_counterexample_real and rubi478r47_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[m, Add[n, Multiply[-1, 1]]]",
      optionalFinding "m., a., n. and b."] },
  { rule := rubi478r48, ruleDecl := ``rubi478r48, proofs := [],
    counterexamples := [(.real, ``rubi478r48_counterexample_real), (.complex, ``rubi478r48_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi478r48_counterexample_real and rubi478r48_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[m, Add[n, Multiply[-1, 1]]]",
      optionalFinding "m., a., n. and b."] },
  { rule := linLinPow, ruleDecl := ``linLinPow,
    proofs := [(.real, ``linLinPow_real), (.complex, ``linLinPow_complex)],
    findings := [condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[m, n, 2], 0]; NeQ[m, -1]", optionalFinding "a., b., m., c. and d."] },
  { rule := monoBinomByParts, ruleDecl := ``monoBinomByParts,
    proofs := [(.real, ``monoBinomByParts_real), (.complex, ``monoBinomByParts_complex)],
    findings := [
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding, condFinding "EqQ[Add[Multiply[Add[m, 1], Power[n, -1]], p], 0]; GtQ[p, 0]", optionalFinding "m. and b."] },
  { rule := linLinRecip, ruleDecl := ``linLinRecip,
    proofs := [(.real, ``linLinRecip_real), (.complex, ``linLinRecip_complex)],
    findings := [
      recFinding,
      condFinding "EqQ[Add[Multiply[b, c], Multiply[a, d]], 0]", optionalFinding "b. and d."] },
  { rule := linLinMonoPow, ruleDecl := ``linLinMonoPow,
    proofs := [(.real, ``linLinMonoPow_real), (.complex, ``linLinMonoPow_complex)],
    findings := [
      recFinding,
      condFinding "EqQ[Add[Multiply[b, c], Multiply[a, d]], 0]; EqQ[n, m]; GtQ[a, 0]; GtQ[c, 0]", optionalFinding "a., b., m., c., d., n., f. and p."] },
  { rule := powInvLinLog, ruleDecl := ``powInvLinLog,
    proofs := [(.real, ``powInvLinLog_real), (.complex, ``powInvLinLog_complex)],
    findings := [
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[m, q]; IntegerQ[q]", optionalFinding "m., e., q., a., b., c., n. and p."] },
  { rule := powInvLinLog2, ruleDecl := ``powInvLinLog2,
    proofs := [(.real, ``powInvLinLog2_real), (.complex, ``powInvLinLog2_complex)],
    findings := [
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[m, q]; IntegerQ[q]", optionalFinding "m., e., q., a., b., c., n. and p."] }
]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem catalogPart3_wellFormed : ∀ e ∈ catalogPart3,
    (if e.rule.shape == .antiderivRec then e.rule.recOk else e.rule.wellFormed) = true := by
  intro e he
  simp only [catalogPart3, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The Integration catalogue, in v0.1 file order: part 4. -/
def catalogPart4 : List CEntry := [
  { rule := powInvLinLogLin, ruleDecl := ``powInvLinLogLin,
    proofs := [(.real, ``powInvLinLogLin_real), (.complex, ``powInvLinLogLin_complex)],
    findings := [
      recFinding,
      condFinding "EqQ[m, q]; IntegerQ[q]", optionalFinding "m., g., q., a., b., c., e., n. and p."] },
  { rule := polyBinomSplit, ruleDecl := ``polyBinomSplit,
    proofs := [(.real, ``polyBinomSplit_real), (.complex, ``polyBinomSplit_complex)],
    findings := [
      recFinding,
      condFinding "EqQ[Add[m, Multiply[-1, n], 1], 0]", optionalFinding "B., m., b. and p."] },
  { rule := polyBinomBinomSplit, ruleDecl := ``polyBinomBinomSplit,
    proofs := [(.real, ``polyBinomBinomSplit_real), (.complex, ``polyBinomBinomSplit_complex)],
    findings := [
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[m, Multiply[-1, n], 1], 0]", optionalFinding "B., m., a., b., p., d. and q."] },
  { rule := rubi479r78, ruleDecl := ``rubi479r78, proofs := [],
    counterexamples := [(.real, ``rubi479r78_counterexample_real), (.complex, ``rubi479r78_counterexample_complex)],
    findings := [
      "counterexample: at a = c = 1, d = -1 and the other metavariables 0 the conditions hold and the integrand x²/(sin x - x cos x)² is defined near x = π, but the residual integrand 1/sin²(x) is not defined at x = π (Lean theorems rubi479r78_counterexample_real and rubi479r78_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a, c], d], 0]",
      optionalFinding "c., a. and d."] },
  { rule := rubi479r82, ruleDecl := ``rubi479r82, proofs := [],
    counterexamples := [(.real, ``rubi479r82_counterexample_real), (.complex, ``rubi479r82_counterexample_complex)],
    findings := [
      "counterexample: at a = b = c = m = n = 1, d = -1 the conditions hold and the integrand x sin x/(sin x - x cos x)² is defined near x = π, but the residual integrand 1/(x sin x) is not defined at x = π (Lean theorems rubi479r82_counterexample_real and rubi479r82_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a, c], d], 0]; EqQ[m, Add[2, Multiply[-1, n]]]",
      optionalFinding "b., a., c. and d."] },
  { rule := cosPowOverSin, ruleDecl := ``cosPowOverSin,
    proofs := [(.real, ``cosPowOverSin_real), (.complex, ``cosPowOverSin_complex)],
    findings := [
      "independence: n is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[n, 1]; EqQ[Add[Power[a, 2], Multiply[-1, Power[b, 2]]], 0]", optionalFinding "e., f., m., c., d. and b."] },
  { rule := sinPowOverCos, ruleDecl := ``sinPowOverCos,
    proofs := [(.real, ``sinPowOverCos_real), (.complex, ``sinPowOverCos_complex)],
    findings := [
      "independence: n is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[n, 1]; EqQ[Add[Power[a, 2], Multiply[-1, Power[b, 2]]], 0]", optionalFinding "e., f., m., c., d. and b."] },
  { rule := expOnePlusCos, ruleDecl := ``expOnePlusCos,
    proofs := [(.real, ``expOnePlusCos_real), (.complex, ``expOnePlusCos_complex)],
    findings := [
      "independence: n is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[f, Multiply[-1, g]], 0]; ILtQ[n, 0]", optionalFinding "c., a., b., g., d., e. and n."] },
  { rule := expOneMinusCos, ruleDecl := ``expOneMinusCos,
    proofs := [(.real, ``expOneMinusCos_real), (.complex, ``expOneMinusCos_complex)],
    findings := [
      "independence: n is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[f, g], 0]; ILtQ[n, 0]", optionalFinding "c., a., b., g., d., e. and n."] },
  { rule := rubi477r32, ruleDecl := ``rubi477r32, proofs := [],
    counterexamples := [(.real, ``rubi477r32_counterexample_real), (.complex, ``rubi477r32_counterexample_complex)],
    findings := [
      "counterexample: at e = 1 and the other metavariables 0 the conditions hold and the integrand 0⁰ sin(x)⁰ (0 + 0 cos x)⁰ is defined everywhere, but the residual integrand 0⁰ tan(x/2)⁰ is not defined at x = π (Lean theorems rubi477r32_counterexample_real and rubi477r32_counterexample_complex).",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[Add[f, Multiply[-1, g]], 0]; IntegersQ[m, n]; EqQ[Add[m, n], 0]", optionalFinding "c., a., b., d., e., m., g. and n."] },
  { rule := expLinCosOverSin, ruleDecl := ``expLinCosOverSin,
    proofs := [(.real, ``expLinCosOverSin_real), (.complex, ``expLinCosOverSin_complex)],
    findings := [
      recFinding,
      condFinding "EqQ[Add[Power[f, 2], Multiply[-1, Power[g, 2]]], 0]; EqQ[Add[Power[h, 2], Multiply[-1, Power[i, 2]]], 0]; EqQ[Add[Multiply[g, h], Multiply[-1, f, i]], 0]", optionalFinding "c., a., b., i., d., e. and g."] },
  { rule := expLinSinOverCos, ruleDecl := ``expLinSinOverCos,
    proofs := [(.real, ``expLinSinOverCos_real), (.complex, ``expLinSinOverCos_complex)],
    findings := [
      recFinding,
      condFinding "EqQ[Add[Power[f, 2], Multiply[-1, Power[g, 2]]], 0]; EqQ[Add[Power[h, 2], Multiply[-1, Power[i, 2]]], 0]; EqQ[Add[Multiply[g, h], Multiply[f, i]], 0]", optionalFinding "c., a., b., i., d., e. and g."] },
  { rule := rubi1212r54, ruleDecl := ``rubi1212r54, proofs := [],
    counterexamples := [(.real, ``rubi1212r54_counterexample_real), (.complex, ``rubi1212r54_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, c = 1, e = 1 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1212r54_counterexample_real and rubi1212r54_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]",
      optionalFinding "e., a., b. and c."] },
  { rule := rubi1212r59, ruleDecl := ``rubi1212r59, proofs := [],
    counterexamples := [(.real, ``rubi1212r59_counterexample_real), (.complex, ``rubi1212r59_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, c = 1, e = 1, m = 2, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1212r59_counterexample_real and rubi1212r59_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; NeQ[Add[m, Multiply[2, p], 3], 0]; LtQ[p, -1]; GtQ[m, 1]; IntegerQ[Multiply[2, p]]",
      optionalFinding "e., a., b. and c."] },
  { rule := monoOverLogScale, ruleDecl := ``monoOverLogScale,
    proofs := [(.real, ``monoOverLogScale_real), (.complex, ``monoOverLogScale_complex)],
    findings := [
      recFinding,
      condFinding "EqQ[m, Add[n, Multiply[-1, 1]]]", optionalFinding "m. and c."] },
  { rule := sinSqOverQuotSq, ruleDecl := ``sinSqOverQuotSq,
    proofs := [(.real, ``sinSqOverQuotSq_real), (.complex, ``sinSqOverQuotSq_complex)],
    findings := [
      condFinding "EqQ[Add[Multiply[a, c], d], 0]", optionalFinding "a., c. and d."] },
  { rule := logQuotSplit, ruleDecl := ``logQuotSplit,
    proofs := [(.real, ``logQuotSplit_real), (.complex, ``logQuotSplit_complex)],
    findings := [
      recFinding,
      condFinding "EqQ[Add[Multiply[Power[e, 2], f], Multiply[Power[d, 2], g]], 0]; GtQ[Multiply[c, Power[Multiply[2, d], -1]], 0]", optionalFinding "a., b., c., e. and g."] },
  { rule := rubi1212r103, ruleDecl := ``rubi1212r103, proofs := [],
    counterexamples := [(.real, ``rubi1212r103_counterexample_real), (.complex, ``rubi1212r103_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, b = 1, e = 1, m = -1, p = -1 and the other metavariables 0 the conditions hold and the integrand 1/(x (1 + x)) is defined near x = 1, but the result divides by m + 1 = 0 (Lean theorems rubi1212r103_counterexample_real and rubi1212r103_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; NeQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; NeQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; EqQ[Add[m, Multiply[2, p], 3], 0]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := linQuadPowEqReduce, ruleDecl := ``linQuadPowEqReduce,
    proofs := [(.real, ``linQuadPowEqReduce_real), (.complex, ``linQuadPowEqReduce_complex)],
    findings := [
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; NeQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; NeQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; EqQ[Add[m, Multiply[2, p], 3], 0]; LtQ[p, -1]", optionalFinding "d., e., a., b. and c."] },
  { rule := monoBinomPairByParts, ruleDecl := ``monoBinomPairByParts,
    proofs := [(.real, ``monoBinomPairByParts_real), (.complex, ``monoBinomPairByParts_complex)],
    findings := [
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a2, b1], Multiply[a1, b2]], 0]; EqQ[Add[Multiply[Add[m, 1], Power[Multiply[2, n], -1]], p], 0]; GtQ[p, 0]", optionalFinding "m., b1. and b2."] },
  { rule := rubi1114r44, ruleDecl := ``rubi1114r44, proofs := [],
    counterexamples := [(.real, ``rubi1114r44_counterexample_real), (.complex, ``rubi1114r44_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, f = 1, g = 1, h = 1, i = 1, m = 1, n = 1, p = 1, q = 1, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1114r44_counterexample_real and rubi1114r44_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      optionalFinding "i., a., b., c., d., e., f., g. and h."] },
  { rule := rubi1133r11, ruleDecl := ``rubi1133r11, proofs := [],
    counterexamples := [(.real, ``rubi1133r11_counterexample_real), (.complex, ``rubi1133r11_counterexample_complex)],
    findings := [
      "counterexample: at b2 = 1, c = 1, d = 1, n = 2, non2 = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1133r11_counterexample_real and rubi1133r11_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: non2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[non2, Multiply[n, Power[2, -1]]]; EqQ[Add[Multiply[a2, b1], Multiply[a1, b2]], 0]; EqQ[Add[Multiply[a1, a2, d], Multiply[-1, b1, b2, c, Add[Multiply[n, Add[p, 1]], 1]]], 0]",
      optionalFinding "b1., non2., p., b2. and d."] },
  { rule := rubi1133r15, ruleDecl := ``rubi1133r15, proofs := [],
    counterexamples := [(.real, ``rubi1133r15_counterexample_real), (.complex, ``rubi1133r15_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, d = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1133r15_counterexample_real and rubi1133r15_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; NeQ[Add[Multiply[n, Add[p, 1]], 1], 0]",
      optionalFinding "b. and d."] },
  { rule := rubi1133r16, ruleDecl := ``rubi1133r16, proofs := [],
    counterexamples := [(.real, ``rubi1133r16_counterexample_real), (.complex, ``rubi1133r16_counterexample_complex)],
    findings := [
      "counterexample: at b2 = 1, c = 1, d = 1, n = 2, non2 = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1133r16_counterexample_real and rubi1133r16_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: non2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[non2, Multiply[n, Power[2, -1]]]; EqQ[Add[Multiply[a2, b1], Multiply[a1, b2]], 0]; NeQ[Add[Multiply[n, Add[p, 1]], 1], 0]",
      optionalFinding "b1., non2., p., b2. and d."] },
  { rule := rubi1134r15, ruleDecl := ``rubi1134r15, proofs := [],
    counterexamples := [(.real, ``rubi1134r15_counterexample_real), (.complex, ``rubi1134r15_counterexample_complex)],
    findings := [
      "counterexample: at b2 = 1, c = 1, d = 1, e = 1, m = 1, n = 2, non2 = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1134r15_counterexample_real and rubi1134r15_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: non2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[non2, Multiply[n, Power[2, -1]]]; EqQ[Add[Multiply[a2, b1], Multiply[a1, b2]], 0]; EqQ[Add[Multiply[a1, a2, d, Add[m, 1]], Multiply[-1, b1, b2, c, Add[m, Multiply[n, Add[p, 1]], 1]]], 0]; NeQ[m, -1]",
      optionalFinding "e., m., b1., non2., p., b2. and d."] },
  { rule := rubi1134r25, ruleDecl := ``rubi1134r25, proofs := [],
    counterexamples := [(.real, ``rubi1134r25_counterexample_real), (.complex, ``rubi1134r25_counterexample_complex)],
    findings := [
      "counterexample: at b2 = 1, c = 1, d = 1, e = 1, m = 1, n = 2, non2 = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1134r25_counterexample_real and rubi1134r25_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: non2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[non2, Multiply[n, Power[2, -1]]]; EqQ[Add[Multiply[a2, b1], Multiply[a1, b2]], 0]; NeQ[Add[m, Multiply[n, Add[p, 1]], 1], 0]",
      optionalFinding "e., m., b1., non2., p., b2. and d."] },
  { rule := rubi1135r30, ruleDecl := ``rubi1135r30, proofs := [],
    counterexamples := [(.real, ``rubi1135r30_counterexample_real), (.complex, ``rubi1135r30_counterexample_complex)],
    findings := [
      "counterexample: at a = 1, e = 1, f = 1, n = 1, p = -3, q = 1, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1135r30_counterexample_real and rubi1135r30_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "ILtQ[p, 0]; GtQ[q, 0]",
      optionalFinding "b., d. and f."] },
  { rule := rubi1136r28, ruleDecl := ``rubi1136r28, proofs := [],
    counterexamples := [(.real, ``rubi1136r28_counterexample_real), (.complex, ``rubi1136r28_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, f = 1, g = 1, m = 1, n = 1, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 0 (Lean theorems rubi1136r28_counterexample_real and rubi1136r28_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      optionalFinding "g., m., b., d. and f."] },
  { rule := rubi1137r16, ruleDecl := ``rubi1137r16, proofs := [],
    counterexamples := [(.real, ``rubi1137r16_counterexample_real), (.complex, ``rubi1137r16_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, f = 1, g = 1, n = 1, n2 = 2, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1137r16_counterexample_real and rubi1137r16_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[Multiply[a, c, f], Multiply[-1, e, Add[Multiply[b, c], Multiply[a, d]], Add[Multiply[n, Add[p, 1]], 1]]], 0]; EqQ[Add[Multiply[a, c, g], Multiply[-1, b, d, e, Add[Multiply[2, n, Add[p, 1]], 1]]], 0]",
      optionalFinding "f., n., g., n2., b., p. and d."] },
  { rule := rubi1137r17, ruleDecl := ``rubi1137r17, proofs := [],
    counterexamples := [(.real, ``rubi1137r17_counterexample_real), (.complex, ``rubi1137r17_counterexample_complex)],
    findings := [
      "counterexample: at c = -1, d = -1, e = -1, g = -1, n = -1, n2 = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1137r17_counterexample_real and rubi1137r17_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[Multiply[n, Add[p, 1]], 1], 0]; EqQ[Add[Multiply[a, c, g], Multiply[-1, b, d, e, Add[Multiply[2, n, Add[p, 1]], 1]]], 0]",
      optionalFinding "g., n2., b., n., p. and d."] },
  { rule := rubi1138r18, ruleDecl := ``rubi1138r18, proofs := [],
    counterexamples := [(.real, ``rubi1138r18_counterexample_real), (.complex, ``rubi1138r18_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, f = 1, g = 1, h = 1, m = 1, n = 1, n2 = 2, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1138r18_counterexample_real and rubi1138r18_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[Multiply[a, c, f, Add[m, 1]], Multiply[-1, e, Add[Multiply[b, c], Multiply[a, d]], Add[m, Multiply[n, Add[p, 1]], 1]]], 0]; EqQ[Add[Multiply[a, c, g, Add[m, 1]], Multiply[-1, b, d, e, Add[m, Multiply[2, n, Add[p, 1]], 1]]], 0]; NeQ[m, -1]",
      optionalFinding "h., m., f., n., g., n2., b., p. and d."] },
  { rule := rubi1138r19, ruleDecl := ``rubi1138r19, proofs := [],
    counterexamples := [(.real, ``rubi1138r19_counterexample_real), (.complex, ``rubi1138r19_counterexample_complex)],
    findings := [
      "counterexample: at b = -2, d = -2, g = -2, h = -2, m = -2, n = -1, n2 = -2, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1138r19_counterexample_real and rubi1138r19_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[m, Multiply[n, Add[p, 1]], 1], 0]; EqQ[Add[Multiply[a, c, g, Add[m, 1]], Multiply[-1, b, d, e, Add[m, Multiply[2, n, Add[p, 1]], 1]]], 0]; NeQ[m, -1]",
      optionalFinding "h., m., g., n2., b., n., p. and d."] },
  { rule := rubi1212r96, ruleDecl := ``rubi1212r96, proofs := [],
    counterexamples := [(.real, ``rubi1212r96_counterexample_real), (.complex, ``rubi1212r96_counterexample_complex)],
    findings := [
      "counterexample: at a = 2, e = 2, m = 2, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1212r96_counterexample_real and rubi1212r96_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; EqQ[Add[m, Multiply[2, p], 2], 0]; LtQ[p, -1]",
      optionalFinding "e. and c."] },
  { rule := rubi1231r3, ruleDecl := ``rubi1231r3, proofs := [],
    counterexamples := [(.real, ``rubi1231r3_counterexample_real), (.complex, ``rubi1231r3_counterexample_complex)],
    findings := [
      "counterexample: at n = 1, n2 = 2, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1231r3_counterexample_real and rubi1231r3_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]",
      optionalFinding "b., n., c. and n2."] },
  { rule := rubi1231r5, ruleDecl := ``rubi1231r5, proofs := [],
    counterexamples := [(.real, ``rubi1231r5_counterexample_real), (.complex, ``rubi1231r5_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1231r5_counterexample_real and rubi1231r5_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; ILtQ[p, -1]",
      optionalFinding "b., c. and n2."] },
  { rule := rubi1232r10, ruleDecl := ``rubi1232r10, proofs := [],
    counterexamples := [(.real, ``rubi1232r10_counterexample_real), (.complex, ``rubi1232r10_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, m = 1, n = 1, n2 = 2, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1232r10_counterexample_real and rubi1232r10_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n, n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; IGtQ[n, 0]; IGtQ[p, 0]; NeQ[Add[m, Multiply[2, n, p], 1], 0]",
      optionalFinding "d., m., b., c. and n2."] },
  { rule := rubi1232r18, ruleDecl := ``rubi1232r18, proofs := [],
    counterexamples := [(.real, ``rubi1232r18_counterexample_real), (.complex, ``rubi1232r18_counterexample_complex)],
    findings := [
      "counterexample: at b = 2, m = 2, n = 1, n2 = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1232r18_counterexample_real and rubi1232r18_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, n2 are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; IGtQ[n, 0]; GtQ[m, Add[Multiply[2, n], Multiply[-1, 1]]]",
      optionalFinding "d., b., c. and n2."] },
  { rule := rubi1233r11, ruleDecl := ``rubi1233r11, proofs := [],
    counterexamples := [(.real, ``rubi1233r11_counterexample_real), (.complex, ``rubi1233r11_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, e = 1, n = 1, n2 = 2, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1233r11_counterexample_real and rubi1233r11_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., q., b., c. and p."] },
  { rule := rubi1233r12, ruleDecl := ``rubi1233r12, proofs := [],
    counterexamples := [(.real, ``rubi1233r12_counterexample_real), (.complex, ``rubi1233r12_counterexample_complex)],
    findings := [
      "counterexample: at e = 1, n = 1, n2 = 2, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1233r12_counterexample_real and rubi1233r12_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., q., c. and p."] },
  { rule := rubi1233r19, ruleDecl := ``rubi1233r19, proofs := [],
    counterexamples := [(.real, ``rubi1233r19_counterexample_real), (.complex, ``rubi1233r19_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, c = 1, d = 1, n = 1, n2 = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1233r19_counterexample_real and rubi1233r19_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; NeQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]",
      optionalFinding "e., b. and c."] },
  { rule := rubi1233r20, ruleDecl := ``rubi1233r20, proofs := [],
    counterexamples := [(.real, ``rubi1233r20_counterexample_real), (.complex, ``rubi1233r20_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, d = 1, n = 1, n2 = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1233r20_counterexample_real and rubi1233r20_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]",
      optionalFinding "e. and c."] },
  { rule := rubi1233r27, ruleDecl := ``rubi1233r27, proofs := [],
    counterexamples := [(.real, ``rubi1233r27_counterexample_real), (.complex, ``rubi1233r27_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, d = 1, e = 1, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1233r27_counterexample_real and rubi1233r27_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; ILtQ[p, -1]",
      optionalFinding "e. and c."] },
  { rule := rubi1233r50, ruleDecl := ``rubi1233r50, proofs := [],
    counterexamples := [(.real, ``rubi1233r50_counterexample_real), (.complex, ``rubi1233r50_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, e = 1, f = 1, g = 1, n = 1, n2 = 2, p = 1, q = 1, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1233r50_counterexample_real and rubi1233r50_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., q., g., r., b., c. and p."] },
  { rule := rubi1233r51, ruleDecl := ``rubi1233r51, proofs := [],
    counterexamples := [(.real, ``rubi1233r51_counterexample_real), (.complex, ``rubi1233r51_counterexample_complex)],
    findings := [
      "counterexample: at e = 1, f = 1, g = 1, n = 1, n2 = 2, p = 1, q = 1, r = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1233r51_counterexample_real and rubi1233r51_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., q., g., r., c. and p."] },
  { rule := rubi1234r17, ruleDecl := ``rubi1234r17, proofs := [],
    counterexamples := [(.real, ``rubi1234r17_counterexample_real), (.complex, ``rubi1234r17_counterexample_complex)],
    findings := [
      "counterexample: at b = 1, e = 1, f = 1, m = 1, n = 1, n2 = 2, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1234r17_counterexample_real and rubi1234r17_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "f., m., e., q., b., c. and p."] },
  { rule := rubi1234r18, ruleDecl := ``rubi1234r18, proofs := [],
    counterexamples := [(.real, ``rubi1234r18_counterexample_real), (.complex, ``rubi1234r18_counterexample_complex)],
    findings := [
      "counterexample: at e = 1, f = 1, m = 1, n = 1, n2 = 2, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi1234r18_counterexample_real and rubi1234r18_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "f., m., e., q., c. and p."] },
  { rule := rubi1234r38, ruleDecl := ``rubi1234r38, proofs := [],
    counterexamples := [(.real, ``rubi1234r38_counterexample_real), (.complex, ``rubi1234r38_counterexample_complex)],
    findings := [
      "counterexample: at e = 1, f = 1, m = 1, n = 1, n2 = 2, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1234r38_counterexample_real and rubi1234r38_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, n2 are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; IGtQ[n, 0]; GtQ[m, Add[n, Multiply[-1, 1]]]; NeQ[Add[m, Multiply[n, Add[Multiply[2, p], 1]], 1], 0]; IntegerQ[p]",
      optionalFinding "f., m., e. and c."] },
  { rule := rubi1235r2, ruleDecl := ``rubi1235r2, proofs := [],
    counterexamples := [(.real, ``rubi1235r2_counterexample_real), (.complex, ``rubi1235r2_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, f = 1, n = 1, n2 = 2, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1235r2_counterexample_real and rubi1235r2_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[Multiply[a, e], Multiply[-1, b, d, Add[Multiply[n, Add[p, 1]], 1]]], 0]; EqQ[Add[Multiply[a, f], Multiply[-1, c, d, Add[Multiply[2, n, Add[p, 1]], 1]]], 0]",
      optionalFinding "e., n., f., n2., b., c. and p."] },
  { rule := rubi1235r3, ruleDecl := ``rubi1235r3, proofs := [],
    counterexamples := [(.real, ``rubi1235r3_counterexample_real), (.complex, ``rubi1235r3_counterexample_complex)],
    findings := [
      "counterexample: at b = -1, d = -1, f = -1, n = -1, n2 = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1235r3_counterexample_real and rubi1235r3_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[Multiply[n, Add[p, 1]], 1], 0]; EqQ[Add[Multiply[c, d], Multiply[a, f]], 0]",
      optionalFinding "f., n2., b., n., c. and p."] },
  { rule := rubi1236r3, ruleDecl := ``rubi1236r3, proofs := [],
    counterexamples := [(.real, ``rubi1236r3_counterexample_real), (.complex, ``rubi1236r3_counterexample_complex)],
    findings := [
      "counterexample: at d = 1, e = 1, f = 1, g = 1, m = 1, n = 1, n2 = 2, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1236r3_counterexample_real and rubi1236r3_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[Multiply[a, e, Add[m, 1]], Multiply[-1, b, d, Add[m, Multiply[n, Add[p, 1]], 1]]], 0]; EqQ[Add[Multiply[a, f, Add[m, 1]], Multiply[-1, c, d, Add[m, Multiply[2, n, Add[p, 1]], 1]]], 0]; NeQ[m, -1]",
      optionalFinding "g., m., e., n., f., n2., b., c. and p."] },
  { rule := rubi1236r4, ruleDecl := ``rubi1236r4, proofs := [],
    counterexamples := [(.real, ``rubi1236r4_counterexample_real), (.complex, ``rubi1236r4_counterexample_complex)],
    findings := [
      "counterexample: at c = -2, f = -2, g = -2, m = -2, n = -1, n2 = -2, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1236r4_counterexample_real and rubi1236r4_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[m, Multiply[n, Add[p, 1]], 1], 0]; EqQ[Add[Multiply[c, d], Multiply[a, f]], 0]; NeQ[m, -1]",
      optionalFinding "g., m., f., n2., b., n., c. and p."] },
  { rule := rubi21r7, ruleDecl := ``rubi21r7, proofs := [],
    counterexamples := [(.real, ``rubi21r7_counterexample_real), (.complex, ``rubi21r7_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, d = 1, e = 1, g = 1, m = 1, n = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi21r7_counterexample_real and rubi21r7_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      optionalFinding "c., d., m., b., g., e. and f."] },
  { rule := rubi23r13, ruleDecl := ``rubi23r13, proofs := [],
    counterexamples := [(.real, ``rubi23r13_counterexample_real), (.complex, ``rubi23r13_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, d = 1, e = 1, f = 1, m = 1, n = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi23r13_counterexample_real and rubi23r13_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[m, Add[n, Multiply[-1, 1]]]; EqQ[Add[Multiply[d, e], Multiply[-1, c, f]], 0]",
      optionalFinding "e., f., m., a., b., c. and d."] },
  { rule := rubi23r37, ruleDecl := ``rubi23r37, proofs := [],
    counterexamples := [(.real, ``rubi23r37_counterexample_real), (.complex, ``rubi23r37_counterexample_complex)],
    findings := [
      "counterexample: at a = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorems rubi23r37_counterexample_real and rubi23r37_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      optionalFinding "a., b. and c."] },
  { rule := rubi312r11, ruleDecl := ``rubi312r11, proofs := [],
    counterexamples := [(.real, ``rubi312r11_counterexample_real), (.complex, ``rubi312r11_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, d = 1, m = 1, p = 1, q = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 0 (Lean theorems rubi312r11_counterexample_real and rubi312r11_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      recFinding,
      optionalFinding "d., a., b., c., n. and p."] },
  { rule := rubi321r12, ruleDecl := ``rubi321r12, proofs := [],
    counterexamples := [(.real, ``rubi321r12_counterexample_real), (.complex, ``rubi321r12_counterexample_complex)],
    findings := [
      "counterexample: at A = 1, B = 1, a = -3, b = 1, c = 1, d = 1, e = 1, f = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi321r12_counterexample_real and rubi321r12_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: mn is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[n, mn], 0]; NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]",
      optionalFinding "A., B., e., a., b., n., c., d., f. and g."] },
  { rule := rubi321r2, ruleDecl := ``rubi321r2, proofs := [],
    counterexamples := [(.real, ``rubi321r2_counterexample_real), (.complex, ``rubi321r2_counterexample_complex)],
    findings := [
      "counterexample: at B = 1, a = -3, b = 1, c = 1, d = 1, e = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = -1 (Lean theorems rubi321r2_counterexample_real and rubi321r2_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: mn, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[Add[n, mn], 0]; NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; IGtQ[p, 0]",
      optionalFinding "A., B., e., a., b., n., c., d. and p."] },
  { rule := rubi322r17, ruleDecl := ``rubi322r17, proofs := [],
    counterexamples := [(.real, ``rubi322r17_counterexample_real), (.complex, ``rubi322r17_counterexample_complex)],
    findings := [
      "counterexample: at A = 1, B = 1, a = 1, c = 1, e = 1, f = 1, g = 1, m = 1, mn = -1, n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi322r17_counterexample_real and rubi322r17_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, mn are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[Add[n, mn], 0]; IGtQ[n, 0]; EqQ[Add[Multiply[b, d, f], Multiply[-1, a, c, h]], 0]; EqQ[Add[Multiply[b, d, g], Multiply[-1, h, Add[Multiply[b, c], Multiply[a, d]]]], 0]; IntegerQ[m]",
      optionalFinding "f., g., h., m., A., B., e., a., b., n., c., d. and p."] },
  { rule := rubi35r8, ruleDecl := ``rubi35r8, proofs := [], unproved := [.complex],
    counterexamples := [(.real, ``rubi35r8_counterexample_real)],
    findings := [
      "counterexample: at c = 2, d = -1, e = 2, f = 2, g = 2, m = 2, n = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the residual integrand 1 is not defined at x = 1 (Lean theorem rubi35r8_counterexample_real). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "complex: not proved; the counterexample of the other domain was not established over ℂ.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "GtQ[m, 0]; NeQ[d, 1]",
      optionalFinding "f., g., m., e., c., a., b. and n."] },
  { rule := rubi1234r34, ruleDecl := ``rubi1234r34, proofs := [],
    counterexamples := [(.real, ``rubi1234r34_counterexample_real), (.complex, ``rubi1234r34_counterexample_complex)],
    findings := [
      "counterexample: at a = 4, d = -3, m = 2, n = 1, n2 = 2, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1234r34_counterexample_real and rubi1234r34_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; IGtQ[n, 0]; LtQ[p, -1]; GtQ[m, Add[n, Multiply[-1, 1]]]; IntegerQ[p]",
      optionalFinding "f., m., e., c. and p."] },
  { rule := rubi1234r40, ruleDecl := ``rubi1234r40, proofs := [],
    counterexamples := [(.real, ``rubi1234r40_counterexample_real), (.complex, ``rubi1234r40_counterexample_complex)],
    findings := [
      "counterexample: at d = 2, f = -3, m = -2, n = 1, n2 = 2, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1234r40_counterexample_real and rubi1234r40_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, n2 are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; IGtQ[n, 0]; LtQ[m, -1]; IntegerQ[p]",
      optionalFinding "f., m., e. and c."] },
  { rule := rubi1234r61, ruleDecl := ``rubi1234r61, proofs := [],
    counterexamples := [(.real, ``rubi1234r61_counterexample_real), (.complex, ``rubi1234r61_counterexample_complex)],
    findings := [
      "counterexample: at a = -3, b = -3, c = -1, e = -1, f = 1, m = -2, n = 1, n2 = 2, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1234r61_counterexample_real and rubi1234r61_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; IGtQ[n, 0]; GtQ[p, 0]; LtQ[m, Multiply[-1, n]]",
      optionalFinding "f., a., b., c., n2., p., d. and e."] },
  { rule := rubi1234r64, ruleDecl := ``rubi1234r64, proofs := [],
    counterexamples := [(.real, ``rubi1234r64_counterexample_real), (.complex, ``rubi1234r64_counterexample_complex)],
    findings := [
      "counterexample: at c = 1, e = -2, f = 4, m = -1, n = 2, n2 = 4, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1234r64_counterexample_real and rubi1234r64_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; IGtQ[n, 0]; GtQ[p, 0]; LtQ[m, 0]",
      optionalFinding "f., c., n2., p., d. and e."] },
  { rule := rubi1234r66, ruleDecl := ``rubi1234r66, proofs := [],
    counterexamples := [(.real, ``rubi1234r66_counterexample_real), (.complex, ``rubi1234r66_counterexample_complex)],
    findings := [
      "counterexample: at c = 3, e = 2, m = 2, n = 1, n2 = 2, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1234r66_counterexample_real and rubi1234r66_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; IGtQ[n, 0]; LtQ[p, -1]; GtQ[m, n]",
      optionalFinding "f., m., c., n2., d. and e."] },
  { rule := rubi1234r67, ruleDecl := ``rubi1234r67, proofs := [],
    counterexamples := [(.real, ``rubi1234r67_counterexample_real), (.complex, ``rubi1234r67_counterexample_complex)],
    findings := [
      "counterexample: at b = 4, d = 3, f = -1, m = 3, n = 2, n2 = 4, p = -3 and the other metavariables 0 the conditions hold and the integrand is defined near x = 1, but the result is not defined at x = 1 (Lean theorems rubi1234r67_counterexample_real and rubi1234r67_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: m, n, n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; IGtQ[n, 0]; LtQ[p, -1]; GtQ[m, 0]",
      optionalFinding "f., m., a., b., c., n2., d. and e."] },
  { rule := rubi1235r6, ruleDecl := ``rubi1235r6, proofs := [],
    counterexamples := [(.real, ``rubi1235r6_counterexample_real), (.complex, ``rubi1235r6_counterexample_complex)],
    findings := [
      "counterexample: at b = 4, e = 2, f = -3 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1235r6_counterexample_real and rubi1235r6_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2, n3 are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[n3, Multiply[3, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[Power[a, 2], g, Add[n, 1]], Multiply[-1, c, Add[Multiply[n, Add[Multiply[2, p], 3]], 1], Add[Multiply[a, e], Multiply[-1, b, d, Add[Multiply[n, Add[p, 1]], 1]]]]], 0]; EqQ[Add[Multiply[Power[a, 2], f, Add[n, 1]], Multiply[-1, a, c, d, Add[n, 1], Add[Multiply[2, n, Add[p, 1]], 1]], Multiply[-1, b, Add[Multiply[n, Add[p, 2]], 1], Add[Multiply[a, e], Multiply[-1, b, d, Add[Multiply[n, Add[p, 1]], 1]]]]], 0]",
      optionalFinding "e., f., n2., g., n3., b., c. and p."] },
  { rule := rubi1235r7, ruleDecl := ``rubi1235r7, proofs := [],
    counterexamples := [(.real, ``rubi1235r7_counterexample_real), (.complex, ``rubi1235r7_counterexample_complex)],
    findings := [
      "counterexample: at b = -1, f = -3, g = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1235r7_counterexample_real and rubi1235r7_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2, n3 are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[n3, Multiply[3, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[Power[a, 2], g, Add[n, 1]], Multiply[c, b, d, Add[Multiply[n, Add[Multiply[2, p], 3]], 1], Add[Multiply[n, Add[p, 1]], 1]]], 0]; EqQ[Add[Multiply[Power[a, 2], f, Add[n, 1]], Multiply[-1, a, c, d, Add[n, 1], Add[Multiply[2, n, Add[p, 1]], 1]], Multiply[Power[b, 2], d, Add[Multiply[n, Add[p, 2]], 1], Add[Multiply[n, Add[p, 1]], 1]]], 0]",
      optionalFinding "f., n2., g., n3., b., c. and p."] },
  { rule := rubi1235r8, ruleDecl := ``rubi1235r8, proofs := [],
    counterexamples := [(.real, ``rubi1235r8_counterexample_real), (.complex, ``rubi1235r8_counterexample_complex)],
    findings := [
      "counterexample: at b = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1235r8_counterexample_real and rubi1235r8_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2, n3 are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[n3, Multiply[3, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[Power[a, 2], g, Add[n, 1]], Multiply[-1, c, Add[Multiply[n, Add[Multiply[2, p], 3]], 1], Add[Multiply[a, e], Multiply[-1, b, d, Add[Multiply[n, Add[p, 1]], 1]]]]], 0]; EqQ[Add[Multiply[a, c, d, Add[n, 1], Add[Multiply[2, n, Add[p, 1]], 1]], Multiply[b, Add[Multiply[n, Add[p, 2]], 1], Add[Multiply[a, e], Multiply[-1, b, d, Add[Multiply[n, Add[p, 1]], 1]]]]], 0]",
      optionalFinding "e., g., n3., b., c., n2. and p."] },
  { rule := rubi1235r9, ruleDecl := ``rubi1235r9, proofs := [],
    counterexamples := [(.real, ``rubi1235r9_counterexample_real), (.complex, ``rubi1235r9_counterexample_complex)],
    findings := [
      "counterexample: at b = -2, p = 4 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1235r9_counterexample_real and rubi1235r9_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: n2, n3 are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[n3, Multiply[3, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[Power[a, 2], g, Add[n, 1]], Multiply[c, b, d, Add[Multiply[n, Add[Multiply[2, p], 3]], 1], Add[Multiply[n, Add[p, 1]], 1]]], 0]; EqQ[Add[Multiply[a, c, d, Add[n, 1], Add[Multiply[2, n, Add[p, 1]], 1]], Multiply[-1, Power[b, 2], d, Add[Multiply[n, Add[p, 2]], 1], Add[Multiply[n, Add[p, 1]], 1]]], 0]",
      optionalFinding "g., n3., b., c., n2. and p."] },
  { rule := rubi321r10, ruleDecl := ``rubi321r10, proofs := [],
    counterexamples := [(.real, ``rubi321r10_counterexample_real), (.complex, ``rubi321r10_counterexample_complex)],
    findings := [
      "counterexample: at b = -1, c = 2, e = 3, f = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi321r10_counterexample_real and rubi321r10_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: mn is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[n, mn], 0]; NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[d, f], Multiply[-1, c, g]], 0]",
      optionalFinding "A., B., e., a., b., n., c., d., f. and g."] },
  { rule := rubi321r8, ruleDecl := ``rubi321r8, proofs := [],
    counterexamples := [(.real, ``rubi321r8_counterexample_real), (.complex, ``rubi321r8_counterexample_complex)],
    findings := [
      "counterexample: at A = 2, B = 4, a = -2, d = 2, e = 3, f = -1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi321r8_counterexample_real and rubi321r8_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.",
      "independence: mn is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[n, mn], 0]; NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[b, f], Multiply[-1, a, g]], 0]",
      optionalFinding "A., B., e., a., b., n., c., d., f. and g."] },
  { rule := improperTrinomEq, ruleDecl := ``improperTrinomEq,
    proofs := [(.real, ``improperTrinomEq_real), (.complex, ``improperTrinomEq_complex)],
    findings := [
      "independence: q, r are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n, q]; EqQ[r, n]", optionalFinding "a., q., b., n., c. and r."] },
  { rule := monoImproperTrinomEq, ruleDecl := ``monoImproperTrinomEq,
    proofs := [(.real, ``monoImproperTrinomEq_real), (.complex, ``monoImproperTrinomEq_complex)],
    findings := [
      "independence: q, r are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[q, n]; EqQ[r, n]", optionalFinding "m., a., q., b., n., c., r. and p."] },
  { rule := trinomNegPow, ruleDecl := ``trinomNegPow,
    proofs := [(.real, ``trinomNegPow_real), (.complex, ``trinomNegPow_complex)],
    findings := [
      "independence: n, n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; LtQ[n, 0]; IntegerQ[p]", optionalFinding "b., c., n2. and p."] },
  { rule := pfMonoBinomPair, ruleDecl := ``pfMonoBinomPair,
    proofs := [(.real, ``pfMonoBinomPair_real), (.complex, ``pfMonoBinomPair_complex)],
    findings := [
      "independence: n is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; IGtQ[n, 0]", optionalFinding "e., m., b. and d."] },
  { rule := binomTripleNegFlip, ruleDecl := ``binomTripleNegFlip,
    proofs := [(.real, ``binomTripleNegFlip_real), (.complex, ``binomTripleNegFlip_complex)],
    findings := [
      "independence: mn, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[mn, Multiply[-1, n]]; IntegerQ[q]", optionalFinding "a., b., n., p., d., mn., q., f. and r."] },
  { rule := monoBinomTripleNegFlip, ruleDecl := ``monoBinomTripleNegFlip,
    proofs := [(.real, ``monoBinomTripleNegFlip_real), (.complex, ``monoBinomTripleNegFlip_complex)],
    findings := [
      "independence: mn, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[mn, Multiply[-1, n]]; IntegerQ[q]", optionalFinding "m., b., n., p., d., mn., q., f. and r."] },
  { rule := binomTriplePosFlip, ruleDecl := ``binomTriplePosFlip,
    proofs := [(.real, ``binomTriplePosFlip_real), (.complex, ``binomTriplePosFlip_complex)],
    findings := [
      "independence: mn, p, r are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[mn, Multiply[-1, n]]; IntegerQ[p]; IntegerQ[r]", optionalFinding "a., b., n., p., d., mn., q., f. and r."] },
  { rule := monoBinomTriplePosFlip, ruleDecl := ``monoBinomTriplePosFlip,
    proofs := [(.real, ``monoBinomTriplePosFlip_real), (.complex, ``monoBinomTriplePosFlip_complex)],
    findings := [
      "independence: mn, p, r are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[mn, Multiply[-1, n]]; IntegerQ[p]; IntegerQ[r]", optionalFinding "m., a., b., n., p., d., mn., q., f. and r."] },
  { rule := linTrinomSplit, ruleDecl := ``linTrinomSplit,
    proofs := [(.real, ``linTrinomSplit_real), (.complex, ``linTrinomSplit_complex)],
    findings := [
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[m, Multiply[-1, n], 1], 0]", optionalFinding "B., m., e., q., b., c. and p."] },
  { rule := linBinomSplit, ruleDecl := ``linBinomSplit,
    proofs := [(.real, ``linBinomSplit_real), (.complex, ``linBinomSplit_complex)],
    findings := [
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[m, Multiply[-1, n], 1], 0]", optionalFinding "B., m., e., q., c. and p."] },
  { rule := linearPowerNondeg, ruleDecl := ``linearPowerNondeg,
    proofs := [(.real, ``linearPowerNondeg_real), (.complex, ``linearPowerNondeg_complex)],
    findings := [
      "strengthened: the condition b (m + 1) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.linear_power, which stays refuted.",
      neqFinding "NeQ[m, -1]", optionalFinding "a. and b."] },
  { rule := constTimesLinearNondeg, ruleDecl := ``constTimesLinearNondeg,
    proofs := [(.real, ``constTimesLinearNondeg_real), (.complex, ``constTimesLinearNondeg_complex)],
    findings := [
      "strengthened: the condition 2 c ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.constant_times_linear, which stays refuted.",
      optionalFinding "c." false] },
  { rule := rubi41_13r11Nondeg, ruleDecl := ``rubi41_13r11Nondeg,
    proofs := [(.real, ``rubi41_13r11Nondeg_real), (.complex, ``rubi41_13r11Nondeg_complex)],
    findings := [
      "strengthened: the condition 2 c ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r11, which stays refuted.",
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]",
      optionalFinding "e., a., b. and c."] },
  { rule := rubi41_13r12Nondeg, ruleDecl := ``rubi41_13r12Nondeg,
    proofs := [(.real, ``rubi41_13r12Nondeg_real), (.complex, ``rubi41_13r12Nondeg_complex)],
    findings := [
      "strengthened: the condition 2 c ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r12, which stays refuted.",
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]",
      optionalFinding "e., a., b. and c."] },
  { rule := rubi1112r1Nondeg, ruleDecl := ``rubi1112r1Nondeg,
    proofs := [(.real, ``rubi1112r1Nondeg_real), (.complex, ``rubi1112r1Nondeg_complex)],
    findings := [
      "strengthened: the condition b (m + 2) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_1_2_r1, which stays refuted.",
      condFinding "EqQ[Add[Multiply[a, d], Multiply[-1, b, c, Add[m, 2]]], 0]",
      optionalFinding "b., m. and d."] },
  { rule := rubi1132r3Nondeg, ruleDecl := ``rubi1132r3Nondeg,
    proofs := [(.real, ``rubi1132r3Nondeg_real), (.complex, ``rubi1132r3Nondeg_complex)],
    findings := [
      "strengthened: the condition b n (p + 1) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_2_r3, which stays refuted.",
      condFinding "EqQ[m, Add[n, Multiply[-1, 1]]]; NeQ[p, -1]",
      optionalFinding "m. and b."] },
  { rule := rubi1131r3Nondeg, ruleDecl := ``rubi1131r3Nondeg,
    proofs := [(.real, ``rubi1131r3Nondeg_real), (.complex, ``rubi1131r3Nondeg_complex)],
    findings := [
      "strengthened: the condition a ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_1_r3, which stays refuted.",
      condFinding "EqQ[Add[Multiply[1, Power[n, -1]], p, 1], 0]",
      optionalFinding "b." false] },
  { rule := rubi1132r6Nondeg, ruleDecl := ``rubi1132r6Nondeg,
    proofs := [(.real, ``rubi1132r6Nondeg_real), (.complex, ``rubi1132r6Nondeg_complex)],
    findings := [
      "strengthened: the condition a c (m + 1) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_2_r6, which stays refuted.",
      condFinding "EqQ[Add[Multiply[Add[m, 1], Power[n, -1]], p, 1], 0]; NeQ[m, -1]",
      optionalFinding "c., m. and b."] },
  { rule := rubi1133r10Nondeg, ruleDecl := ``rubi1133r10Nondeg,
    proofs := [(.real, ``rubi1133r10Nondeg_real), (.complex, ``rubi1133r10Nondeg_complex)],
    findings := [
      "strengthened: the condition a ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_3_r10, which stays refuted.",
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[a, d], Multiply[-1, b, c, Add[Multiply[n, Add[p, 1]], 1]]], 0]",
      optionalFinding "b., p. and d."] },
  { rule := rubi1134r14Nondeg, ruleDecl := ``rubi1134r14Nondeg,
    proofs := [(.real, ``rubi1134r14Nondeg_real), (.complex, ``rubi1134r14Nondeg_complex)],
    findings := [
      "strengthened: the condition a e (m + 1) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_4_r14, which stays refuted.",
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[a, d, Add[m, 1]], Multiply[-1, b, c, Add[m, Multiply[n, Add[p, 1]], 1]]], 0]; NeQ[m, -1]",
      optionalFinding "e., m., b., p. and d."] },
  { rule := rubi1212r4Nondeg, ruleDecl := ``rubi1212r4Nondeg,
    proofs := [(.real, ``rubi1212r4Nondeg_real), (.complex, ``rubi1212r4Nondeg_complex)],
    findings := [
      "strengthened: the condition b (p + 1) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r4, which stays refuted.",
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; NeQ[p, -1]",
      optionalFinding "e., a., b., c. and p."] },
  { rule := rubi1213r1Nondeg, ruleDecl := ``rubi1213r1Nondeg,
    proofs := [(.real, ``rubi1213r1Nondeg_real), (.complex, ``rubi1213r1Nondeg_complex)],
    findings := [
      "strengthened: the condition c (m + 2 p + 2) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_3_r1, which stays refuted.",
      condFinding "EqQ[Add[Multiply[b, g, Add[m, p, 1]], Multiply[-1, c, f, Add[m, Multiply[2, p], 2]]], 0]; NeQ[Add[m, Multiply[2, p], 2], 0]",
      optionalFinding "e., m., g., b., c. and p."] },
  { rule := rubi1214r1Nondeg, ruleDecl := ``rubi1214r1Nondeg,
    proofs := [(.real, ``rubi1214r1Nondeg_real), (.complex, ``rubi1214r1Nondeg_complex)],
    findings := [
      "strengthened: the condition g (m + n + 3) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_4_r1, which stays refuted.",
      condFinding "EqQ[Add[Multiply[c, f, Add[m, 2]], Multiply[-1, b, g, Add[m, n, 3]]], 0]; NeQ[Add[m, n, 3], 0]",
      optionalFinding "m., g., n., b. and c."] },
  { rule := rubi1113r2Nondeg, ruleDecl := ``rubi1113r2Nondeg,
    proofs := [(.real, ``rubi1113r2Nondeg_real), (.complex, ``rubi1113r2Nondeg_complex)],
    findings := [
      "strengthened: the condition d f (n + p + 2) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_1_3_r2, which stays refuted.",
      condFinding "NeQ[Add[n, p, 2], 0]; EqQ[Add[Multiply[a, d, f, Add[n, p, 2]], Multiply[-1, b, Add[Multiply[d, e, Add[n, 1]], Multiply[c, f, Add[p, 1]]]]], 0]",
      optionalFinding "a., b., c., d., n., e., f. and p."] },
  { rule := rubi1211r3Nondeg, ruleDecl := ``rubi1211r3Nondeg,
    proofs := [(.real, ``rubi1211r3Nondeg_real), (.complex, ``rubi1211r3Nondeg_complex)],
    findings := [
      "strengthened: the condition 2 c (2 p + 1) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_1_r3, which stays refuted.",
      condFinding "EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; NeQ[p, Multiply[-1, Power[2, -1]]]",
      optionalFinding "b. and c."] },
  { rule := rubi1212r55Nondeg, ruleDecl := ``rubi1212r55Nondeg,
    proofs := [(.real, ``rubi1212r55Nondeg_real), (.complex, ``rubi1212r55Nondeg_complex)],
    findings := [
      "strengthened: the condition e (p + 1) (b^2 - 4 a c) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r55, which stays refuted.",
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; EqQ[Add[m, Multiply[2, p], 3], 0]; NeQ[p, -1]",
      optionalFinding "e., a., b., c. and p."] },
  { rule := rubi4112r81Nondeg, ruleDecl := ``rubi4112r81Nondeg,
    proofs := [(.real, ``rubi4112r81Nondeg_real), (.complex, ``rubi4112r81Nondeg_complex)],
    findings := [
      "strengthened: the condition b n (p + 1) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_12_r81, which stays refuted.",
      condFinding "EqQ[m, Add[n, Multiply[-1, 1]]]; NeQ[p, -1]",
      optionalFinding "m., a., b., n. and p."] },
  { rule := rubi4112r82Nondeg, ruleDecl := ``rubi4112r82Nondeg,
    proofs := [(.real, ``rubi4112r82Nondeg_real), (.complex, ``rubi4112r82Nondeg_complex)],
    findings := [
      "strengthened: the condition b n (p + 1) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_12_r82, which stays refuted.",
      condFinding "EqQ[m, Add[n, Multiply[-1, 1]]]; NeQ[p, -1]",
      optionalFinding "m., a., b., n. and p."] },
  { rule := rubi1214r65Nondeg, ruleDecl := ``rubi1214r65Nondeg,
    proofs := [(.real, ``rubi1214r65Nondeg_real), (.complex, ``rubi1214r65Nondeg_complex)],
    findings := [
      "strengthened: the condition c e (m + 2 p + 3) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_4_r65, which stays refuted.",
      condFinding "EqQ[Add[Multiply[b, e, Add[m, p, 2]], Multiply[2, c, d, Add[p, 1]]], 0]; EqQ[Add[Multiply[b, d, Add[p, 1]], Multiply[a, e, Add[m, 1]]], 0]; NeQ[Add[m, Multiply[2, p], 3], 0]",
      optionalFinding "d., e., m., a., b., c. and p."] }
]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem catalogPart4_wellFormed : ∀ e ∈ catalogPart4,
    (if e.rule.shape == .antiderivRec then e.rule.recOk else e.rule.wellFormed) = true := by
  intro e he
  simp only [catalogPart4, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The Integration catalogue, in v0.1 file order: part 5. -/
def catalogPart5 : List CEntry := [
  { rule := rubi1214r66Nondeg, ruleDecl := ``rubi1214r66Nondeg,
    proofs := [(.real, ``rubi1214r66Nondeg_real), (.complex, ``rubi1214r66Nondeg_complex)],
    findings := [
      "strengthened: the condition c e (m + 2 p + 3) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_4_r66, which stays refuted.",
      condFinding "EqQ[Multiply[d, Add[p, 1]], 0]; EqQ[Multiply[a, Add[m, 1]], 0]; NeQ[Add[m, Multiply[2, p], 3], 0]",
      optionalFinding "d., e., m., a., c. and p."] },
  { rule := rubi1235r2Nondeg, ruleDecl := ``rubi1235r2Nondeg,
    proofs := [(.real, ``rubi1235r2Nondeg_real), (.complex, ``rubi1235r2Nondeg_complex)],
    findings := [
      "strengthened: the condition a ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_3_5_r2, which stays refuted.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[Multiply[a, e], Multiply[-1, b, d, Add[Multiply[n, Add[p, 1]], 1]]], 0]; EqQ[Add[Multiply[a, f], Multiply[-1, c, d, Add[Multiply[2, n, Add[p, 1]], 1]]], 0]",
      optionalFinding "e., n., f., n2., b., c. and p."] },
  { rule := rubi1213r14Nondeg, ruleDecl := ``rubi1213r14Nondeg,
    proofs := [(.real, ``rubi1213r14Nondeg_real), (.complex, ``rubi1213r14Nondeg_complex)],
    findings := [
      "strengthened: the condition 2 c (p + 1) (2 p + 3) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_3_r14, which stays refuted.",
      condFinding "EqQ[Add[Multiply[a, e, g], Multiply[-1, c, d, f, Add[Multiply[2, p], 3]]], 0]; NeQ[p, -1]",
      optionalFinding "d., e., f., g. and c."] },
  { rule := rubi1213r13Nondeg, ruleDecl := ``rubi1213r13Nondeg,
    proofs := [(.real, ``rubi1213r13Nondeg_real), (.complex, ``rubi1213r13Nondeg_complex)],
    findings := [
      "strengthened: the condition 2 c^2 (p + 1) (2 p + 3) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_3_r13, which stays refuted.",
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[Power[b, 2], e, g, Add[p, 2]], Multiply[-1, 2, a, c, e, g], Multiply[c, Add[Multiply[2, c, d, f], Multiply[-1, b, Add[Multiply[e, f], Multiply[d, g]]]], Add[Multiply[2, p], 3]]], 0]; NeQ[p, -1]",
      optionalFinding "d., e., f., g., a., b. and c."] },
  { rule := rubi1117r6Nondeg, ruleDecl := ``rubi1117r6Nondeg,
    proofs := [(.real, ``rubi1117r6Nondeg_real), (.complex, ``rubi1117r6Nondeg_complex)],
    findings := [
      "strengthened: the condition 2 b1 b2 n (p + 1) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_1_7_r6, which stays refuted.",
      condFinding "EqQ[Add[Multiply[a2, b1], Multiply[a1, b2]], 0]; EqQ[Add[m, Multiply[-1, 2, n], 1], 0]; NeQ[p, -1]",
      optionalFinding "m., b1., n. and b2."] },
  { rule := rubi1113r9Nondeg, ruleDecl := ``rubi1113r9Nondeg,
    proofs := [(.real, ``rubi1113r9Nondeg_real), (.complex, ``rubi1113r9Nondeg_complex)],
    findings := [
      "strengthened: the condition d^2 f^2 (n + p + 2) (n + p + 3) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_1_3_r9, which stays refuted.",
      condFinding "NeQ[Add[n, p, 2], 0]; NeQ[Add[n, p, 3], 0]; EqQ[Add[Multiply[d, f, Add[n, p, 2], Add[Multiply[Power[a, 2], d, f, Add[n, p, 3]], Multiply[-1, b, Add[Multiply[b, c, e], Multiply[a, Add[Multiply[d, e, Add[n, 1]], Multiply[c, f, Add[p, 1]]]]]]]], Multiply[-1, b, Add[Multiply[d, e, Add[n, 1]], Multiply[c, f, Add[p, 1]]], Add[Multiply[a, d, f, Add[n, p, 4]], Multiply[-1, b, Add[Multiply[d, e, Add[n, 2]], Multiply[c, f, Add[p, 2]]]]]]], 0]",
      optionalFinding "a., b., c., d., n., e., f. and p."] },
  { rule := rubi1213r25Nondeg, ruleDecl := ``rubi1213r25Nondeg,
    proofs := [(.real, ``rubi1213r25Nondeg_real), (.complex, ``rubi1213r25Nondeg_complex)],
    findings := [
      "strengthened: the conditions c (m + 2 p + 2) ≠ 0 and e ≠ 0 (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_3_r25, which stays refuted, and the case e = d = m = 0, f ≠ 0, where the result with only the first condition is not an antiderivative.",
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; EqQ[Add[Multiply[m, Add[Multiply[d, g], Multiply[e, f]]], Multiply[2, e, f, Add[p, 1]]], 0]",
      optionalFinding "e., f., g. and c."] },
  { rule := rubi1213r24Nondeg, ruleDecl := ``rubi1213r24Nondeg,
    proofs := [(.real, ``rubi1213r24Nondeg_real), (.complex, ``rubi1213r24Nondeg_complex)],
    findings := [
      "strengthened: the conditions c (m + 2 p + 2) ≠ 0 and e ≠ 0 (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_3_r24, which stays refuted, and the case e = d = m = 0, where the result with only the first condition is not an antiderivative.",
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; EqQ[Add[Multiply[m, Add[Multiply[g, Add[Multiply[c, d], Multiply[-1, b, e]]], Multiply[c, e, f]]], Multiply[e, Add[p, 1], Add[Multiply[2, c, f], Multiply[-1, b, g]]]], 0]",
      optionalFinding "d., e., f., g., a., b. and c."] },
  { rule := rubi1212r20Nondeg, ruleDecl := ``rubi1212r20Nondeg,
    proofs := [(.real, ``rubi1212r20Nondeg_real), (.complex, ``rubi1212r20Nondeg_complex)],
    findings := [
      "strengthened: the condition e^p ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r20, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IntegerQ[p]",
      optionalFinding "e., m., b., c. and p."] },
  { rule := rubi1212r103Nondeg, ruleDecl := ``rubi1212r103Nondeg,
    proofs := [(.real, ``rubi1212r103Nondeg_real), (.complex, ``rubi1212r103Nondeg_complex)],
    findings := [
      "strengthened: the condition (m + 1) (c d^2 - b d e + a e^2) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r103, which stays refuted.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; NeQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; NeQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; EqQ[Add[m, Multiply[2, p], 3], 0]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi1212r104Nondeg, ruleDecl := ``rubi1212r104Nondeg,
    proofs := [(.real, ``rubi1212r104Nondeg_real), (.complex, ``rubi1212r104Nondeg_complex)],
    findings := [
      "strengthened: the condition (m + 1) (c d^2 + a e^2) ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r104, which stays refuted.",
      recFinding,
      condFinding "NeQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; EqQ[Add[m, Multiply[2, p], 3], 0]",
      optionalFinding "e. and c."] },
  { rule := rubi1212r1Nondeg, ruleDecl := ``rubi1212r1Nondeg,
    proofs := [(.real, ``rubi1212r1Nondeg_real), (.complex, ``rubi1212r1Nondeg_complex)],
    findings := [
      "strengthened: the conditions d ≠ 0 and e ≠ 0 (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r1, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., m., a., b., c. and p."] },
  { rule := rubi1213r20Nondeg, ruleDecl := ``rubi1213r20Nondeg,
    proofs := [(.real, ``rubi1213r20Nondeg_real), (.complex, ``rubi1213r20Nondeg_complex)],
    findings := [
      "strengthened: the conditions d ≠ 0 and e ≠ 0 (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_3_r20, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., f., g., a., b., c. and p."] },
  { rule := rubi1213r19Nondeg, ruleDecl := ``rubi1213r19Nondeg,
    proofs := [(.real, ``rubi1213r19Nondeg_real), (.complex, ``rubi1213r19Nondeg_complex)],
    findings := [
      "strengthened: the condition e^p ≠ 0 (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_3_r19, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IntegerQ[p]",
      optionalFinding "e., m., f., g., b., c. and p."] },
  { rule := rubi1223r7Nondeg, ruleDecl := ``rubi1223r7Nondeg, 
    proofs := [(.real, ``rubi1223r7Nondeg_real), (.complex, ``rubi1223r7Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[d, 0]; NeQ[e, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_2_3_r7, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., q., b., c. and p."] },
  { rule := rubi1223r8Nondeg, ruleDecl := ``rubi1223r8Nondeg, 
    proofs := [(.real, ``rubi1223r8Nondeg_real), (.complex, ``rubi1223r8Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[d, 0]; NeQ[e, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_2_3_r8, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., q., c. and p."] },
  { rule := rubi1133r15Nondeg, ruleDecl := ``rubi1133r15Nondeg, 
    proofs := [(.real, ``rubi1133r15Nondeg_real), (.complex, ``rubi1133r15Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[b, Add[Multiply[n, Add[p, 1]], 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_3_r15, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; NeQ[Add[Multiply[n, Add[p, 1]], 1], 0]",
      optionalFinding "b. and d."] },
  { rule := binomPowLinNondeg, ruleDecl := ``binomPowLinNondeg, 
    proofs := [(.real, ``binomPowLinNondeg_real), (.complex, ``binomPowLinNondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[b, e, Add[m, Multiply[n, Add[p, 1]], 1]], 0]; NeQ[Multiply[b, Add[m, Multiply[n, Add[p, 1]], 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.power_binomial_times_linear, which stays refuted.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; NeQ[Add[m, Multiply[n, Add[p, 1]], 1], 0]",
      optionalFinding "e., m., b., p. and d."] },
  { rule := rubi1134r17Nondeg, ruleDecl := ``rubi1134r17Nondeg, 
    proofs := [(.real, ``rubi1134r17Nondeg_real), (.complex, ``rubi1134r17Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[a, b, e, Add[m, 1]], 0]; NeQ[b, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_4_r17, which stays refuted.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[m, Multiply[n, Add[p, 1]], 1], 0]; NeQ[m, -1]",
      optionalFinding "e., m., b., p. and d."] },
  { rule := rubi1213r35Nondeg, ruleDecl := ``rubi1213r35Nondeg, 
    proofs := [(.real, ``rubi1213r35Nondeg_real), (.complex, ``rubi1213r35Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[c, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_3_r35, which stays refuted.",
      recFinding,
      condFinding "EqQ[Add[Multiply[a, Power[g, 2]], Multiply[Power[f, 2], c]], 0]",
      optionalFinding "g. and c."] },
  { rule := rubi1224r11Nondeg, ruleDecl := ``rubi1224r11Nondeg, 
    proofs := [(.real, ``rubi1224r11Nondeg_real), (.complex, ``rubi1224r11Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[d, 0]; NeQ[e, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_2_4_r11, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "f., m., e., q., b., c. and p."] },
  { rule := rubi1224r12Nondeg, ruleDecl := ``rubi1224r12Nondeg, 
    proofs := [(.real, ``rubi1224r12Nondeg_real), (.complex, ``rubi1224r12Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[d, 0]; NeQ[e, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_2_4_r12, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "f., m., e., q., c. and p."] },
  { rule := rubi1233r12Nondeg, ruleDecl := ``rubi1233r12Nondeg, 
    proofs := [(.real, ``rubi1233r12Nondeg_real), (.complex, ``rubi1233r12Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[d, 0]; NeQ[e, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_3_3_r12, which stays refuted.",
      "independence: n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., q., c. and p."] },
  { rule := rubi1233r19Nondeg, ruleDecl := ``rubi1233r19Nondeg, 
    proofs := [(.real, ``rubi1233r19Nondeg_real), (.complex, ``rubi1233r19Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[e, Add[Multiply[n, Add[q, 2]], 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_3_3_r19, which stays refuted.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; NeQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]",
      optionalFinding "e., b. and c."] },
  { rule := rubi1233r20Nondeg, ruleDecl := ``rubi1233r20Nondeg, 
    proofs := [(.real, ``rubi1233r20Nondeg_real), (.complex, ``rubi1233r20Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[e, Add[Multiply[n, Add[q, 2]], 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_3_3_r20, which stays refuted.",
      "independence: n2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]",
      optionalFinding "e. and c."] },
  { rule := rubi1216r5Nondeg, ruleDecl := ``rubi1216r5Nondeg, 
    proofs := [(.real, ``rubi1216r5Nondeg_real), (.complex, ``rubi1216r5Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[a, 0]; NeQ[c, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_6_r5, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[g, 2]], Multiply[-1, b, g, h], Multiply[a, Power[h, 2]]], 0]; EqQ[Add[Multiply[Power[c, 2], d, Power[g, 2]], Multiply[-1, a, c, e, g, h], Multiply[Power[a, 2], f, Power[h, 2]]], 0]; IntegerQ[m]",
      optionalFinding "h., m., b., c., d., e. and f."] },
  { rule := rubi1216r6Nondeg, ruleDecl := ``rubi1216r6Nondeg, 
    proofs := [(.real, ``rubi1216r6Nondeg_real), (.complex, ``rubi1216r6Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[a, 0]; NeQ[c, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_6_r6, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[g, 2]], Multiply[a, Power[h, 2]]], 0]; EqQ[Add[Multiply[Power[c, 2], d, Power[g, 2]], Multiply[-1, a, c, e, g, h], Multiply[Power[a, 2], f, Power[h, 2]]], 0]; IntegerQ[m]",
      optionalFinding "h., m., c., d., e. and f."] },
  { rule := rubi1216r7Nondeg, ruleDecl := ``rubi1216r7Nondeg, 
    proofs := [(.real, ``rubi1216r7Nondeg_real), (.complex, ``rubi1216r7Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[a, 0]; NeQ[c, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_6_r7, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[g, 2]], Multiply[-1, b, g, h], Multiply[a, Power[h, 2]]], 0]; EqQ[Add[Multiply[Power[c, 2], d, Power[g, 2]], Multiply[Power[a, 2], f, Power[h, 2]]], 0]; IntegerQ[m]",
      optionalFinding "h., m., b., c., d. and f."] },
  { rule := rubi1216r8Nondeg, ruleDecl := ``rubi1216r8Nondeg, 
    proofs := [(.real, ``rubi1216r8Nondeg_real), (.complex, ``rubi1216r8Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[a, 0]; NeQ[c, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_6_r8, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[g, 2]], Multiply[a, Power[h, 2]]], 0]; EqQ[Add[Multiply[Power[c, 2], d, Power[g, 2]], Multiply[Power[a, 2], f, Power[h, 2]]], 0]; IntegerQ[m]",
      optionalFinding "h., m., c., d. and f."] },
  { rule := rubi1216r10Nondeg, ruleDecl := ``rubi1216r10Nondeg, 
    proofs := [(.real, ``rubi1216r10Nondeg_real), (.complex, ``rubi1216r10Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[e, 0]; NeQ[f, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_6_r10, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[e, 2]], Multiply[a, Power[f, 2]]], 0]; IntegerQ[p]",
      optionalFinding "c., e. and f."] },
  { rule := rubi1216r9Nondeg, ruleDecl := ``rubi1216r9Nondeg, 
    proofs := [(.real, ``rubi1216r9Nondeg_real), (.complex, ``rubi1216r9Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[e, 0]; NeQ[f, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_6_r9, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[e, 2]], Multiply[-1, b, e, f], Multiply[a, Power[f, 2]]], 0]; IntegerQ[p]",
      optionalFinding "a., b., c., e. and f."] },
  { rule := rubi1213r36Nondeg, ruleDecl := ``rubi1213r36Nondeg, 
    proofs := [(.real, ``rubi1213r36Nondeg_real), (.complex, ``rubi1213r36Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[f, 0]; NeQ[g, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_3_r36, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[f, 2]], Multiply[-1, b, f, g], Multiply[a, Power[g, 2]]], 0]; IntegerQ[p]",
      optionalFinding "e., f., g., a., b., c. and p."] },
  { rule := rubi1224r55Nondeg, ruleDecl := ``rubi1224r55Nondeg, 
    proofs := [(.real, ``rubi1224r55Nondeg_real), (.complex, ``rubi1224r55Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Power[d, 2], 0]; NeQ[Multiply[Power[d, 2], Power[f, 4]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_2_4_r55, which stays refuted.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; GtQ[p, 0]; LtQ[m, -2]",
      optionalFinding "f., a., b., c., p., d. and e."] },
  { rule := rubi1224r56Nondeg, ruleDecl := ``rubi1224r56Nondeg, 
    proofs := [(.real, ``rubi1224r56Nondeg_real), (.complex, ``rubi1224r56Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Power[d, 2], 0]; NeQ[Multiply[Power[d, 2], Power[f, 4]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_2_4_r56, which stays refuted.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "GtQ[p, 0]; LtQ[m, -2]",
      optionalFinding "f., c., p., d. and e."] },
  { rule := rubi1224r57Nondeg, ruleDecl := ``rubi1224r57Nondeg, 
    proofs := [(.real, ``rubi1224r57Nondeg_real), (.complex, ``rubi1224r57Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[d, e], 0]; NeQ[Multiply[d, e, Power[f, 2]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_2_4_r57, which stays refuted.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; GtQ[p, 0]; LtQ[m, 0]",
      optionalFinding "f., a., b., c., p., d. and e."] },
  { rule := rubi1224r58Nondeg, ruleDecl := ``rubi1224r58Nondeg, 
    proofs := [(.real, ``rubi1224r58Nondeg_real), (.complex, ``rubi1224r58Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[d, e], 0]; NeQ[Multiply[d, e, Power[f, 2]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_2_4_r58, which stays refuted.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "GtQ[p, 0]; LtQ[m, 0]",
      optionalFinding "f., c., p., d. and e."] },
  { rule := rubi1113r12Nondeg, ruleDecl := ``rubi1113r12Nondeg, 
    proofs := [(.real, ``rubi1113r12Nondeg_real), (.complex, ``rubi1113r12Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_1_3_r12, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[0, p, 1]",
      optionalFinding "e., f., a., b., c. and d."] },
  { rule := rubi1114r38Nondeg, ruleDecl := ``rubi1114r38Nondeg, 
    proofs := [(.real, ``rubi1114r38Nondeg_real), (.complex, ``rubi1114r38Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_1_4_r38, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[0, p, 1]",
      optionalFinding "e., f., g., h., a., b., c. and d."] },
  { rule := rubi1212r12Nondeg, ruleDecl := ``rubi1212r12Nondeg, 
    proofs := [(.real, ``rubi1212r12Nondeg_real), (.complex, ``rubi1212r12Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[2, a, c, Add[p, 1]], 0]; NeQ[Multiply[2, a, Add[p, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r12, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]; NeQ[p, Multiply[-3, Power[2, -1]]]",
      optionalFinding "e. and c."] },
  { rule := rubi1213r16Nondeg, ruleDecl := ``rubi1213r16Nondeg, 
    proofs := [(.real, ``rubi1213r16Nondeg_real), (.complex, ``rubi1213r16Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, a, c, Add[p, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_3_r16, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]",
      optionalFinding "d., e., f., g. and c."] },
  { rule := rubi1213r15Nondeg, ruleDecl := ``rubi1213r15Nondeg, 
    proofs := [(.real, ``rubi1213r15Nondeg_real), (.complex, ``rubi1213r15Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[c, Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_3_r15, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; LtQ[p, -1]",
      optionalFinding "d., e., f., g., a., b. and c."] },
  { rule := rubi1211r5Nondeg, ruleDecl := ``rubi1211r5Nondeg, 
    proofs := [(.real, ``rubi1211r5Nondeg_real), (.complex, ``rubi1211r5Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, c, Add[Multiply[2, p], 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_1_r5, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; GtQ[p, 0]; IntegerQ[Multiply[4, p]]",
      optionalFinding "a., b. and c."] },
  { rule := rubi1222r17Nondeg, ruleDecl := ``rubi1222r17Nondeg, 
    proofs := [(.real, ``rubi1222r17Nondeg_real), (.complex, ``rubi1222r17Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[a, d, Add[m, 1]], 0]; NeQ[Multiply[a, Power[d, 2]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_2_2_r17, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; LtQ[m, -1]",
      optionalFinding "d., b. and c."] },
  { rule := rubi1221r5Nondeg, ruleDecl := ``rubi1221r5Nondeg, 
    proofs := [(.real, ``rubi1221r5Nondeg_real), (.complex, ``rubi1221r5Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, a, Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_2_1_r5, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; LtQ[p, -1]; IntegerQ[Multiply[2, p]]",
      optionalFinding "b. and c."] },
  { rule := rubi1212r102Nondeg, ruleDecl := ``rubi1212r102Nondeg, 
    proofs := [(.real, ``rubi1212r102Nondeg_real), (.complex, ``rubi1212r102Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[4, a, c, Add[p, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r102, which stays refuted.",
      recFinding,
      condFinding "NeQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; EqQ[Add[m, Multiply[2, p], 3], 0]; LtQ[p, -1]",
      optionalFinding "e. and c."] },
  { rule := rubi1113r13Nondeg, ruleDecl := ``rubi1113r13Nondeg, 
    proofs := [(.real, ``rubi1113r13Nondeg_real), (.complex, ``rubi1113r13Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[b, d, Add[p, Multiply[-1, 1]]], 0]; NeQ[Multiply[b, d], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_1_3_r13, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "GtQ[p, 1]",
      optionalFinding "e., f., a., b., c. and d."] },
  { rule := rubi1113r14Nondeg, ruleDecl := ``rubi1113r14Nondeg, 
    proofs := [(.real, ``rubi1113r14Nondeg_real), (.complex, ``rubi1113r14Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[Add[p, 1], Add[Multiply[b, e], Multiply[-1, a, f]], Add[Multiply[d, e], Multiply[-1, c, f]]], 0]; NeQ[Multiply[Add[Multiply[b, e], Multiply[-1, a, f]], Add[Multiply[d, e], Multiply[-1, c, f]]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_1_3_r14, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]",
      optionalFinding "e., f., a., b., c. and d."] },
  { rule := rubi1135r24Nondeg, ruleDecl := ``rubi1135r24Nondeg, 
    proofs := [(.real, ``rubi1135r24Nondeg_real), (.complex, ``rubi1135r24Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Power[Add[Multiply[b, c], Multiply[-1, a, d]], 2], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_5_r24, which stays refuted.",
      "independence: q, r are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[q, -1]; GtQ[r, 1]",
      optionalFinding "d., f. and b."] },
  { rule := rubi1135r25Nondeg, ruleDecl := ``rubi1135r25Nondeg, 
    proofs := [(.real, ``rubi1135r25Nondeg_real), (.complex, ``rubi1135r25Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[b, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_5_r25, which stays refuted.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "GtQ[q, 1]",
      optionalFinding "d., f. and b."] },
  { rule := rubi1135r26Nondeg, ruleDecl := ``rubi1135r26Nondeg, 
    proofs := [(.real, ``rubi1135r26Nondeg_real), (.complex, ``rubi1135r26Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Power[Add[Multiply[b, c], Multiply[-1, a, d]], 2], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_5_r26, which stays refuted.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[q, -1]",
      optionalFinding "d., f. and b."] },
  { rule := rubi1135r30Nondeg, ruleDecl := ``rubi1135r30Nondeg, 
    proofs := [(.real, ``rubi1135r30Nondeg_real), (.complex, ``rubi1135r30Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[b, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_5_r30, which stays refuted.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "ILtQ[p, 0]; GtQ[q, 0]",
      optionalFinding "b., d. and f."] },
  { rule := rubi1212r43Nondeg, ruleDecl := ``rubi1212r43Nondeg, 
    proofs := [(.real, ``rubi1212r43Nondeg_real), (.complex, ``rubi1212r43Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[c, Add[m, Multiply[2, p], 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r43, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; GtQ[m, 1]; NeQ[Add[m, Multiply[2, p], 1], 0]; IntegerQ[Multiply[2, p]]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi1212r44Nondeg, ruleDecl := ``rubi1212r44Nondeg, 
    proofs := [(.real, ``rubi1212r44Nondeg_real), (.complex, ``rubi1212r44Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[c, Add[m, Multiply[2, p], 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r44, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; GtQ[m, 1]; NeQ[Add[m, Multiply[2, p], 1], 0]; IntegerQ[Multiply[2, p]]",
      optionalFinding "e. and c."] },
  { rule := rubi1212r45Nondeg, ruleDecl := ``rubi1212r45Nondeg, 
    proofs := [(.real, ``rubi1212r45Nondeg_real), (.complex, ``rubi1212r45Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[Add[m, p, 1], Add[Multiply[2, c, d], Multiply[-1, b, e]]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r45, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; LtQ[m, 0]; NeQ[Add[m, p, 1], 0]; IntegerQ[Multiply[2, p]]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi1212r39Nondeg, ruleDecl := ``rubi1212r39Nondeg, 
    proofs := [(.real, ``rubi1212r39Nondeg_real), (.complex, ``rubi1212r39Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[e, Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0]; NeQ[Multiply[Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r39, which stays refuted.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[c, Power[d, 2]], Multiply[-1, b, d, e], Multiply[a, Power[e, 2]]], 0]; LtQ[p, -1]; LtQ[0, m, 1]; IntegerQ[Multiply[2, p]]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi1212r54Nondeg, ruleDecl := ``rubi1212r54Nondeg, 
    proofs := [(.real, ``rubi1212r54Nondeg_real), (.complex, ``rubi1212r54Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[d, Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0]; NeQ[Multiply[Power[d, 2], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_2_r54, which stays refuted.",
      recFinding,
      condFinding "NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]",
      optionalFinding "e., a., b. and c."] },
  { rule := rubi479r1Nondeg, ruleDecl := ``rubi479r1Nondeg, 
    proofs := [(.real, ``rubi479r1Nondeg_real), (.complex, ``rubi479r1Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[b, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r1, which stays refuted.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]",
      optionalFinding "e., f., m., c., d., n. and b."] },
  { rule := rubi479r2Nondeg, ruleDecl := ``rubi479r2Nondeg, 
    proofs := [(.real, ``rubi479r2Nondeg_real), (.complex, ``rubi479r2Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[b, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r2, which stays refuted.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]",
      optionalFinding "e., f., m., c., d., n. and b."] },
  { rule := rubi479r25Nondeg, ruleDecl := ``rubi479r25Nondeg, 
    proofs := [(.real, ``rubi479r25Nondeg_real), (.complex, ``rubi479r25Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[b, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r25, which stays refuted.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]; IGtQ[p, 0]",
      optionalFinding "e., f., m., c., d., p., n. and b."] },
  { rule := rubi479r26Nondeg, ruleDecl := ``rubi479r26Nondeg, 
    proofs := [(.real, ``rubi479r26Nondeg_real), (.complex, ``rubi479r26Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[b, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r26, which stays refuted.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]; IGtQ[p, 0]",
      optionalFinding "e., f., m., c., d., p., n. and b."] },
  { rule := rubi476r1Nondeg, ruleDecl := ``rubi476r1Nondeg, 
    proofs := [(.real, ``rubi476r1Nondeg_real), (.complex, ``rubi476r1Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[b, Add[n, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_6_r1, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; NeQ[n, -1]",
      optionalFinding "c., d., m., a., b. and n."] },
  { rule := rubi476r2Nondeg, ruleDecl := ``rubi476r2Nondeg, 
    proofs := [(.real, ``rubi476r2Nondeg_real), (.complex, ``rubi476r2Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[b, Add[n, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_6_r2, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; NeQ[n, -1]",
      optionalFinding "c., d., m., a., b. and n."] },
  { rule := rubi476r16Nondeg, ruleDecl := ``rubi476r16Nondeg, 
    proofs := [(.real, ``rubi476r16Nondeg_real), (.complex, ``rubi476r16Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[b, d, Add[n, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_6_r16, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; NeQ[n, -1]",
      optionalFinding "e., f., m., c., d., b. and n."] },
  { rule := rubi476r17Nondeg, ruleDecl := ``rubi476r17Nondeg, 
    proofs := [(.real, ``rubi476r17Nondeg_real), (.complex, ``rubi476r17Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[b, d, Add[n, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_6_r17, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; NeQ[n, -1]",
      optionalFinding "e., f., m., c., d., b. and n."] },
  { rule := rubi4113r1Nondeg, ruleDecl := ``rubi4113r1Nondeg, 
    proofs := [(.real, ``rubi4113r1Nondeg_real), (.complex, ``rubi4113r1Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[4, c], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r1, which stays refuted.",
      recFinding,
      condFinding "EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]",
      optionalFinding "a., b. and c."] },
  { rule := rubi4113r2Nondeg, ruleDecl := ``rubi4113r2Nondeg, 
    proofs := [(.real, ``rubi4113r2Nondeg_real), (.complex, ``rubi4113r2Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[4, c], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r2, which stays refuted.",
      recFinding,
      condFinding "EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]",
      optionalFinding "a., b. and c."] },
  { rule := rubi4113r13Nondeg, ruleDecl := ``rubi4113r13Nondeg, 
    proofs := [(.real, ``rubi4113r13Nondeg_real), (.complex, ``rubi4113r13Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, c], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r13, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r14Nondeg, ruleDecl := ``rubi4113r14Nondeg, 
    proofs := [(.real, ``rubi4113r14Nondeg_real), (.complex, ``rubi4113r14Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, c], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r14, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r19Nondeg, ruleDecl := ``rubi4113r19Nondeg, 
    proofs := [(.real, ``rubi4113r19Nondeg_real), (.complex, ``rubi4113r19Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, c], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r19, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r20Nondeg, ruleDecl := ``rubi4113r20Nondeg, 
    proofs := [(.real, ``rubi4113r20Nondeg_real), (.complex, ``rubi4113r20Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, c], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r20, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r15Nondeg, ruleDecl := ``rubi4113r15Nondeg, 
    proofs := [(.real, ``rubi4113r15Nondeg_real), (.complex, ``rubi4113r15Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r15, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r16Nondeg, ruleDecl := ``rubi4113r16Nondeg, 
    proofs := [(.real, ``rubi4113r16Nondeg_real), (.complex, ``rubi4113r16Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r16, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r21Nondeg, ruleDecl := ``rubi4113r21Nondeg, 
    proofs := [(.real, ``rubi4113r21Nondeg_real), (.complex, ``rubi4113r21Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r21, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r22Nondeg, ruleDecl := ``rubi4113r22Nondeg, 
    proofs := [(.real, ``rubi4113r22Nondeg_real), (.complex, ``rubi4113r22Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r22, which stays refuted.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi479r11Nondeg, ruleDecl := ``rubi479r11Nondeg, 
    proofs := [(.real, ``rubi479r11Nondeg_real), (.complex, ``rubi479r11Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Power[b, 2], 0]; NeQ[b, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r11, which stays refuted.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 1]; NeQ[Add[Power[a, 2], Multiply[-1, Power[b, 2]]], 0]; IGtQ[m, 0]",
      optionalFinding "e., f., m., c., d. and b."] },
  { rule := rubi479r12Nondeg, ruleDecl := ``rubi479r12Nondeg, 
    proofs := [(.real, ``rubi479r12Nondeg_real), (.complex, ``rubi479r12Nondeg_complex)],
    findings := [
      "strengthened: the conditions NeQ[Power[b, 2], 0]; NeQ[b, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r12, which stays refuted.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 1]; NeQ[Add[Power[a, 2], Multiply[-1, Power[b, 2]]], 0]; IGtQ[m, 0]",
      optionalFinding "e., f., m., c., d. and b."] },
  { rule := rubi23r32Nondeg, ruleDecl := ``rubi23r32Nondeg, 
    proofs := [(.real, ``rubi23r32Nondeg_real), (.complex, ``rubi23r32Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_2_3_r32, which stays refuted.",
      recFinding,
      condFinding "EqQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]",
      optionalFinding "g., h., m., e., f., a., b., c. and d."] },
  { rule := rubi23r33Nondeg, ruleDecl := ``rubi23r33Nondeg, 
    proofs := [(.real, ``rubi23r33Nondeg_real), (.complex, ``rubi23r33Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_2_3_r33, which stays refuted.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[d, g], Multiply[-1, c, h]], 0]",
      optionalFinding "g., h., m., e., f., a., b., c. and d."] },
  { rule := rubi314r17Nondeg, ruleDecl := ``rubi314r17Nondeg, 
    proofs := [(.real, ``rubi314r17Nondeg_real), (.complex, ``rubi314r17Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_4_r17, which stays refuted.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; LtQ[q, -1]; IntegerQ[Multiply[2, q]]",
      optionalFinding "e., a., b., c., n. and p."] },
  { rule := rubi315r16Nondeg, ruleDecl := ``rubi315r16Nondeg, 
    proofs := [(.real, ``rubi315r16Nondeg_real), (.complex, ``rubi315r16Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r16, which stays refuted.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; LtQ[q, -1]; IntegerQ[Multiply[2, q]]",
      optionalFinding "e., a., b., c., n. and p."] },
  { rule := rubi315r13Nondeg, ruleDecl := ``rubi315r13Nondeg, 
    proofs := [(.real, ``rubi315r13Nondeg_real), (.complex, ``rubi315r13Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r13, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]",
      optionalFinding "a., b., c., n., p. and e."] },
  { rule := rubi314r9Nondeg, ruleDecl := ``rubi314r9Nondeg, 
    proofs := [(.real, ``rubi314r9Nondeg_real), (.complex, ``rubi314r9Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_4_r9, which stays refuted.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; IGtQ[r, 0]; ILtQ[m, -1]",
      optionalFinding "m., a., b., c., n., p., e. and r."] },
  { rule := rubi314r18Nondeg, ruleDecl := ``rubi314r18Nondeg, 
    proofs := [(.real, ``rubi314r18Nondeg_real), (.complex, ``rubi314r18Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_4_r18, which stays refuted.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; ILtQ[q, -1]",
      optionalFinding "e., r., a., b., c., n. and p."] },
  { rule := rubi315r17Nondeg, ruleDecl := ``rubi315r17Nondeg, 
    proofs := [(.real, ``rubi315r17Nondeg_real), (.complex, ``rubi315r17Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r17, which stays refuted.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; ILtQ[q, -1]",
      optionalFinding "e., r., a., b., c., n. and p."] },
  { rule := rubi479r16Nondeg, ruleDecl := ``rubi479r16Nondeg, 
    proofs := [(.real, ``rubi479r16Nondeg_real), (.complex, ``rubi479r16Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[a, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r16, which stays refuted.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]",
      optionalFinding "e., f., m., c., d., n. and b."] },
  { rule := rubi479r27Nondeg, ruleDecl := ``rubi479r27Nondeg, 
    proofs := [(.real, ``rubi479r27Nondeg_real), (.complex, ``rubi479r27Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[b, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r27, which stays refuted.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]; IGtQ[p, 0]",
      optionalFinding "e., f., m., c., d., p., n. and b."] },
  { rule := rubi479r30Nondeg, ruleDecl := ``rubi479r30Nondeg, 
    proofs := [(.real, ``rubi479r30Nondeg_real), (.complex, ``rubi479r30Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[a, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r30, which stays refuted.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]; IGtQ[p, 0]",
      optionalFinding "e., f., m., c., d., p., n. and b."] },
  { rule := rubi4112r33Nondeg, ruleDecl := ``rubi4112r33Nondeg, 
    proofs := [(.real, ``rubi4112r33Nondeg_real), (.complex, ``rubi4112r33Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[d, n], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_12_r33, which stays refuted.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 0]; LtQ[n, Add[m, 1]]",
      optionalFinding "e., m., c. and d."] },
  { rule := rubi4112r34Nondeg, ruleDecl := ``rubi4112r34Nondeg, 
    proofs := [(.real, ``rubi4112r34Nondeg_real), (.complex, ``rubi4112r34Nondeg_complex)],
    findings := [
      "strengthened: the condition NeQ[Multiply[d, n], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_12_r34, which stays refuted.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 0]; LtQ[n, Add[m, 1]]",
      optionalFinding "e., m., c. and d."] },
  { rule := rubi311r3Nondeg, ruleDecl := ``rubi311r3Nondeg, 
    proofs := [(.real, ``rubi311r3Nondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[b, n, Add[p, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_1_r3, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]; IntegerQ[Multiply[2, p]]",
      optionalFinding "a., b., c. and n."] },
  { rule := rubi312r5Nondeg, ruleDecl := ``rubi312r5Nondeg, 
    proofs := [(.real, ``rubi312r5Nondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[d, Add[m, 1]], 0]; NeQ[Add[m, 1], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_2_r5, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[m, -1]; GtQ[p, 0]",
      optionalFinding "d., m., a., b., c., n. and p."] },
  { rule := rubi312r6Nondeg, ruleDecl := ``rubi312r6Nondeg, 
    proofs := [(.real, ``rubi312r6Nondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[b, d, n, Add[p, 1]], 0]; NeQ[Multiply[b, n, Add[p, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_2_r6, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[m, -1]; LtQ[p, -1]",
      optionalFinding "d., m., a., b., c. and n."] },
  { rule := rubi314r12Nondeg, ruleDecl := ``rubi314r12Nondeg, 
    proofs := [(.real, ``rubi314r12Nondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[e, Add[q, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_4_r12, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "ILtQ[q, -1]; GtQ[m, 0]",
      optionalFinding "f., m., e., q., a., b., c. and n."] },
  { rule := rubi315r8Nondeg, ruleDecl := ``rubi315r8Nondeg, 
    proofs := [(.real, ``rubi315r8Nondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[e, Add[q, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r8, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "ILtQ[q, -1]; GtQ[m, 0]",
      optionalFinding "f., m., e., q., a., b., c. and n."] },
  { rule := rubi314r2Nondeg, ruleDecl := ``rubi314r2Nondeg, 
    proofs := [(.real, ``rubi314r2Nondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[d, f, Add[m, 1]], 0]; NeQ[Multiply[d, Add[m, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_4_r2, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      recFinding,
      condFinding "EqQ[Add[m, Multiply[r, Add[q, 1]], 1], 0]; NeQ[m, -1]",
      optionalFinding "f., m., e., r., a., b., c. and n."] },
  { rule := rubi315r3Nondeg, ruleDecl := ``rubi315r3Nondeg, 
    proofs := [(.real, ``rubi315r3Nondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[d, f, Add[m, 1]], 0]; NeQ[Multiply[d, Add[m, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r3, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      recFinding,
      condFinding "EqQ[Add[m, Multiply[r, Add[q, 1]], 1], 0]; NeQ[m, -1]",
      optionalFinding "f., m., e., r., a., b., c. and n."] },
  { rule := logPowOverSqNondeg, ruleDecl := ``logPowOverSqNondeg, 
    proofs := [(.real, ``logPowOverSqNondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.log_power_over_linear_square, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      recFinding,
      condFinding "GtQ[p, 0]",
      optionalFinding "a., b., c., n., p. and e."] },
  { rule := rubi313r1Nondeg, ruleDecl := ``rubi313r1Nondeg, 
    proofs := [(.real, ``rubi313r1Nondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_3_r1, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      recFinding,
      condFinding "EqQ[Add[Multiply[r, Add[q, 1]], 1], 0]",
      optionalFinding "e., r., a., b., c. and n."] }
]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem catalogPart5_wellFormed : ∀ e ∈ catalogPart5,
    (if e.rule.shape == .antiderivRec then e.rule.recOk else e.rule.wellFormed) = true := by
  intro e he
  simp only [catalogPart5, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The Integration catalogue, in v0.1 file order: part 6. -/
def catalogPart6 : List CEntry := [
  { rule := rubi313r10Nondeg, ruleDecl := ``rubi313r10Nondeg, 
    proofs := [(.real, ``rubi313r10Nondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, d, Add[q, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_3_r10, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[q, -1]",
      optionalFinding "e., a., b., c. and n."] },
  { rule := rubi314r13Nondeg, ruleDecl := ``rubi314r13Nondeg, 
    proofs := [(.real, ``rubi314r13Nondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[2, d, f, Add[q, 1]], 0]; NeQ[Multiply[2, d, Add[q, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_4_r13, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "ILtQ[q, -1]; ILtQ[m, 0]",
      optionalFinding "f., m., e., q., a., b., c. and n."] },
  { rule := rubi315r9Nondeg, ruleDecl := ``rubi315r9Nondeg, 
    proofs := [(.real, ``rubi315r9Nondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[2, d, f, Add[q, 1]], 0]; NeQ[Multiply[2, d, Add[q, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r9, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "ILtQ[q, -1]; ILtQ[m, 0]",
      optionalFinding "f., m., e., q., a., b., c. and n."] },
  { rule := rubi313r7Nondeg, ruleDecl := ``rubi313r7Nondeg, 
    proofs := [(.real, ``rubi313r7Nondeg_real)],
    unproved := [.complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[b, n, Add[p, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_3_r7, which stays refuted.",
      "domain: proved over ℝ only, with the real logarithm, which is not differentiable on the complex branch cut; the complex domain is unproved.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]; GtQ[q, 0]",
      optionalFinding "e., q., a., b., c. and n."] }
]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem catalogPart6_wellFormed : ∀ e ∈ catalogPart6,
    (if e.rule.shape == .antiderivRec then e.rule.recOk else e.rule.wellFormed) = true := by
  intro e he
  simp only [catalogPart6, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> decide

/-- The rules with a proof or a counterexample, in v0.1 file order. -/
def catalogVerified : List CEntry :=
  catalogPart1 ++ catalogPart2 ++ catalogPart3 ++ catalogPart4 ++ catalogPart5 ++ catalogPart6

/-- The Integration catalogue: the verified rules, then the strengthened variants checked
numerically (`OSR.IntegrationNum1`), unproved. -/
def catalog : List CEntry :=
  catalogVerified ++ IntegrationNum1.entries

/-- Every catalogue rule is well formed: recursive rules by `recOk`, the
others by `wellFormed`. -/
theorem catalog_wellFormed : ∀ e ∈ catalog,
    (if e.rule.shape == .antiderivRec then e.rule.recOk else e.rule.wellFormed) = true := by
  intro e he
  simp only [catalog, catalogVerified, List.mem_append] at he
  rcases he with (((((h | h) | h) | h) | h) | h) | h
  · exact catalogPart1_wellFormed e h
  · exact catalogPart2_wellFormed e h
  · exact catalogPart3_wellFormed e h
  · exact catalogPart4_wellFormed e h
  · exact catalogPart5_wellFormed e h
  · exact catalogPart6_wellFormed e h
  · exact IntegrationNum1.entries_wellFormed e h

end OSR.Integration
