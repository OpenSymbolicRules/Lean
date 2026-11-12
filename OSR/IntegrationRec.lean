import OSR.Calculus

/-!
# Integration (RUBI): rules with residual integrals

A RUBI rule whose result contains `Int[H, x]` becomes a recursive
antiderivative rule (`Shape.antiderivRec`): the result is an expression in
which each residual integral is a hole variable `I1`, `I2`, …, exported as
`int(λx. H)(x)` (the form of the `calculus1#int` FMP).  Its statement,
`OSR.Calculus.AntiderivRecHolds`, says that wherever the integrand is defined
near a point, the residual integrands are defined near it too, and that for
every choice of antiderivatives of the residual integrands the result is an
antiderivative of the integrand.

The reference rewriter does not apply these rules: continuing inside a
residual integral is left to the consumer.  The conventions of
`OSR.Integration` (left-nested products and sums, `Power[u, -1]` kept,
optional wildcards as plain metavariables, `FreeQ` as `independent`, `NeQ`,
`GtQ` and `IntegerQ` as conditions) apply.
-/

namespace OSR.IntegrationRec

open OSR OSR.Calculus Filter Topology

private abbrev x : Expr := .var "x"
private abbrev v (n : String) : Expr := .var n
private abbrev ln (e : Expr) : Expr := .app1 .ln e
private abbrev sin (e : Expr) : Expr := .app1 .sin e
private abbrev cos (e : Expr) : Expr := .app1 .cos e
private abbrev add (a b : Expr) : Expr := .app2 .add a b
private abbrev mul (a b : Expr) : Expr := .app2 .mul a b
private abbrev inv (e : Expr) : Expr := .pow e (.int (-1))
private abbrev sq (e : Expr) : Expr := .pow e (.int 2)
private abbrev neg (e : Expr) : Expr := mul (.int (-1)) e

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

private def sine : String := "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p"
private def sineM : String := "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m"
private def logPow : String := "rubi:3 Logarithms/3.1.1 (a+b log(c x^n))^p"
private def logMisc : String := "rubi:3 Logarithms/3.5 Miscellaneous logarithms"
private def trigLog : String := "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p"
private def quad : String := "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p"

/-! ## Rules -/

/-- `d (e + f x)^2`. -/
private abbrev sqArg : Expr := mul (v "d") (sq (add (v "e") (mul (v "f") x)))
/-- `d x^n`. -/
private abbrev powArg : Expr := mul (v "d") (.pow x (v "n"))

/-- `Int[Sin[c + d (e + f x)^2], x] := Sin[c] Int[Cos[d (e + f x)^2], x]
+ Cos[c] Int[Sin[d (e + f x)^2], x]`. -/
def sinAddSq : CRule where
  id := "integration.sin_add_square"; legacyId := some s!"{sine}:3"; shape := .antiderivRec
  x := "x"; body := sin (add (v "c") sqArg)
  result := add (mul (sin (v "c")) (v "I1")) (mul (cos (v "c")) (v "I2"))
  integrals := [("I1", cos sqArg), ("I2", sin sqArg)]
  independent := ["c", "d", "e", "f"]; priority := 140
  description := "sin(c + u) = sin c cos u + cos c sin u under the integral"
  provenance := migrated s!"{sine}:3" s!"{sineM}#3"

/-- `Int[Cos[c + d (e + f x)^2], x] := Cos[c] Int[Cos[…], x] - Sin[c] Int[Sin[…], x]`. -/
def cosAddSq : CRule where
  id := "integration.cos_add_square"; legacyId := some s!"{sine}:4"; shape := .antiderivRec
  x := "x"; body := cos (add (v "c") sqArg)
  result := add (mul (cos (v "c")) (v "I1")) (mul (neg (sin (v "c"))) (v "I2"))
  integrals := [("I1", cos sqArg), ("I2", sin sqArg)]
  independent := ["c", "d", "e", "f"]; priority := 150
  description := "cos(c + u) = cos c cos u - sin c sin u under the integral"
  provenance := migrated s!"{sine}:4" s!"{sineM}#4"

/-- `Int[Sin[c + d x^n]/x, x] := Sin[c] Int[Cos[d x^n]/x, x] + Cos[c] Int[Sin[d x^n]/x, x]`. -/
def sinAddPowOverX : CRule where
  id := "integration.sin_add_power_over_x"; legacyId := some s!"{sine}:25"
  shape := .antiderivRec; x := "x"
  body := mul (sin (add (v "c") powArg)) (inv x)
  result := add (mul (sin (v "c")) (v "I1")) (mul (cos (v "c")) (v "I2"))
  integrals := [("I1", mul (cos powArg) (inv x)), ("I2", mul (sin powArg) (inv x))]
  independent := ["c", "d", "n"]; priority := 160
  description := "sin(c + d x^n)/x split by the addition formula"
  provenance := migrated s!"{sine}:25" s!"{sineM}#25"

/-- `Int[Cos[c + d x^n]/x, x] := Cos[c] Int[Cos[d x^n]/x, x] - Sin[c] Int[Sin[d x^n]/x, x]`. -/
def cosAddPowOverX : CRule where
  id := "integration.cos_add_power_over_x"; legacyId := some s!"{sine}:26"
  shape := .antiderivRec; x := "x"
  body := mul (cos (add (v "c") powArg)) (inv x)
  result := add (mul (cos (v "c")) (v "I1")) (mul (neg (sin (v "c"))) (v "I2"))
  integrals := [("I1", mul (cos powArg) (inv x)), ("I2", mul (sin powArg) (inv x))]
  independent := ["c", "d", "n"]; priority := 170
  description := "cos(c + d x^n)/x split by the addition formula"
  provenance := migrated s!"{sine}:26" s!"{sineM}#26"

/-- `a + b x^n/2`. -/
private abbrev halfArg : Expr := add (v "a") (mul (mul (v "b") (.pow x (v "n"))) (inv (.int 2)))
/-- `x^m cos(2 a + b x^n)`. -/
private abbrev doubleArg : Expr :=
  mul (.pow x (v "m")) (cos (add (mul (.int 2) (v "a")) (mul (v "b") (.pow x (v "n")))))
/-- `1/2`, as converted: `1 · 2^(-1)`. -/
private abbrev half : Expr := mul (.int 1) (inv (.int 2))

/-- `Int[x^m Sin[a + b x^n/2]^2, x] := 1/2 Int[x^m, x] - 1/2 Int[x^m Cos[2 a + b x^n], x]`. -/
def powSinSq : CRule where
  id := "integration.power_sin_square"; legacyId := some s!"{sine}:39"; shape := .antiderivRec
  x := "x"; body := mul (.pow x (v "m")) (sq (sin halfArg))
  result := add (mul half (v "I1")) (mul (mul (mul (.int (-1)) (.int 1)) (inv (.int 2))) (v "I2"))
  integrals := [("I1", .pow x (v "m")), ("I2", doubleArg)]
  independent := ["a", "b", "m", "n"]; priority := 180
  description := "x^m sin(θ)^2 = x^m/2 - x^m cos(2θ)/2 under the integral"
  provenance := migrated s!"{sine}:39" s!"{sineM}#39"

/-- `Int[x^m Cos[a + b x^n/2]^2, x] := 1/2 Int[x^m, x] + 1/2 Int[x^m Cos[2 a + b x^n], x]`. -/
def powCosSq : CRule where
  id := "integration.power_cos_square"; legacyId := some s!"{sine}:40"; shape := .antiderivRec
  x := "x"; body := mul (.pow x (v "m")) (sq (cos halfArg))
  result := add (mul half (v "I1")) (mul half (v "I2"))
  integrals := [("I1", .pow x (v "m")), ("I2", doubleArg)]
  independent := ["a", "b", "m", "n"]; priority := 190
  description := "x^m cos(θ)^2 = x^m/2 + x^m cos(2θ)/2 under the integral"
  provenance := migrated s!"{sine}:40" s!"{sineM}#40"

/-- `log(d x^n)`. -/
private abbrev logDxn : Expr := ln (mul (v "d") (.pow x (v "n")))
/-- `log(c log(d x^n)^p)`. -/
private abbrev logLog : Expr := ln (mul (v "c") (.pow logDxn (v "p")))

/-- `Int[Log[c Log[d x^n]^p], x] := x Log[c Log[d x^n]^p] - n p Int[1/Log[d x^n], x]`. -/
def logPowLog : CRule where
  id := "integration.log_power_log"; legacyId := some s!"{logMisc}:1"; shape := .antiderivRec
  x := "x"; body := logLog
  result := add (mul x logLog) (mul (mul (mul (.int (-1)) (v "n")) (v "p")) (v "I1"))
  integrals := [("I1", mul (.int 1) (inv logDxn))]
  independent := ["c", "d", "n", "p"]; priority := 200
  description := "Integration by parts of log(c log(d x^n)^p)"
  provenance := migrated s!"{logMisc}:1" "3 Logarithms/3.5 Miscellaneous logarithms.m#1"

/-- `a + b log(c x^n)`. -/
private abbrev logLin : Expr := add (v "a") (mul (v "b") (ln (mul (v "c") (.pow x (v "n")))))

/-- `Int[(a + b Log[c x^n])^p, x] := x (a + b Log[c x^n])^p
- b n p Int[(a + b Log[c x^n])^(p - 1), x]` for `p > 0` and `2 p ∈ ℤ`. -/
def logLinPow : CRule where
  id := "integration.log_linear_power"; legacyId := some s!"{logPow}:2"; shape := .antiderivRec
  x := "x"; body := .pow logLin (v "p")
  result := add (mul x (.pow logLin (v "p")))
    (mul (mul (mul (mul (.int (-1)) (v "b")) (v "n")) (v "p")) (v "I1"))
  integrals := [("I1", .pow logLin (add (v "p") (mul (.int (-1)) (.int 1))))]
  independent := ["a", "b", "c", "n", "p"]
  conditions := [.gt (v "p") (.int 0), .int (mul (.int 2) (v "p"))]; priority := 210
  description := "Reduction of (a + b log(c x^n))^p"
  provenance := migrated s!"{logPow}:2" "3 Logarithms/3.1.1 (a+b log(c x^n))^p.m#2"

/-- `a x log(b x)`. -/
private abbrev xLog : Expr := mul (mul (v "a") x) (ln (mul (v "b") x))

/-- `Int[Sin[a x Log[b x]] Log[b x], x] := -Cos[a x Log[b x]]/a - Int[Sin[a x Log[b x]], x]`. -/
def sinXLog : CRule where
  id := "integration.sin_x_log_times_log"; legacyId := some s!"{trigLog}:45"
  shape := .antiderivRec; x := "x"
  body := mul (sin xLog) (ln (mul (v "b") x))
  result := add (mul (mul (.int (-1)) (cos xLog)) (inv (v "a"))) (neg (v "I1"))
  integrals := [("I1", sin xLog)]
  independent := ["a", "b"]; priority := 220
  description := "Antiderivative of sin(a x log(b x)) log(b x)"
  provenance := migrated s!"{trigLog}:45" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#45"

/-- `Int[Cos[a x Log[b x]] Log[b x], x] := Sin[a x Log[b x]]/a - Int[Cos[a x Log[b x]], x]`. -/
def cosXLog : CRule where
  id := "integration.cos_x_log_times_log"; legacyId := some s!"{trigLog}:46"
  shape := .antiderivRec; x := "x"
  body := mul (cos xLog) (ln (mul (v "b") x))
  result := add (mul (sin xLog) (inv (v "a"))) (neg (v "I1"))
  integrals := [("I1", cos xLog)]
  independent := ["a", "b"]; priority := 230
  description := "Antiderivative of cos(a x log(b x)) log(b x)"
  provenance := migrated s!"{trigLog}:46" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#46"

/-- `a + c x^2`. -/
private abbrev quadExpr : Expr := add (v "a") (mul (v "c") (sq x))

/-- `Int[(d + e x) (a + c x^2)^p, x] := e (a + c x^2)^(p+1)/(2 c (p+1))
+ d Int[(a + c x^2)^p, x]` for `p ≠ -1`. -/
def linearQuadPow : CRule where
  id := "integration.linear_times_quadratic_power"; legacyId := some s!"{quad}:14"
  shape := .antiderivRec; x := "x"
  body := mul (add (v "d") (mul (v "e") x)) (.pow quadExpr (v "p"))
  result := add
    (mul (mul (v "e") (.pow quadExpr (add (v "p") (.int 1))))
      (inv (mul (mul (.int 2) (v "c")) (add (v "p") (.int 1)))))
    (mul (v "d") (v "I1"))
  integrals := [("I1", .pow quadExpr (v "p"))]
  independent := ["a", "c", "d", "e", "p"]; conditions := [.ne (v "p") (.int (-1))]
  priority := 240
  description := "Antiderivative of (d + e x) (a + c x^2)^p"
  provenance := migrated s!"{quad}:14" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#14"

/-! ### Second batch -/

private def linPair : String := "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n"
private def binPair : String := "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q"
private def binTriple : String := "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r"
private def quadLin : String := "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p"
private def quadPair : String := "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q"
private def sineQuad : String := "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n"
private def logBin : String := "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p"

/-- `b c - a d`. -/
private abbrev detBC : Expr := add (mul (v "b") (v "c")) (mul (mul (.int (-1)) (v "a")) (v "d"))

/-- `Int[1/((a + b x) (c + d x)), x] := b/(b c - a d) Int[1/(a + b x), x]
- d/(b c - a d) Int[1/(c + d x), x]` for `b c - a d ≠ 0`. -/
def pfLinear : CRule where
  id := "integration.partial_fractions_linear"; legacyId := some s!"{linPair}:3"
  shape := .antiderivRec; x := "x"
  body := mul (.int 1) (inv (mul (add (v "a") (mul (v "b") x)) (add (v "c") (mul (v "d") x))))
  result := add (mul (mul (v "b") (inv detBC)) (v "I1"))
    (mul (mul (mul (.int (-1)) (v "d")) (inv detBC)) (v "I2"))
  integrals := [("I1", mul (.int 1) (inv (add (v "a") (mul (v "b") x)))),
    ("I2", mul (.int 1) (inv (add (v "c") (mul (v "d") x))))]
  independent := ["a", "b", "c", "d"]; conditions := [.ne detBC (.int 0)]; priority := 250
  description := "Partial fractions of 1/((a + b x) (c + d x))"
  provenance := migrated s!"{linPair}:3" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.m#3"

/-- `a + b x^n`, `c + d x^n`. -/
private abbrev binA : Expr := add (v "a") (mul (v "b") (.pow x (v "n")))
private abbrev binB : Expr := add (v "c") (mul (v "d") (.pow x (v "n")))

/-- `Int[1/((a + b x^n) (c + d x^n)), x]`, the same partial fractions. -/
def pfPower : CRule where
  id := "integration.partial_fractions_power"; legacyId := some s!"{binPair}:19"
  shape := .antiderivRec; x := "x"
  body := mul (.int 1) (inv (mul binA binB))
  result := add (mul (mul (v "b") (inv detBC)) (v "I1"))
    (mul (mul (mul (.int (-1)) (v "d")) (inv detBC)) (v "I2"))
  integrals := [("I1", mul (.int 1) (inv binA)), ("I2", mul (.int 1) (inv binB))]
  independent := ["a", "b", "c", "d", "n"]; conditions := [.ne detBC (.int 0)]; priority := 260
  description := "Partial fractions of 1/((a + b x^n) (c + d x^n))"
  provenance := migrated s!"{binPair}:19" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#19"

/-- `Int[(a + b x^n)^p (c + d x^n)^q (e + f x^n), x] :=
e Int[(a + b x^n)^p (c + d x^n)^q, x] + f Int[x^n (a + b x^n)^p (c + d x^n)^q, x]`. -/
def splitBinomial : CRule where
  id := "integration.split_linear_factor_binomial"; legacyId := some s!"{binTriple}:11"
  shape := .antiderivRec; x := "x"
  body := mul (mul (.pow binA (v "p")) (.pow binB (v "q"))) (add (v "e") (mul (v "f") (.pow x (v "n"))))
  result := add (mul (v "e") (v "I1")) (mul (v "f") (v "I2"))
  integrals := [("I1", mul (.pow binA (v "p")) (.pow binB (v "q"))),
    ("I2", mul (mul (.pow x (v "n")) (.pow binA (v "p"))) (.pow binB (v "q")))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "p", "q"]; priority := 270
  description := "Split the factor e + f x^n under the integral"
  provenance := migrated s!"{binTriple}:11" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#11"

/-- `a + c x^2`, `d + f x^2`. -/
private abbrev quadA : Expr := add (v "a") (mul (v "c") (sq x))
private abbrev quadD : Expr := add (v "d") (mul (v "f") (sq x))

/-- `Int[(g + h x) (a + c x^2)^p (d + f x^2)^q, x] :=
g Int[(a + c x^2)^p (d + f x^2)^q, x] + h Int[x (a + c x^2)^p (d + f x^2)^q, x]`. -/
def splitQuadratic : CRule where
  id := "integration.split_linear_factor_quadratic"; legacyId := some s!"{quadPair}:13"
  shape := .antiderivRec; x := "x"
  body := mul (mul (add (v "g") (mul (v "h") x)) (.pow quadA (v "p"))) (.pow quadD (v "q"))
  result := add (mul (v "g") (v "I1")) (mul (v "h") (v "I2"))
  integrals := [("I1", mul (.pow quadA (v "p")) (.pow quadD (v "q"))),
    ("I2", mul (mul x (.pow quadA (v "p"))) (.pow quadD (v "q")))]
  independent := ["a", "c", "d", "f", "g", "h", "p", "q"]; priority := 280
  description := "Split the factor g + h x under the integral"
  provenance := migrated s!"{quadPair}:13" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#13"

/-- `a + b x + c x^2`. -/
private abbrev trinom : Expr := add (add (v "a") (mul (v "b") x)) (mul (v "c") (sq x))
/-- `2 c d - b e`. -/
private abbrev detCD : Expr := add (mul (mul (.int 2) (v "c")) (v "d")) (mul (mul (.int (-1)) (v "b")) (v "e"))

/-- `Int[(d + e x) Sin[a + b x + c x^2], x] := -e Cos[…]/(2 c)
+ (2 c d - b e)/(2 c) Int[Sin[…], x]` for `2 c d - b e ≠ 0`. -/
def linSinQuad : CRule where
  id := "integration.linear_sin_trinomial"; legacyId := some s!"{sineQuad}:17"
  shape := .antiderivRec; x := "x"
  body := mul (add (v "d") (mul (v "e") x)) (sin trinom)
  result := add (mul (mul (mul (.int (-1)) (v "e")) (cos trinom)) (inv (mul (.int 2) (v "c"))))
    (mul (mul detCD (inv (mul (.int 2) (v "c")))) (v "I1"))
  integrals := [("I1", sin trinom)]
  independent := ["a", "b", "c", "d", "e"]; conditions := [.ne detCD (.int 0)]; priority := 290
  description := "Antiderivative of (d + e x) sin(a + b x + c x^2)"
  provenance := migrated s!"{sineQuad}:17" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#17"

/-- `Int[(d + e x) Cos[a + b x + c x^2], x]`, as `linSinQuad`. -/
def linCosQuad : CRule where
  id := "integration.linear_cos_trinomial"; legacyId := some s!"{sineQuad}:18"
  shape := .antiderivRec; x := "x"
  body := mul (add (v "d") (mul (v "e") x)) (cos trinom)
  result := add (mul (mul (v "e") (sin trinom)) (inv (mul (.int 2) (v "c"))))
    (mul (mul detCD (inv (mul (.int 2) (v "c")))) (v "I1"))
  integrals := [("I1", cos trinom)]
  independent := ["a", "b", "c", "d", "e"]; conditions := [.ne detCD (.int 0)]; priority := 300
  description := "Antiderivative of (d + e x) cos(a + b x + c x^2)"
  provenance := migrated s!"{sineQuad}:18" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#18"

/-- `Int[(d + e x) (a + b x + c x^2)^p, x] := e (…)^(p+1)/(2 c (p+1))
+ (2 c d - b e)/(2 c) Int[(…)^p, x]` for `2 c d - b e ≠ 0`, `p ≠ -1`. -/
def linTrinomPow : CRule where
  id := "integration.linear_times_trinomial_power"; legacyId := some s!"{quad}:13"
  shape := .antiderivRec; x := "x"
  body := mul (add (v "d") (mul (v "e") x)) (.pow trinom (v "p"))
  result := add
    (mul (mul (v "e") (.pow trinom (add (v "p") (.int 1))))
      (inv (mul (mul (.int 2) (v "c")) (add (v "p") (.int 1)))))
    (mul (mul detCD (inv (mul (.int 2) (v "c")))) (v "I1"))
  integrals := [("I1", .pow trinom (v "p"))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.ne detCD (.int 0), .ne (v "p") (.int (-1))]; priority := 310
  description := "Antiderivative of (d + e x) (a + b x + c x^2)^p"
  provenance := migrated s!"{quad}:13" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#13"

/-- `Int[(d + e x) (f + g x)/(a + b x + c x^2), x] := e g x/c
+ 1/c Int[(c d f - a e g + (c e f + c d g - b e g) x)/(a + b x + c x^2), x]`
for `b^2 - 4 a c ≠ 0`. -/
def prodOverTrinom : CRule where
  id := "integration.product_over_trinomial"; legacyId := some s!"{quadLin}:11"
  shape := .antiderivRec; x := "x"
  body := mul (mul (add (v "d") (mul (v "e") x)) (add (v "f") (mul (v "g") x))) (inv trinom)
  result := add (mul (mul (mul (v "e") (v "g")) x) (inv (v "c")))
    (mul (mul (.int 1) (inv (v "c"))) (v "I1"))
  integrals := [("I1", mul
    (add (add (mul (mul (v "c") (v "d")) (v "f")) (mul (mul (mul (.int (-1)) (v "a")) (v "e")) (v "g")))
      (mul (add (add (mul (mul (v "c") (v "e")) (v "f")) (mul (mul (v "c") (v "d")) (v "g")))
        (mul (mul (mul (.int (-1)) (v "b")) (v "e")) (v "g"))) x))
    (inv trinom))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  conditions := [.ne (add (sq (v "b")) (mul (mul (mul (.int (-1)) (.int 4)) (v "a")) (v "c"))) (.int 0)]
  priority := 320
  description := "Antiderivative of (d + e x) (f + g x)/(a + b x + c x^2)"
  provenance := migrated s!"{quadLin}:11" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#11"

/-- `Int[(d + e x) (f + g x)/(a + c x^2), x] := e g x/c
+ 1/c Int[(c d f - a e g + c (e f + d g) x)/(a + c x^2), x]`. -/
def prodOverQuad : CRule where
  id := "integration.product_over_quadratic"; legacyId := some s!"{quadLin}:12"
  shape := .antiderivRec; x := "x"
  body := mul (mul (add (v "d") (mul (v "e") x)) (add (v "f") (mul (v "g") x))) (inv quadA)
  result := add (mul (mul (mul (v "e") (v "g")) x) (inv (v "c")))
    (mul (mul (.int 1) (inv (v "c"))) (v "I1"))
  integrals := [("I1", mul
    (add (add (mul (mul (v "c") (v "d")) (v "f")) (mul (mul (mul (.int (-1)) (v "a")) (v "e")) (v "g")))
      (mul (mul (v "c") (add (mul (v "e") (v "f")) (mul (v "d") (v "g")))) x))
    (inv quadA))]
  independent := ["a", "c", "d", "e", "f", "g"]; priority := 330
  description := "Antiderivative of (d + e x) (f + g x)/(a + c x^2)"
  provenance := migrated s!"{quadLin}:12" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#12"

/-- `Int[(a + b x^n)^p (e + f x^n)/(c + d x^n), x] := f/d Int[(a + b x^n)^p, x]
+ (d e - c f)/d Int[(a + b x^n)^p/(c + d x^n), x]`. -/
def powerRatio : CRule where
  id := "integration.power_ratio_split"; legacyId := some s!"{binTriple}:10"
  shape := .antiderivRec; x := "x"
  body := mul (mul (.pow binA (v "p")) (add (v "e") (mul (v "f") (.pow x (v "n"))))) (inv binB)
  result := add (mul (mul (v "f") (inv (v "d"))) (v "I1"))
    (mul (mul (add (mul (v "d") (v "e")) (mul (mul (.int (-1)) (v "c")) (v "f"))) (inv (v "d"))) (v "I2"))
  integrals := [("I1", .pow binA (v "p")), ("I2", mul (.pow binA (v "p")) (inv binB))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "n"]; priority := 340
  description := "Split (a + b x^n)^p (e + f x^n)/(c + d x^n)"
  provenance := migrated s!"{binTriple}:10" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#10"

/-- `log(c (d + e x^n)^p)`. -/
private abbrev logBinExpr : Expr :=
  ln (mul (v "c") (.pow (add (v "d") (mul (v "e") (.pow x (v "n")))) (v "p")))

/-- `Int[Log[c (d + e x^n)^p], x] := x Log[c (d + e x^n)^p]
- e n p Int[x^n/(d + e x^n), x]`. -/
def logPowBinom : CRule where
  id := "integration.log_power_binomial"; legacyId := some s!"{logBin}:1"
  shape := .antiderivRec; x := "x"
  body := logBinExpr
  result := add (mul x logBinExpr) (mul (mul (mul (mul (.int (-1)) (v "e")) (v "n")) (v "p")) (v "I1"))
  integrals := [("I1", mul (.pow x (v "n")) (inv (add (v "d") (mul (v "e") (.pow x (v "n"))))))]
  independent := ["c", "d", "e", "n", "p"]; priority := 350
  description := "Integration by parts of log(c (d + e x^n)^p)"
  provenance := migrated s!"{logBin}:1" "3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p.m#1"

/-! ### Third batch -/

private def quadM : String := "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m"
private def binW : String := "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q"
private def active : String := "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions"
private def lin3 : String := "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p"
private def lin4 : String := "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q"

/-- `d + e x`. -/
private abbrev linDE : Expr := add (v "d") (mul (v "e") x)
/-- `c d^2 + a e^2`. -/
private abbrev detQ : Expr := add (mul (v "c") (sq (v "d"))) (mul (v "a") (sq (v "e")))

/-- `Int[1/((d + e x) (a + c x^2)), x] := e^2/(c d^2 + a e^2) Int[1/(d + e x), x]
+ 1/(c d^2 + a e^2) Int[(c d - c e x)/(a + c x^2), x]` for `c d^2 + a e^2 ≠ 0`. -/
def pfLinQuad : CRule where
  id := "integration.partial_fractions_linear_quadratic"; legacyId := some s!"{quad}:79"
  shape := .antiderivRec; x := "x"
  body := mul (.int 1) (inv (mul linDE quadA))
  result := add (mul (mul (sq (v "e")) (inv detQ)) (v "I1")) (mul (mul (.int 1) (inv detQ)) (v "I2"))
  integrals := [("I1", mul (.int 1) (inv linDE)),
    ("I2", mul (add (mul (v "c") (v "d")) (mul (mul (mul (.int (-1)) (v "c")) (v "e")) x)) (inv quadA))]
  independent := ["a", "c", "d", "e"]; conditions := [.ne detQ (.int 0)]; priority := 360
  description := "Partial fractions of 1/((d + e x) (a + c x^2))"
  provenance := migrated s!"{quad}:79" s!"{quadM}#79"

/-- `c d^2 - b d e + a e^2`. -/
private abbrev detT : Expr :=
  add (add (mul (v "c") (sq (v "d"))) (mul (mul (mul (.int (-1)) (v "b")) (v "d")) (v "e")))
    (mul (v "a") (sq (v "e")))

/-- `Int[1/((d + e x) (a + b x + c x^2)), x]`, the partial fractions with
`c d^2 - b d e + a e^2` (and RUBI's two other conditions). -/
def pfLinTrinom : CRule where
  id := "integration.partial_fractions_linear_trinomial"; legacyId := some s!"{quad}:78"
  shape := .antiderivRec; x := "x"
  body := mul (.int 1) (inv (mul linDE trinom))
  result := add (mul (mul (sq (v "e")) (inv detT)) (v "I1")) (mul (mul (.int 1) (inv detT)) (v "I2"))
  integrals := [("I1", mul (.int 1) (inv linDE)),
    ("I2", mul (add (add (mul (v "c") (v "d")) (mul (mul (.int (-1)) (v "b")) (v "e")))
      (mul (mul (mul (.int (-1)) (v "c")) (v "e")) x)) (inv trinom))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (add (sq (v "b")) (mul (mul (mul (.int (-1)) (.int 4)) (v "a")) (v "c"))) (.int 0),
    .ne detT (.int 0), .ne detCD (.int 0)]
  priority := 370
  description := "Partial fractions of 1/((d + e x) (a + b x + c x^2))"
  provenance := migrated s!"{quad}:78" s!"{quadM}#78"

/-- `(e x)^m`. -/
private abbrev exm : Expr := .pow (mul (v "e") x) (v "m")

/-- `Int[(e x)^m/((a + b x^n) (c + d x^n)), x]`, the partial fractions of
`pfPower` with the factor `(e x)^m`. -/
def pfPowerWeighted : CRule where
  id := "integration.partial_fractions_power_weighted"; legacyId := some s!"{binW}:63"
  shape := .antiderivRec; x := "x"
  body := mul exm (inv (mul binA binB))
  result := add (mul (mul (v "b") (inv detBC)) (v "I1"))
    (mul (mul (mul (.int (-1)) (v "d")) (inv detBC)) (v "I2"))
  integrals := [("I1", mul exm (inv binA)), ("I2", mul exm (inv binB))]
  independent := ["a", "b", "c", "d", "e", "n", "m"]; conditions := [.ne detBC (.int 0)]
  priority := 380
  description := "Partial fractions of (e x)^m/((a + b x^n) (c + d x^n))"
  provenance := migrated s!"{binW}:63" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#63"

/-- `c + d x`. -/
private abbrev linCD : Expr := add (v "c") (mul (v "d") x)

/-- `Int[(e + f x)^m (a + b Sin[c + d x] Cos[c + d x])^n, x] :=
Int[(e + f x)^m (a + b Sin[2 c + 2 d x]/2)^n, x]`. -/
def sinCosDouble : CRule where
  id := "integration.sin_cos_double_angle"; legacyId := some s!"{active}:68"
  shape := .antiderivRec; x := "x"
  body := mul (.pow (add (v "e") (mul (v "f") x)) (v "m"))
    (.pow (add (v "a") (mul (mul (v "b") (sin linCD)) (cos linCD))) (v "n"))
  result := v "I1"
  integrals := [("I1", mul (.pow (add (v "e") (mul (v "f") x)) (v "m"))
    (.pow (add (v "a") (mul (mul (v "b")
      (sin (add (mul (.int 2) (v "c")) (mul (mul (.int 2) (v "d")) x)))) (inv (.int 2)))) (v "n")))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]; priority := 390
  description := "sin u cos u = sin(2 u)/2 under the integral"
  provenance := migrated s!"{active}:68" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#68"

/-- `Int[(e + f x^n)/((a + b x^n) (c + d x^n)), x] := (b e - a f)/(b c - a d)
Int[1/(a + b x^n), x] - (d e - c f)/(b c - a d) Int[1/(c + d x^n), x]`. -/
def pfGeneral : CRule where
  id := "integration.partial_fractions_general"; legacyId := some s!"{binTriple}:2"
  shape := .antiderivRec; x := "x"
  body := mul (add (v "e") (mul (v "f") (.pow x (v "n")))) (inv (mul binA binB))
  result := add
    (mul (mul (add (mul (v "b") (v "e")) (mul (mul (.int (-1)) (v "a")) (v "f"))) (inv detBC)) (v "I1"))
    (mul (mul (mul (.int (-1)) (add (mul (v "d") (v "e")) (mul (mul (.int (-1)) (v "c")) (v "f"))))
      (inv detBC)) (v "I2"))
  integrals := [("I1", mul (.int 1) (inv binA)), ("I2", mul (.int 1) (inv binB))]
  independent := ["a", "b", "c", "d", "e", "f", "n"]; priority := 400
  description := "Partial fractions of (e + f x^n)/((a + b x^n) (c + d x^n))"
  provenance := migrated s!"{binTriple}:2" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#2"

/-- `(c + d x)^n (e + f x)^p`. -/
private abbrev twoPow : Expr :=
  mul (.pow linCD (v "n")) (.pow (add (v "e") (mul (v "f") x)) (v "p"))

/-- `Int[(c + d x)^n (e + f x)^p (g + h x)/(a + b x), x] := h/b Int[…, x]
+ (b g - a h)/b Int[…/(a + b x), x]`. -/
def linOverLin : CRule where
  id := "integration.linear_factor_over_linear"; legacyId := some s!"{lin4}:17"
  shape := .antiderivRec; x := "x"
  body := mul (mul twoPow (add (v "g") (mul (v "h") x))) (inv (add (v "a") (mul (v "b") x)))
  result := add (mul (mul (v "h") (inv (v "b"))) (v "I1"))
    (mul (mul (add (mul (v "b") (v "g")) (mul (mul (.int (-1)) (v "a")) (v "h"))) (inv (v "b"))) (v "I2"))
  integrals := [("I1", twoPow), ("I2", mul twoPow (inv (add (v "a") (mul (v "b") x))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "n", "p"]; priority := 410
  description := "Split (g + h x)/(a + b x) under the integral"
  provenance := migrated s!"{lin4}:17" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#17"

/-- `b^2 - 4 a c`, `(b^2 - 4 a c)/(4 c)`, `(b + 2 c x)^2/(4 c)`. -/
private abbrev discr : Expr := add (sq (v "b")) (mul (mul (mul (.int (-1)) (.int 4)) (v "a")) (v "c"))
private abbrev discrOver : Expr := mul discr (inv (mul (.int 4) (v "c")))
private abbrev squareOver : Expr :=
  mul (sq (add (v "b") (mul (mul (.int 2) (v "c")) x))) (inv (mul (.int 4) (v "c")))

/-- `Int[Sin[a + b x + c x^2], x] := Cos[(b^2 - 4 a c)/(4 c)] Int[Sin[(b + 2 c x)^2/(4 c)], x]
- Sin[(b^2 - 4 a c)/(4 c)] Int[Cos[(b + 2 c x)^2/(4 c)], x]` (completing the square). -/
def sinTrinomSq : CRule where
  id := "integration.sin_trinomial_square"; legacyId := some s!"{sineQuad}:3"
  shape := .antiderivRec; x := "x"
  body := sin trinom
  result := add (mul (cos discrOver) (v "I1")) (mul (neg (sin discrOver)) (v "I2"))
  integrals := [("I1", sin squareOver), ("I2", cos squareOver)]
  independent := ["a", "b", "c"]; conditions := [.ne discr (.int 0)]; priority := 420
  description := "Complete the square in sin(a + b x + c x^2)"
  provenance := migrated s!"{sineQuad}:3" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#3"

/-- `Int[Cos[a + b x + c x^2], x]`, completing the square. -/
def cosTrinomSq : CRule where
  id := "integration.cos_trinomial_square"; legacyId := some s!"{sineQuad}:4"
  shape := .antiderivRec; x := "x"
  body := cos trinom
  result := add (mul (cos discrOver) (v "I1")) (mul (sin discrOver) (v "I2"))
  integrals := [("I1", cos squareOver), ("I2", sin squareOver)]
  independent := ["a", "b", "c"]; conditions := [.ne discr (.int 0)]; priority := 430
  description := "Complete the square in cos(a + b x + c x^2)"
  provenance := migrated s!"{sineQuad}:4" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#4"

/-- `Int[(c + d x^n)/(a + b x^n), x] := c x/a - (b c - a d)/a Int[1/(b + a x^(-n)), x]`
for `b c - a d ≠ 0`, `n < 0`. -/
def binomRatio : CRule where
  id := "integration.binomial_ratio_negative_power"; legacyId := some s!"{binPair}:14"
  shape := .antiderivRec; x := "x"
  body := mul binB (inv binA)
  result := add (mul (mul (v "c") x) (inv (v "a")))
    (mul (mul (mul (.int (-1)) detBC) (inv (v "a"))) (v "I1"))
  integrals := [("I1", mul (.int 1) (inv (add (v "b") (mul (v "a") (.pow x (mul (.int (-1)) (v "n")))))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.ne detBC (.int 0), .gt (.int 0) (v "n")]; priority := 440
  description := "Antiderivative of (c + d x^n)/(a + b x^n) for n < 0"
  provenance := migrated s!"{binPair}:14" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#14"

/-- `Int[(e x)^m (a + b Log[c Log[d x^n]^p]), x]`, by parts, for `m ≠ -1`. -/
def logLogWeighted : CRule where
  id := "integration.power_log_log"; legacyId := some s!"{logMisc}:3"
  shape := .antiderivRec; x := "x"
  body := mul exm (add (v "a") (mul (v "b") logLog))
  result := add (mul (mul (.pow (mul (v "e") x) (add (v "m") (.int 1))) (add (v "a") (mul (v "b") logLog)))
      (inv (mul (v "e") (add (v "m") (.int 1)))))
    (mul (mul (mul (mul (mul (.int (-1)) (v "b")) (v "n")) (v "p")) (inv (add (v "m") (.int 1)))) (v "I1"))
  integrals := [("I1", mul exm (inv logDxn))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]; conditions := [.ne (v "m") (.int (-1))]
  priority := 450
  description := "Integration by parts of (e x)^m (a + b log(c log(d x^n)^p))"
  provenance := migrated s!"{logMisc}:3" "3 Logarithms/3.5 Miscellaneous logarithms.m#3"

/-- `n + p + 2`. -/
private abbrev np2 : Expr := add (add (v "n") (v "p")) (.int 2)

/-- `Int[(a + b x) (c + d x)^n (e + f x)^p, x]` for `n + p + 2 ≠ 0`. -/
def linTwoPow : CRule where
  id := "integration.linear_times_two_powers"; legacyId := some s!"{lin3}:8"
  shape := .antiderivRec; x := "x"
  body := mul (mul (add (v "a") (mul (v "b") x)) (.pow linCD (v "n"))) (.pow (add (v "e") (mul (v "f") x)) (v "p"))
  result := add
    (mul (mul (mul (v "b") (.pow linCD (add (v "n") (.int 1)))) (.pow (add (v "e") (mul (v "f") x)) (add (v "p") (.int 1))))
      (inv (mul (mul (v "d") (v "f")) np2)))
    (mul (mul (add (mul (mul (mul (v "a") (v "d")) (v "f")) np2)
        (mul (mul (.int (-1)) (v "b")) (add (mul (mul (v "d") (v "e")) (add (v "n") (.int 1)))
          (mul (mul (v "c") (v "f")) (add (v "p") (.int 1))))))
      (inv (mul (mul (v "d") (v "f")) np2))) (v "I1"))
  integrals := [("I1", twoPow)]
  independent := ["a", "b", "c", "d", "e", "f", "n", "p"]; conditions := [.ne np2 (.int 0)]
  priority := 460
  description := "Antiderivative of (a + b x) (c + d x)^n (e + f x)^p"
  provenance := migrated s!"{lin3}:8" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#8"

/-- `Int[(f x)^m (a + b Log[c (d + e x^n)^p]), x]`, by parts, for `m ≠ -1`. -/
def logBinWeighted : CRule where
  id := "integration.power_log_binomial"; legacyId := some s!"{logBin}:7"
  shape := .antiderivRec; x := "x"
  body := mul (.pow (mul (v "f") x) (v "m")) (add (v "a") (mul (v "b") logBinExpr))
  result := add
    (mul (mul (.pow (mul (v "f") x) (add (v "m") (.int 1))) (add (v "a") (mul (v "b") logBinExpr)))
      (inv (mul (v "f") (add (v "m") (.int 1)))))
    (mul (mul (mul (mul (mul (mul (.int (-1)) (v "b")) (v "e")) (v "n")) (v "p"))
      (inv (mul (v "f") (add (v "m") (.int 1))))) (v "I1"))
  integrals := [("I1", mul (mul (.pow x (add (v "n") (mul (.int (-1)) (.int 1))))
    (.pow (mul (v "f") x) (add (v "m") (.int 1)))) (inv (add (v "d") (mul (v "e") (.pow x (v "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]; conditions := [.ne (v "m") (.int (-1))]
  priority := 470
  description := "Integration by parts of (f x)^m (a + b log(c (d + e x^n)^p))"
  provenance := migrated s!"{logBin}:7" "3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p.m#7"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_zero (I : Interp 𝕜) : I.toInt? (0 : 𝕜) = some 0 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

/-- The addition formula proves `sinAddSq` in any interpretation having it. -/
theorem sinAddSq_holds (I : Interp 𝕜)
    (hadd : ∀ a b : 𝕜, I.sin (a + b) = I.sin a * I.cos b + I.cos a * I.sin b) :
    AntiderivRecHolds I "x" sinAddSq.conditions sinAddSq.body sinAddSq.result
      sinAddSq.integrals := by
  intro env _ t _
  refine ⟨fun i hi => Eventually.of_forall fun _ => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [sinAddSq, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp [Defined, eval, toInt?_two]
  · exact Eventually.of_forall fun _ => by simp [sinAddSq, Defined]
  · simp only [sinAddSq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (sinAddSq.integrals.map (·.1)) Φ "x" w)
        sinAddSq.result) = fun w => I.sin (env "c") * Φ "I1" w + I.cos (env "c") * Φ "I2" w := by
      funext w
      simp [sinAddSq, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [sinAddSq, eval, toInt?_two, hadd]

theorem sinAddSq_real : sinAddSq.Holds .real := sinAddSq_holds Interp.real Real.sin_add

theorem sinAddSq_complex : sinAddSq.Holds .complex :=
  sinAddSq_holds Interp.complex Complex.sin_add

/-- The addition formula proves `cosAddSq`. -/
theorem cosAddSq_holds (I : Interp 𝕜)
    (hadd : ∀ a b : 𝕜, I.cos (a + b) = I.cos a * I.cos b - I.sin a * I.sin b) :
    AntiderivRecHolds I "x" cosAddSq.conditions cosAddSq.body cosAddSq.result
      cosAddSq.integrals := by
  intro env _ t _
  refine ⟨fun i hi => Eventually.of_forall fun _ => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [cosAddSq, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp [Defined, eval, toInt?_two]
  · exact Eventually.of_forall fun _ => by simp [cosAddSq, Defined]
  · simp only [cosAddSq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (cosAddSq.integrals.map (·.1)) Φ "x" w)
        cosAddSq.result) =
        fun w => I.cos (env "c") * Φ "I1" w + -1 * I.sin (env "c") * Φ "I2" w := by
      funext w
      simp [cosAddSq, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp only [cosAddSq, eval, Interp.toInt?_cast, Function.update_self, Function.update_apply]
    simp [hadd]
    ring

theorem cosAddSq_real : cosAddSq.Holds .real := cosAddSq_holds Interp.real Real.cos_add

theorem cosAddSq_complex : cosAddSq.Holds .complex :=
  cosAddSq_holds Interp.complex Complex.cos_add

/-- The addition formula proves `sinAddPowOverX`. -/
theorem sinAddPowOverX_holds (I : Interp 𝕜)
    (hadd : ∀ a b : 𝕜, I.sin (a + b) = I.sin a * I.cos b + I.cos a * I.sin b) :
    AntiderivRecHolds I "x" sinAddPowOverX.conditions sinAddPowOverX.body
      sinAddPowOverX.result sinAddPowOverX.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [sinAddPowOverX, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simpa [sinAddPowOverX, Defined, eval, toInt?_neg_one] using hw
  · exact Eventually.of_forall fun _ => by simp [sinAddPowOverX, Defined]
  · simp only [sinAddPowOverX, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (sinAddPowOverX.integrals.map (·.1)) Φ "x" w)
        sinAddPowOverX.result) =
        fun w => I.sin (env "c") * Φ "I1" w + I.cos (env "c") * Φ "I2" w := by
      funext w
      simp [sinAddPowOverX, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [sinAddPowOverX, eval, toInt?_neg_one, hadd]
    ring

theorem sinAddPowOverX_real : sinAddPowOverX.Holds .real :=
  sinAddPowOverX_holds Interp.real Real.sin_add

theorem sinAddPowOverX_complex : sinAddPowOverX.Holds .complex :=
  sinAddPowOverX_holds Interp.complex Complex.sin_add

/-- The addition formula proves `cosAddPowOverX`. -/
theorem cosAddPowOverX_holds (I : Interp 𝕜)
    (hadd : ∀ a b : 𝕜, I.cos (a + b) = I.cos a * I.cos b - I.sin a * I.sin b) :
    AntiderivRecHolds I "x" cosAddPowOverX.conditions cosAddPowOverX.body
      cosAddPowOverX.result cosAddPowOverX.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [cosAddPowOverX, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simpa [cosAddPowOverX, Defined, eval, toInt?_neg_one] using hw
  · exact Eventually.of_forall fun _ => by simp [cosAddPowOverX, Defined]
  · simp only [cosAddPowOverX, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (cosAddPowOverX.integrals.map (·.1)) Φ "x" w)
        cosAddPowOverX.result) =
        fun w => I.cos (env "c") * Φ "I1" w + -1 * I.sin (env "c") * Φ "I2" w := by
      funext w
      simp [cosAddPowOverX, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp only [cosAddPowOverX, eval, Interp.toInt?_cast, Function.update_self,
      Function.update_apply]
    simp [hadd]
    ring

theorem cosAddPowOverX_real : cosAddPowOverX.Holds .real :=
  cosAddPowOverX_holds Interp.real Real.cos_add

theorem cosAddPowOverX_complex : cosAddPowOverX.Holds .complex :=
  cosAddPowOverX_holds Interp.complex Complex.cos_add

/-- The half-angle formula proves `powSinSq`. -/
theorem powSinSq_holds (I : Interp 𝕜) (h2 : (2 : 𝕜) ≠ 0)
    (hsq : ∀ a y : 𝕜, I.sin (a + y * 2⁻¹) ^ 2 = 2⁻¹ - 2⁻¹ * I.cos (2 * a + y)) :
    AntiderivRecHolds I "x" powSinSq.conditions powSinSq.body powSinSq.result
      powSinSq.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powSinSq, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simp [powSinSq, Defined, eval, toInt?_two, toInt?_neg_one] at hw ⊢
      tauto
  · exact Eventually.of_forall fun _ => by
      simp [powSinSq, Defined, eval, toInt?_neg_one, h2]
  · simp only [powSinSq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (powSinSq.integrals.map (·.1)) Φ "x" w)
        powSinSq.result) = fun w => 1 * 2⁻¹ * Φ "I1" w + -1 * 1 * 2⁻¹ * Φ "I2" w := by
      funext w
      simp [powSinSq, eval, recEnv, toInt?_neg_one]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [powSinSq, eval, toInt?_two, toInt?_neg_one, hsq]
    ring

theorem powSinSq_real : powSinSq.Holds .real := by
  refine powSinSq_holds Interp.real two_ne_zero fun a y => ?_
  simp only [Interp.real]
  rw [Real.sin_sq, Real.cos_sq, show 2 * (a + y * 2⁻¹) = 2 * a + y by ring]
  ring

theorem powSinSq_complex : powSinSq.Holds .complex := by
  refine powSinSq_holds Interp.complex two_ne_zero fun a y => ?_
  simp only [Interp.complex]
  rw [Complex.sin_sq, Complex.cos_sq, show 2 * (a + y * 2⁻¹) = 2 * a + y by ring]
  ring

/-- The half-angle formula proves `powCosSq`. -/
theorem powCosSq_holds (I : Interp 𝕜) (h2 : (2 : 𝕜) ≠ 0)
    (hsq : ∀ a y : 𝕜, I.cos (a + y * 2⁻¹) ^ 2 = 2⁻¹ + 2⁻¹ * I.cos (2 * a + y)) :
    AntiderivRecHolds I "x" powCosSq.conditions powCosSq.body powCosSq.result
      powCosSq.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powCosSq, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simp [powCosSq, Defined, eval, toInt?_two, toInt?_neg_one] at hw ⊢
      tauto
  · exact Eventually.of_forall fun _ => by
      simp [powCosSq, Defined, eval, toInt?_neg_one, h2]
  · simp only [powCosSq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (powCosSq.integrals.map (·.1)) Φ "x" w)
        powCosSq.result) = fun w => 1 * 2⁻¹ * Φ "I1" w + 1 * 2⁻¹ * Φ "I2" w := by
      funext w
      simp [powCosSq, eval, recEnv, toInt?_neg_one]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [powCosSq, eval, toInt?_two, toInt?_neg_one, hsq]
    ring

theorem powCosSq_real : powCosSq.Holds .real := by
  refine powCosSq_holds Interp.real two_ne_zero fun a y => ?_
  simp only [Interp.real]
  rw [Real.cos_sq, show 2 * (a + y * 2⁻¹) = 2 * a + y by ring]
  ring

theorem powCosSq_complex : powCosSq.Holds .complex := by
  refine powCosSq_holds Interp.complex two_ne_zero fun a y => ?_
  simp only [Interp.complex]
  rw [Complex.cos_sq, show 2 * (a + y * 2⁻¹) = 2 * a + y by ring]
  ring

/-- **Counterexample** to `logPowLog`, for an interpretation with `ln` defined
at `1` and `ln 1 = 0`: at `c = d = 1`, `n = p = 0` the integrand `log(1)` is
defined everywhere, but the residual integrand `1/log(d x^n)` is not. -/
theorem logPowLog_not (I : Interp 𝕜) (h1 : I.lnDefined 1) (h0 : I.ln 1 = 0) :
    ¬ AntiderivRecHolds I "x" logPowLog.conditions logPowLog.body logPowLog.result
      logPowLog.integrals := by
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" ∨ s = "d" then 1 else 0) 1
    (by simp [logPowLog]) (Eventually.of_forall fun _ => ?_) ?_
  · simp [logPowLog, Defined, eval, toInt?_zero, h1]
  · simp only [logPowLog, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]
    intro h
    simp only [Defined, eval, Interp.toInt?_cast] at h
    simp [toInt?_zero, h0] at h

theorem logPowLog_counterexample_real : ¬ logPowLog.Holds .real :=
  logPowLog_not Interp.real (show (0 : ℝ) < 1 from one_pos) Real.log_one

theorem logPowLog_counterexample_complex : ¬ logPowLog.Holds .complex :=
  logPowLog_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero) Complex.log_one

/-- **Counterexample** to `sinXLog` (and `cosXLog` below): at `a = 0`, `b = 1`
the integrand is defined near `1`, but `a^(-1)` is not. -/
theorem sinXLog_not (I : Interp 𝕜) (hnear : ∀ᶠ w in 𝓝 (1 : 𝕜), I.lnDefined w) :
    ¬ AntiderivRecHolds I "x" sinXLog.conditions sinXLog.body sinXLog.result
      sinXLog.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" then 1 else 0) 1
    (by simp [sinXLog]) ?_ (fun _ w => w * eval I (Function.update
      (fun s => if s = "b" then 1 else 0) "x" 1) (sin xLog)) ?_ ?_
  · filter_upwards [hnear] with w hw
    simp [sinXLog, Defined, eval, hw]
  · simp only [sinXLog, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [sinXLog, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem sinXLog_counterexample_real : ¬ sinXLog.Holds .real :=
  sinXLog_not Interp.real (lt_mem_nhds one_pos)

theorem sinXLog_counterexample_complex : ¬ sinXLog.Holds .complex :=
  sinXLog_not Interp.complex (eventually_ne_nhds one_ne_zero)

theorem cosXLog_not (I : Interp 𝕜) (hnear : ∀ᶠ w in 𝓝 (1 : 𝕜), I.lnDefined w) :
    ¬ AntiderivRecHolds I "x" cosXLog.conditions cosXLog.body cosXLog.result
      cosXLog.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" then 1 else 0) 1
    (by simp [cosXLog]) ?_ (fun _ w => w * eval I (Function.update
      (fun s => if s = "b" then 1 else 0) "x" 1) (cos xLog)) ?_ ?_
  · filter_upwards [hnear] with w hw
    simp [cosXLog, Defined, eval, hw]
  · simp only [cosXLog, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [cosXLog, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem cosXLog_counterexample_real : ¬ cosXLog.Holds .real :=
  cosXLog_not Interp.real (lt_mem_nhds one_pos)

theorem cosXLog_counterexample_complex : ¬ cosXLog.Holds .complex :=
  cosXLog_not Interp.complex (eventually_ne_nhds one_ne_zero)

/-- **Counterexample** to `linearQuadPow`: at `a = 1` and the other
metavariables `0` the condition `p ≠ -1` holds and the integrand is defined
everywhere, but `(2 c (p + 1))^(-1)` is not. -/
theorem linearQuadPow_not (I : Interp 𝕜) :
    ¬ AntiderivRecHolds I "x" linearQuadPow.conditions linearQuadPow.body linearQuadPow.result
      linearQuadPow.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "a" then 1 else 0) 0
    (by simp [linearQuadPow, Cond.Holds, Defined, eval]) (Eventually.of_forall fun _ => ?_)
    (fun _ w => w * 1) ?_ ?_
  · simp [linearQuadPow, Defined, eval, toInt?_zero, toInt?_two]
  · simp only [linearQuadPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    simpa [eval, toInt?_zero, toInt?_two] using hasDerivAt_mul_const (1 : 𝕜)
  · intro h
    simp only [linearQuadPow, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem linearQuadPow_counterexample_real : ¬ linearQuadPow.Holds .real :=
  linearQuadPow_not Interp.real

theorem linearQuadPow_counterexample_complex : ¬ linearQuadPow.Holds .complex :=
  linearQuadPow_not Interp.complex

/-! ### Second batch -/

/-- Partial fractions of `1/((a + b x) (c + d x))`, in any interpretation. -/
theorem pfLinear_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" pfLinear.conditions pfLinear.body pfLinear.result
      pfLinear.integrals := by
  intro env hc t hF
  have hK := hc (.ne detBC (.int 0)) (by simp [pfLinear])
  simp [Cond.Holds, Defined, eval] at hK
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [pfLinear, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simp [pfLinear, Defined, eval, toInt?_neg_one] at hw ⊢
      tauto
  · exact Eventually.of_forall fun _ => by simp [pfLinear, Defined, eval, recEnv, toInt?_neg_one, hK]
  · simp only [pfLinear, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [pfLinear, Defined, eval, toInt?_neg_one] at ht
    obtain ⟨hA, hB⟩ := ht
    have hfun : (fun w => eval I (recEnv env (pfLinear.integrals.map (·.1)) Φ "x" w)
        pfLinear.result) = fun w =>
          env "b" * (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ * Φ "I1" w +
            -1 * env "d" * (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ * Φ "I2" w := by
      funext w
      simp [pfLinear, eval, recEnv, toInt?_neg_one]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [pfLinear, eval, toInt?_neg_one]
    field_simp
    ring

theorem pfLinear_real : pfLinear.Holds .real := pfLinear_holds Interp.real

theorem pfLinear_complex : pfLinear.Holds .complex := pfLinear_holds Interp.complex

/-- Partial fractions of `1/((a + b x^n) (c + d x^n))`, in any interpretation. -/
theorem pfPower_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" pfPower.conditions pfPower.body pfPower.result
      pfPower.integrals := by
  intro env hc t hF
  have hK := hc (.ne detBC (.int 0)) (by simp [pfPower])
  simp [Cond.Holds, Defined, eval] at hK
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [pfPower, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simp [pfPower, Defined, eval, toInt?_neg_one] at hw ⊢
      tauto
  · exact Eventually.of_forall fun _ => by simp [pfPower, Defined, eval, recEnv, toInt?_neg_one, hK]
  · simp only [pfPower, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [pfPower, Defined, eval, toInt?_neg_one] at ht
    obtain ⟨-, hA, hB⟩ := ht
    have hfun : (fun w => eval I (recEnv env (pfPower.integrals.map (·.1)) Φ "x" w)
        pfPower.result) = fun w =>
          env "b" * (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ * Φ "I1" w +
            -1 * env "d" * (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ * Φ "I2" w := by
      funext w
      simp [pfPower, eval, recEnv, toInt?_neg_one]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [pfPower, eval, toInt?_neg_one]
    field_simp
    ring

theorem pfPower_real : pfPower.Holds .real := pfPower_holds Interp.real

theorem pfPower_complex : pfPower.Holds .complex := pfPower_holds Interp.complex

/-- Linearity: `(…)(e + f x^n) = e (…) + f x^n (…)`. -/
theorem splitBinomial_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" splitBinomial.conditions splitBinomial.body splitBinomial.result
      splitBinomial.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [splitBinomial, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp only [splitBinomial, Defined] at hw ⊢
      exact hw.1
    · filter_upwards [hF] with w hw
      simp only [splitBinomial, Defined] at hw ⊢
      exact ⟨⟨hw.2.2.2, hw.1.1⟩, hw.1.2⟩
  · exact Eventually.of_forall fun _ => by simp [splitBinomial, Defined]
  · simp only [splitBinomial, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (splitBinomial.integrals.map (·.1)) Φ "x" w)
        splitBinomial.result) = fun w => env "e" * Φ "I1" w + env "f" * Φ "I2" w := by
      funext w
      simp [splitBinomial, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [splitBinomial, eval]
    ring

theorem splitBinomial_real : splitBinomial.Holds .real := splitBinomial_holds Interp.real

theorem splitBinomial_complex : splitBinomial.Holds .complex :=
  splitBinomial_holds Interp.complex

/-- Linearity: `(g + h x)(…) = g (…) + h x (…)`. -/
theorem splitQuadratic_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" splitQuadratic.conditions splitQuadratic.body splitQuadratic.result
      splitQuadratic.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [splitQuadratic, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp only [splitQuadratic, Defined] at hw ⊢
      exact ⟨hw.1.2, hw.2⟩
    · filter_upwards [hF] with w hw
      simp only [splitQuadratic, Defined] at hw ⊢
      exact ⟨⟨trivial, hw.1.2⟩, hw.2⟩
  · exact Eventually.of_forall fun _ => by simp [splitQuadratic, Defined]
  · simp only [splitQuadratic, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (splitQuadratic.integrals.map (·.1)) Φ "x" w)
        splitQuadratic.result) = fun w => env "g" * Φ "I1" w + env "h" * Φ "I2" w := by
      funext w
      simp [splitQuadratic, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [splitQuadratic, eval]
    ring

theorem splitQuadratic_real : splitQuadratic.Holds .real := splitQuadratic_holds Interp.real

theorem splitQuadratic_complex : splitQuadratic.Holds .complex :=
  splitQuadratic_holds Interp.complex

/-- **Counterexample** to `linSinQuad`: at `b = e = 1` and the other
metavariables `0`, `2 c d - b e = -1 ≠ 0` and the integrand is defined
everywhere, but `(2 c)^(-1)` is not. -/
theorem linSinQuad_not (I : Interp 𝕜) :
    ¬ AntiderivRecHolds I "x" linSinQuad.conditions linSinQuad.body linSinQuad.result
      linSinQuad.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" then 1 else 0) 0
    (by simp [linSinQuad, Cond.Holds, Defined, eval]) (Eventually.of_forall fun _ => ?_)
    (fun _ w => w * eval I (Function.update (fun s => if s = "b" ∨ s = "e" then 1 else 0) "x" 0)
      (sin trinom)) ?_ ?_
  · simp [linSinQuad, Defined, eval, toInt?_two]
  · simp only [linSinQuad, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [linSinQuad, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem linSinQuad_counterexample_real : ¬ linSinQuad.Holds .real := linSinQuad_not Interp.real

theorem linSinQuad_counterexample_complex : ¬ linSinQuad.Holds .complex :=
  linSinQuad_not Interp.complex

/-- **Counterexample** to `linCosQuad`, as for `linSinQuad`. -/
theorem linCosQuad_not (I : Interp 𝕜) :
    ¬ AntiderivRecHolds I "x" linCosQuad.conditions linCosQuad.body linCosQuad.result
      linCosQuad.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" then 1 else 0) 0
    (by simp [linCosQuad, Cond.Holds, Defined, eval]) (Eventually.of_forall fun _ => ?_)
    (fun _ w => w * eval I (Function.update (fun s => if s = "b" ∨ s = "e" then 1 else 0) "x" 0)
      (cos trinom)) ?_ ?_
  · simp [linCosQuad, Defined, eval, toInt?_two]
  · simp only [linCosQuad, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [linCosQuad, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem linCosQuad_counterexample_real : ¬ linCosQuad.Holds .real := linCosQuad_not Interp.real

theorem linCosQuad_counterexample_complex : ¬ linCosQuad.Holds .complex :=
  linCosQuad_not Interp.complex

/-- **Counterexample** to `linTrinomPow`: at `b = e = 1` and the other
metavariables `0` the conditions hold and the integrand is defined everywhere,
but `(2 c (p + 1))^(-1)` is not. -/
theorem linTrinomPow_not (I : Interp 𝕜) :
    ¬ AntiderivRecHolds I "x" linTrinomPow.conditions linTrinomPow.body linTrinomPow.result
      linTrinomPow.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" then 1 else 0) 0
    (by simp [linTrinomPow, Cond.Holds, Defined, eval]) (Eventually.of_forall fun _ => ?_)
    (fun _ w => w * eval I (Function.update (fun s => if s = "b" ∨ s = "e" then 1 else 0) "x" 0)
      (.pow trinom (v "p"))) ?_ ?_
  · simp [linTrinomPow, Defined, eval, toInt?_zero, toInt?_two]
  · simp only [linTrinomPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [linTrinomPow, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem linTrinomPow_counterexample_real : ¬ linTrinomPow.Holds .real :=
  linTrinomPow_not Interp.real

theorem linTrinomPow_counterexample_complex : ¬ linTrinomPow.Holds .complex :=
  linTrinomPow_not Interp.complex

/-- **Counterexample** to `prodOverTrinom`: at `a = b = 1` and the other
metavariables `0`, `b^2 - 4 a c = 1 ≠ 0` and the integrand is defined near
`0`, but `c^(-1)` is not. -/
theorem prodOverTrinom_not (I : Interp 𝕜) :
    ¬ AntiderivRecHolds I "x" prodOverTrinom.conditions prodOverTrinom.body
      prodOverTrinom.result prodOverTrinom.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" then 1 else 0) 0
    (by simp [prodOverTrinom, Cond.Holds, Defined, eval, toInt?_two]) ?_
    (fun _ w => w * eval I (Function.update (fun s => if s = "a" ∨ s = "b" then 1 else 0) "x" 0)
      (prodOverTrinom.integrals.head!.2)) ?_ ?_
  · filter_upwards [eventually_ne_nhds (neg_ne_zero.mpr (one_ne_zero (α := 𝕜))).symm] with w hw
    simp [prodOverTrinom, Defined, eval, toInt?_neg_one, toInt?_two]
    intro h
    exact hw (by linear_combination h)
  · simp only [prodOverTrinom, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [prodOverTrinom, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem prodOverTrinom_counterexample_real : ¬ prodOverTrinom.Holds .real :=
  prodOverTrinom_not Interp.real

theorem prodOverTrinom_counterexample_complex : ¬ prodOverTrinom.Holds .complex :=
  prodOverTrinom_not Interp.complex

/-- **Counterexample** to `prodOverQuad`: at `a = 1` and the other
metavariables `0` the integrand is defined everywhere, but `c^(-1)` is not. -/
theorem prodOverQuad_not (I : Interp 𝕜) :
    ¬ AntiderivRecHolds I "x" prodOverQuad.conditions prodOverQuad.body prodOverQuad.result
      prodOverQuad.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "a" then 1 else 0) 0
    (by simp [prodOverQuad]) (Eventually.of_forall fun _ => ?_)
    (fun _ w => w * eval I (Function.update (fun s => if s = "a" then 1 else 0) "x" 0)
      (prodOverQuad.integrals.head!.2)) ?_ ?_
  · simp [prodOverQuad, Defined, eval, toInt?_neg_one, toInt?_two]
  · simp only [prodOverQuad, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [prodOverQuad, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem prodOverQuad_counterexample_real : ¬ prodOverQuad.Holds .real :=
  prodOverQuad_not Interp.real

theorem prodOverQuad_counterexample_complex : ¬ prodOverQuad.Holds .complex :=
  prodOverQuad_not Interp.complex

/-- **Counterexample** to `powerRatio`: at `c = 1` and the other metavariables
`0` the integrand is defined everywhere, but `d^(-1)` is not. -/
theorem powerRatio_not (I : Interp 𝕜) :
    ¬ AntiderivRecHolds I "x" powerRatio.conditions powerRatio.body powerRatio.result
      powerRatio.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "c" then 1 else 0) 0
    (by simp [powerRatio]) (Eventually.of_forall fun _ => ?_)
    (fun h w => if h = "I1" then
        w * eval I (Function.update (fun s => if s = "c" then 1 else 0) "x" 0) (.pow binA (v "p"))
      else w * eval I (Function.update (fun s => if s = "c" then 1 else 0) "x" 0)
        (mul (.pow binA (v "p")) (inv binB))) ?_ ?_
  · simp [powerRatio, Defined, eval, toInt?_zero, toInt?_neg_one]
  · simp only [powerRatio, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    constructor
    · simpa using hasDerivAt_mul_const
        (eval I (Function.update (fun s => if s = "c" then 1 else 0) "x" 0) (.pow binA (v "p")))
    · simpa using hasDerivAt_mul_const
        (eval I (Function.update (fun s => if s = "c" then 1 else 0) "x" 0)
          (mul (.pow binA (v "p")) (inv binB)))
  · intro h
    simp only [powerRatio, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem powerRatio_counterexample_real : ¬ powerRatio.Holds .real := powerRatio_not Interp.real

theorem powerRatio_counterexample_complex : ¬ powerRatio.Holds .complex :=
  powerRatio_not Interp.complex

/-- **Counterexample** to `logPowBinom`, for an interpretation with `ln`
defined at `1`: at `c = 1` and `d = e = n = p = 0` the integrand `log 1` is
defined everywhere, but the residual integrand `x^n/(d + e x^n)` is not. -/
theorem logPowBinom_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" logPowBinom.conditions logPowBinom.body logPowBinom.result
      logPowBinom.integrals := by
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" then 1 else 0) 1
    (by simp [logPowBinom]) (Eventually.of_forall fun _ => ?_) ?_
  · simp [logPowBinom, Defined, eval, toInt?_zero, h1]
  · simp only [logPowBinom, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]
    intro h
    simp only [Defined, eval, Interp.toInt?_cast] at h
    simp [toInt?_zero] at h

theorem logPowBinom_counterexample_real : ¬ logPowBinom.Holds .real :=
  logPowBinom_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem logPowBinom_counterexample_complex : ¬ logPowBinom.Holds .complex :=
  logPowBinom_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)


theorem pfLinQuad_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" pfLinQuad.conditions pfLinQuad.body pfLinQuad.result
      pfLinQuad.integrals := by
  intro env hc t hF
  have hK := hc (.ne detQ (.int 0)) (by simp [pfLinQuad])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hK
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [pfLinQuad, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simp [pfLinQuad, Defined, eval, toInt?_neg_one, toInt?_two] at hw ⊢
      tauto
  · exact Eventually.of_forall fun _ => by
      simp [pfLinQuad, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hK]
  · simp only [pfLinQuad, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [pfLinQuad, Defined, eval, toInt?_neg_one, toInt?_two] at ht
    obtain ⟨hA, hB⟩ := ht
    have hfun : (fun w => eval I (recEnv env (pfLinQuad.integrals.map (·.1)) Φ "x" w)
        pfLinQuad.result) = fun w => env "e" ^ 2 * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2)⁻¹ * Φ "I1" w + 1 * (env "c" * env "d" ^ 2 + env "a" * env "e" ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [pfLinQuad, eval, recEnv, toInt?_neg_one, toInt?_two]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [pfLinQuad, eval, toInt?_neg_one, toInt?_two]
    field_simp
    rw [div_eq_one_iff_eq (fun h => hK (by linear_combination h))]
    ring

theorem pfLinQuad_real : pfLinQuad.Holds .real := pfLinQuad_holds Interp.real

theorem pfLinQuad_complex : pfLinQuad.Holds .complex := pfLinQuad_holds Interp.complex

theorem pfLinTrinom_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" pfLinTrinom.conditions pfLinTrinom.body pfLinTrinom.result
      pfLinTrinom.integrals := by
  intro env hc t hF
  have hK := hc (.ne detT (.int 0)) (by simp [pfLinTrinom])
  simp [Cond.Holds, Defined, eval, toInt?_two] at hK
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [pfLinTrinom, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simp [pfLinTrinom, Defined, eval, toInt?_neg_one, toInt?_two] at hw ⊢
      tauto
  · exact Eventually.of_forall fun _ => by
      simp [pfLinTrinom, Defined, eval, recEnv, toInt?_neg_one, toInt?_two, hK]
  · simp only [pfLinTrinom, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [pfLinTrinom, Defined, eval, toInt?_neg_one, toInt?_two] at ht
    obtain ⟨hA, hB⟩ := ht
    have hfun : (fun w => eval I (recEnv env (pfLinTrinom.integrals.map (·.1)) Φ "x" w)
        pfLinTrinom.result) = fun w => env "e" ^ 2 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2)⁻¹ * Φ "I1" w + 1 * (env "c" * env "d" ^ 2 + -1 * env "b" * env "d" * env "e" + env "a" * env "e" ^ 2)⁻¹ * Φ "I2" w := by
      funext w
      simp [pfLinTrinom, eval, recEnv, toInt?_neg_one, toInt?_two]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [pfLinTrinom, eval, toInt?_neg_one, toInt?_two]
    field_simp
    rw [div_eq_one_iff_eq (fun h => hK (by linear_combination h))]
    ring

theorem pfLinTrinom_real : pfLinTrinom.Holds .real := pfLinTrinom_holds Interp.real

theorem pfLinTrinom_complex : pfLinTrinom.Holds .complex := pfLinTrinom_holds Interp.complex

theorem pfPowerWeighted_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" pfPowerWeighted.conditions pfPowerWeighted.body
      pfPowerWeighted.result pfPowerWeighted.integrals := by
  intro env hc t hF
  have hK := hc (.ne detBC (.int 0)) (by simp [pfPowerWeighted])
  simp [Cond.Holds, Defined, eval] at hK
  rcases hm : I.toInt? (env "m") with _ | m
  · exfalso
    have h := hF.self_of_nhds
    simp [pfPowerWeighted, Defined, eval, hm] at h
  rcases hn : I.toInt? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [pfPowerWeighted, Defined, eval, hn] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [pfPowerWeighted, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simp [pfPowerWeighted, Defined, eval, toInt?_neg_one, hm, hn] at hw ⊢
      tauto
  · exact Eventually.of_forall fun _ => by
      simp [pfPowerWeighted, Defined, eval, recEnv, toInt?_neg_one, hK]
  · simp only [pfPowerWeighted, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [pfPowerWeighted, Defined, eval, toInt?_neg_one, hm, hn] at ht
    have hA : ¬ env "a" + env "b" * t ^ n = 0 := by tauto
    have hB : ¬ env "c" + env "d" * t ^ n = 0 := by tauto
    have hfun : (fun w => eval I (recEnv env (pfPowerWeighted.integrals.map (·.1)) Φ "x" w)
        pfPowerWeighted.result) = fun w =>
          env "b" * (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ * Φ "I1" w +
            -1 * env "d" * (env "b" * env "c" + -1 * env "a" * env "d")⁻¹ * Φ "I2" w := by
      funext w
      simp [pfPowerWeighted, eval, recEnv, toInt?_neg_one]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [pfPowerWeighted, eval, toInt?_neg_one, hm, hn]
    field_simp
    ring

theorem pfPowerWeighted_real : pfPowerWeighted.Holds .real := pfPowerWeighted_holds Interp.real

theorem pfPowerWeighted_complex : pfPowerWeighted.Holds .complex := pfPowerWeighted_holds Interp.complex

/-- `sin u cos u = sin(2 u)/2` proves `sinCosDouble`. -/
theorem sinCosDouble_holds (I : Interp 𝕜) (h2 : (2 : 𝕜) ≠ 0)
    (hS : ∀ b c d w : 𝕜, b * I.sin (2 * c + 2 * d * w) * 2⁻¹ =
      b * I.sin (c + d * w) * I.cos (c + d * w)) :
    AntiderivRecHolds I "x" sinCosDouble.conditions sinCosDouble.body sinCosDouble.result
      sinCosDouble.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [sinCosDouble, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [sinCosDouble, Defined, eval, toInt?_neg_one, hS, h2] at hw ⊢
    exact hw
  · exact Eventually.of_forall fun _ => by simp [sinCosDouble, Defined]
  · simp only [sinCosDouble, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval I (recEnv env (sinCosDouble.integrals.map (·.1)) Φ "x" w)
        sinCosDouble.result) = Φ "I1" := by
      funext w
      simp [sinCosDouble, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [sinCosDouble, eval, toInt?_neg_one, hS]

theorem sinCosDouble_real : sinCosDouble.Holds .real := by
  refine sinCosDouble_holds Interp.real two_ne_zero fun b c d w => ?_
  simp only [Interp.real]
  rw [show 2 * c + 2 * d * w = 2 * (c + d * w) by ring, Real.sin_two_mul]
  ring

theorem sinCosDouble_complex : sinCosDouble.Holds .complex := by
  refine sinCosDouble_holds Interp.complex two_ne_zero fun b c d w => ?_
  simp only [Interp.complex]
  rw [show 2 * c + 2 * d * w = 2 * (c + d * w) by ring, Complex.sin_two_mul]
  ring

/-- A linear antiderivative `w ↦ w * C` for refutations with two residual
integrals. -/
private theorem two_linear (C1 C2 t : 𝕜) :
    HasDerivAt ((fun h w => if h = "I1" then w * C1 else w * C2) "I1") C1 t ∧
      HasDerivAt ((fun h w => if h = "I1" then w * C1 else w * C2) "I2") C2 t := by
  exact ⟨by simpa using hasDerivAt_mul_const C1, by simpa using hasDerivAt_mul_const C2⟩

/-- **Counterexample** to `pfGeneral`: at `a = c = 1` and the other
metavariables `0` the integrand is defined everywhere, but `b c - a d = 0`. -/
theorem pfGeneral_not (I : Interp 𝕜) :
    ¬ AntiderivRecHolds I "x" pfGeneral.conditions pfGeneral.body pfGeneral.result
      pfGeneral.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" then 1 else 0) 0
    (by simp [pfGeneral]) (Eventually.of_forall fun _ => ?_)
    (fun h w => if h = "I1" then w * eval I (Function.update
        (fun s => if s = "a" ∨ s = "c" then 1 else 0) "x" 0) (mul (.int 1) (inv binA))
      else w * eval I (Function.update (fun s => if s = "a" ∨ s = "c" then 1 else 0) "x" 0)
        (mul (.int 1) (inv binB))) ?_ ?_
  · simp [pfGeneral, Defined, eval, toInt?_zero, toInt?_neg_one]
  · simp only [pfGeneral, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    exact two_linear _ _ _
  · intro h
    simp only [pfGeneral, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem pfGeneral_counterexample_real : ¬ pfGeneral.Holds .real := pfGeneral_not Interp.real

theorem pfGeneral_counterexample_complex : ¬ pfGeneral.Holds .complex :=
  pfGeneral_not Interp.complex

/-- **Counterexample** to `linOverLin`: at `a = 1` and the other
metavariables `0` the integrand is defined everywhere, but `b^(-1)` is not. -/
theorem linOverLin_not (I : Interp 𝕜) :
    ¬ AntiderivRecHolds I "x" linOverLin.conditions linOverLin.body linOverLin.result
      linOverLin.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "a" then 1 else 0) 0
    (by simp [linOverLin]) (Eventually.of_forall fun _ => ?_)
    (fun h w => if h = "I1" then w * eval I (Function.update
        (fun s => if s = "a" then 1 else 0) "x" 0) twoPow
      else w * eval I (Function.update (fun s => if s = "a" then 1 else 0) "x" 0)
        (mul twoPow (inv (add (v "a") (mul (v "b") x))))) ?_ ?_
  · simp [linOverLin, Defined, eval, toInt?_zero, toInt?_neg_one]
  · simp only [linOverLin, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    exact two_linear _ _ _
  · intro h
    simp only [linOverLin, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem linOverLin_counterexample_real : ¬ linOverLin.Holds .real := linOverLin_not Interp.real

theorem linOverLin_counterexample_complex : ¬ linOverLin.Holds .complex :=
  linOverLin_not Interp.complex

/-- **Counterexample** to `sinTrinomSq`: at `b = 1` and `a = c = 0`,
`b^2 - 4 a c = 1 ≠ 0` and the integrand is defined everywhere, but the
residual integrand `sin((b + 2 c x)^2/(4 c))` is not. -/
theorem sinTrinomSq_not (I : Interp 𝕜) :
    ¬ AntiderivRecHolds I "x" sinTrinomSq.conditions sinTrinomSq.body sinTrinomSq.result
      sinTrinomSq.integrals := by
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" then 1 else 0) 0
    (by simp [sinTrinomSq, Cond.Holds, Defined, eval, toInt?_two])
    (Eventually.of_forall fun _ => by simp [sinTrinomSq, Defined, eval, toInt?_two]) ?_
  refine ⟨_, List.mem_cons_self .., ?_⟩
  intro h
  simp only [Defined, eval, Interp.toInt?_cast] at h
  simp at h

theorem sinTrinomSq_counterexample_real : ¬ sinTrinomSq.Holds .real :=
  sinTrinomSq_not Interp.real

theorem sinTrinomSq_counterexample_complex : ¬ sinTrinomSq.Holds .complex :=
  sinTrinomSq_not Interp.complex

/-- **Counterexample** to `cosTrinomSq`, as for `sinTrinomSq`. -/
theorem cosTrinomSq_not (I : Interp 𝕜) :
    ¬ AntiderivRecHolds I "x" cosTrinomSq.conditions cosTrinomSq.body cosTrinomSq.result
      cosTrinomSq.integrals := by
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" then 1 else 0) 0
    (by simp [cosTrinomSq, Cond.Holds, Defined, eval, toInt?_two])
    (Eventually.of_forall fun _ => by simp [cosTrinomSq, Defined, eval, toInt?_two]) ?_
  refine ⟨_, List.mem_cons_self .., ?_⟩
  intro h
  simp only [Defined, eval, Interp.toInt?_cast] at h
  simp at h

theorem cosTrinomSq_counterexample_real : ¬ cosTrinomSq.Holds .real :=
  cosTrinomSq_not Interp.real

theorem cosTrinomSq_counterexample_complex : ¬ cosTrinomSq.Holds .complex :=
  cosTrinomSq_not Interp.complex

private theorem toInt?_one' (I : Interp 𝕜) : I.toInt? (1 : 𝕜) = some 1 :=
  (I.toInt?_eq _ _).2 (by simp)

/-- **Counterexample** to `binomRatio`, for an interpretation in which
`-1 < 0`: at `b = c = 1`, `n = -1` and `a = d = 0` the conditions hold and the
integrand is defined near `1`, but `a^(-1)` is not. -/
theorem binomRatio_not (I : Interp 𝕜) (hlt : I.lt (-1) 0) :
    ¬ AntiderivRecHolds I "x" binomRatio.conditions binomRatio.body binomRatio.result
      binomRatio.integrals := by
  refine not_antiderivRecHolds_result
    (fun s => if s = "b" ∨ s = "c" then 1 else if s = "n" then -1 else 0) 1
    (by simp [binomRatio, Cond.Holds, Defined, eval, hlt]) ?_
    (fun _ w => w * eval I (Function.update
      (fun s => if s = "b" ∨ s = "c" then 1 else if s = "n" then -1 else 0) "x" 1)
      (binomRatio.integrals.head!.2)) ?_ ?_
  · filter_upwards [eventually_ne_nhds (one_ne_zero (α := 𝕜))] with w hw
    simp [binomRatio, Defined, eval, toInt?_neg_one, hw]
  · simp only [binomRatio, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [binomRatio, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem binomRatio_counterexample_real : ¬ binomRatio.Holds .real :=
  binomRatio_not Interp.real (show (-1 : ℝ) < 0 by norm_num)

theorem binomRatio_counterexample_complex : ¬ binomRatio.Holds .complex :=
  binomRatio_not Interp.complex (by simp [Interp.complex])

/-- **Counterexample** to `logLogWeighted`, for an interpretation with `ln`
defined at `1` and `ln 1 = 0`: at `c = d = 1` and the other metavariables `0`
the integrand is defined everywhere, but the residual integrand
`(e x)^m/log(d x^n)` is not. -/
theorem logLogWeighted_not (I : Interp 𝕜) (h1 : I.lnDefined 1) (h0 : I.ln 1 = 0) :
    ¬ AntiderivRecHolds I "x" logLogWeighted.conditions logLogWeighted.body
      logLogWeighted.result logLogWeighted.integrals := by
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" ∨ s = "d" then 1 else 0) 1
    (by simp [logLogWeighted, Cond.Holds, Defined, eval])
    (Eventually.of_forall fun _ => ?_) ?_
  · simp [logLogWeighted, Defined, eval, toInt?_zero, h1]
  · simp only [logLogWeighted, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]
    intro h
    simp only [Defined, eval, Interp.toInt?_cast] at h
    simp [toInt?_zero, h0] at h

theorem logLogWeighted_counterexample_real : ¬ logLogWeighted.Holds .real :=
  logLogWeighted_not Interp.real (show (0 : ℝ) < 1 from one_pos) Real.log_one

theorem logLogWeighted_counterexample_complex : ¬ logLogWeighted.Holds .complex :=
  logLogWeighted_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero) Complex.log_one

/-- **Counterexample** to `linTwoPow`, in an interpretation where `2 ≠ 0`: at
`c = 1` and the other metavariables `0`, `n + p + 2 = 2 ≠ 0` and the integrand
is defined everywhere, but `(d f (n + p + 2))^(-1)` is not. -/
theorem linTwoPow_not (I : Interp 𝕜) (h2 : (2 : 𝕜) ≠ 0) :
    ¬ AntiderivRecHolds I "x" linTwoPow.conditions linTwoPow.body linTwoPow.result
      linTwoPow.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "c" then 1 else 0) 0
    (by simp [linTwoPow, Cond.Holds, Defined, eval, h2]) (Eventually.of_forall fun _ => ?_)
    (fun _ w => w * eval I (Function.update (fun s => if s = "c" then 1 else 0) "x" 0) twoPow)
    ?_ ?_
  · simp [linTwoPow, Defined, eval, toInt?_zero]
  · simp only [linTwoPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [linTwoPow, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem linTwoPow_counterexample_real : ¬ linTwoPow.Holds .real :=
  linTwoPow_not Interp.real two_ne_zero

theorem linTwoPow_counterexample_complex : ¬ linTwoPow.Holds .complex :=
  linTwoPow_not Interp.complex two_ne_zero

/-- **Counterexample** to `logBinWeighted`, for an interpretation with `ln`
defined at `1`: at `c = 1` and the other metavariables `0` the integrand
`log 1` is defined everywhere, but the residual integrand
`x^(n-1) (f x)^(m+1)/(d + e x^n)` is not. -/
theorem logBinWeighted_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" logBinWeighted.conditions logBinWeighted.body
      logBinWeighted.result logBinWeighted.integrals := by
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" then 1 else 0) 1
    (by simp [logBinWeighted, Cond.Holds, Defined, eval])
    (Eventually.of_forall fun _ => ?_) ?_
  · simp [logBinWeighted, Defined, eval, toInt?_zero, h1]
  · simp only [logBinWeighted, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]
    intro h
    simp only [Defined, eval, Interp.toInt?_cast] at h
    simp [toInt?_zero] at h

theorem logBinWeighted_counterexample_real : ¬ logBinWeighted.Holds .real :=
  logBinWeighted_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem logBinWeighted_counterexample_complex : ¬ logBinWeighted.Holds .complex :=
  logBinWeighted_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

end Proofs

/-- Integration by parts reduces `(a + b log(c x^n))^p` over ℝ, for every
integer `p > 0` (the fragment interprets `arith1#power` for integer exponents
only). -/
theorem logLinPow_real : logLinPow.Holds .real := by
  show AntiderivRecHolds Interp.real "x" logLinPow.conditions logLinPow.body logLinPow.result
    logLinPow.integrals
  intro env hc t hF
  have hp0 : 0 < env "p" := by
    have h := hc (.gt (v "p") (.int 0)) (by simp [logLinPow])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hk : intValue? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [logLinPow, Defined, eval, Interp.real, hk] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [logLinPow, Defined, eval, Interp.real, hkn] at h
  have hpk : env "p" = p := (intValue?_eq _ _).1 hk
  have hnk : env "n" = n := (intValue?_eq _ _).1 hkn
  have hp1 : 1 ≤ p := by
    have : (0 : ℝ) < p := hpk ▸ hp0
    exact_mod_cast this
  have hkm : intValue? (env "p" + -1) = some (p - 1) := by
    rw [intValue?_eq, hpk]; push_cast; ring
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) logLinPow.body ↔
      (n < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ n := by
    intro w
    have : ¬ p < 0 := by omega
    simp [logLinPow, Defined, eval, Interp.real, hk, hkn, this]
  have hpos := ((hD t).1 hF.self_of_nhds).2
  have hn0 := ((hD t).1 hF.self_of_nhds).1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [logLinPow, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := (hD w).1 hw
    have : ¬ p - 1 < 0 := by omega
    simp [Defined, eval, Interp.real, hkn, hkm, this]
    exact h
  · filter_upwards [hF] with w hw
    have h := (hD w).1 hw
    have : ¬ p < 0 := by omega
    simp [logLinPow, Defined, eval, Interp.real, recEnv, hk, hkn, this]
    exact h
  · simp only [logLinPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hne : t ≠ 0 ∨ 0 ≤ n := by
      by_cases h : n < 0
      · exact Or.inl (hn0 h)
      · exact Or.inr (by omega)
    have hA := ((((hasDerivAt_zpow n t hne).const_mul (env "c")).log hpos.ne').const_mul
      (env "b")).const_add (env "a")
    have hAp := (hasDerivAt_zpow p _ (Or.inr (by omega))).comp t hA
    have h := ((hasDerivAt_id' t).mul hAp).add (hΦ.const_mul (-1 * env "b" * env "n" * env "p"))
    have hfun : (fun w => eval Interp.real (recEnv env (logLinPow.integrals.map (·.1)) Φ "x" w)
        logLinPow.result) = fun w =>
          w * ((fun y => y ^ p) ∘ fun w => env "a" + env "b" * Real.log (env "c" * w ^ n)) w +
            -1 * env "b" * env "n" * env "p" * Φ "I1" w := by
      funext w
      simp [logLinPow, eval, Interp.real, recEnv, hk, hkn]
    have hval : eval Interp.real (Function.update env "x" t) logLinPow.body =
        (env "a" + env "b" * Real.log (env "c" * t ^ n)) ^ p := by
      simp [logLinPow, eval, Interp.real, hk, hkn]
    rw [hfun, hval]
    refine h.congr_deriv ?_
    simp only [Function.comp, eval, Interp.real, Function.update_self, Function.update_apply]
    simp [hkn, hkm]
    rw [hnk, hpk]
    rcases eq_or_ne n 0 with rfl | hn1
    · simp
    · have ht : t ≠ 0 := by
        rcases hne with h | h
        · exact h
        · intro h0
          subst h0
          rw [zero_zpow n hn1, mul_zero] at hpos
          exact lt_irrefl 0 hpos
      have hc : env "c" ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hpos
        exact lt_irrefl 0 hpos
      have hz : t ^ n ≠ 0 := zpow_ne_zero n ht
      rw [zpow_sub_one₀ ht]
      field_simp
      ring

end OSR.IntegrationRec
