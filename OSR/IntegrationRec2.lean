import OSR.IntegrationRec

/-!
# Integration (RUBI): fourth batch of rules with residual integrals

The rule declarations are generated from the converted v0.1 rules by a
transcription tool and checked by the Integration repository's
`scripts/v1_faithfulness.py`, which compares the exported OpenMath objects
with the v0.1 rules.  Most of these rules are refuted: their conditions leave
free to vanish a coefficient that the result divides by, or let a residual
integrand divide by zero.  The refutations follow one template (an
assignment, a point, and either an undefined result or an undefined residual
integrand); `set_option linter.unusedSimpArgs false` lets that template pass
one simp set to all of them.
-/

set_option linter.unusedSimpArgs false

namespace OSR.IntegrationRec2

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- integration.power_binomial_times_linear -/
def binomPowLin : CRule where
  id := "integration.power_binomial_times_linear"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))))) (.pow (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)) (.int 0)]
  priority := 480
  description := "integration.power_binomial_times_linear"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:24" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#24"

/-- integration.log_power_over_linear_square -/
def logPowOverSq : CRule where
  id := "integration.log_power_over_linear_square"; legacyId := some "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.var "d") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "n", "p"]
  conditions := [.gt (.var "p") (.int 0)]
  priority := 490
  description := "integration.log_power_over_linear_square"
  provenance := migrated "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:5" "3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p.m#5"

/-- integration.power_log_ratio -/
def powLogRatio : CRule where
  id := "integration.power_log_ratio"; legacyId := some "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n"))))))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "A", "B", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.var "m") (.int (-1)),
    .ne (.var "m") (.int (-2))]
  priority := 500
  description := "integration.power_log_ratio"
  provenance := migrated "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:13" "3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.m#13"

/-- integration.power_log_product -/
def powLogProduct : CRule where
  id := "integration.power_log_product"; legacyId := some "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r"))))) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "p")) (.var "r")) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "q")) (.var "r")) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "p", "q", "r"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 510
  description := "integration.power_log_product"
  provenance := migrated "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:4" "3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m#4"

/-- integration.power_log_product_power -/
def powLogProductPow : CRule where
  id := "integration.power_log_product_power"; legacyId := some "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.var "s")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.var "s"))) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "p")) (.var "r")) (.var "s")) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "q")) (.var "r")) (.var "s")) (.pow (.app2 .mul (.var "h") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.app2 .add (.var "s") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.app2 .add (.var "s") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "p", "q", "r", "s"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .int (.var "s"),
    .gt (.var "s") (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 520
  description := "integration.power_log_product_power"
  provenance := migrated "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:7" "3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m#7"

/-- integration.linear_power_log_linear -/
def linPowLogLin : CRule where
  id := "integration.linear_power_log_linear"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "n", "q"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int 0),
    .ne (.var "q") (.int (-1))]
  priority := 530
  description := "integration.linear_power_log_linear"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:7" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#7"

/-- integration.power_log_monomial_log_linear -/
def powLogLogLin : CRule where
  id := "integration.power_log_monomial_log_linear"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "q")) (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m"))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .add (.app2 .mul (.app2 .mul (.var "m") (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "q") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "q") (.int 1)))) (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m"))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "m")) (.var "n")) (.pow (.app2 .mul (.var "g") (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "q") (.int 1))) (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m"))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "q"]
  conditions := [.ne (.var "q") (.int (-1))]
  priority := 540
  description := "integration.power_log_monomial_log_linear"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:30" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#30"

/-- integration.log_monomial_log_linear_over_x -/
def logLogLinOverX : CRule where
  id := "integration.log_monomial_log_linear_over_x"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.int 2)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.app2 .mul (.int 2) (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.pow (.app2 .mul (.int 2) (.var "m")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.int 2)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  priority := 550
  description := "integration.log_monomial_log_linear_over_x"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:29" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#29"

/-- integration.log_power_log_binomial_over_x -/
def logPowLogBinOverX : CRule where
  id := "integration.log_power_log_binomial_over_x"; legacyId := some "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "q")))) (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "p"))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "q")))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "p"))))))) (.pow (.app2 .mul (.var "q") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "q") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "q")))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p", "q"]
  conditions := [.ne (.var "m") (.int (-1))]
  priority := 560
  description := "integration.log_power_log_binomial_over_x"
  provenance := migrated "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:27" "3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p.m#27"

/-- integration.power_two_log_linear -/
def powTwoLogLin : CRule where
  id := "integration.power_two_log_linear"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:39"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "n")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "f")) (.app2 .mul (.var "a") (.var "g"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "g")) (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "n", "m"]
  conditions := [.ne (.var "m") (.int (-1))]
  priority := 570
  description := "integration.power_two_log_linear"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:39" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#39"

/-- integration.two_log_linear -/
def twoLogLin : CRule where
  id := "integration.two_log_linear"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:34"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "n")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "f")) (.app2 .mul (.var "a") (.var "g"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "g")) (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "n"]
  priority := 580
  description := "integration.two_log_linear"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:34" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#34"

/-- integration.two_log_linear_over_x -/
def twoLogLinOverX : CRule where
  id := "integration.two_log_linear_over_x"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:38"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.var "x")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "n")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app1 .ln (.var "x")) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "f")) (.app2 .mul (.var "a") (.var "g"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "g")) (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "n"]
  priority := 590
  description := "integration.two_log_linear_over_x"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:38" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#38"

/-- integration.log_monomial_log_linear -/
def logMonoLogLin : CRule where
  id := "integration.log_monomial_log_linear"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m"))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "m")) (.var "n")) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.var "x") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m"))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  priority := 600
  description := "integration.log_monomial_log_linear"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:27" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#27"

/-- integration.log_product_power -/
def logProductPow : CRule where
  id := "integration.log_product_power"; legacyId := some "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:2"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.var "s"))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.var "s"))) (.pow (.var "b") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "r")) (.var "s")) (.app2 .add (.var "p") (.var "q"))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "q") (.var "r")) (.var "s")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.app2 .add (.var "s") (.app2 .mul (.int (-1)) (.int 1))))),
    ("I2", (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.app2 .add (.var "s") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "q", "r", "s"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.var "p") (.var "q")) (.int 0),
    .int (.var "s"),
    .gt (.var "s") (.int 0),
    .gt (.int 4) (.var "s")]
  priority := 610
  description := "integration.log_product_power"
  provenance := migrated "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:2" "3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m#2"

/-- integration.log_product_over_linear -/
def logProductOverLin : CRule where
  id := "integration.log_product_over_linear"; legacyId := some "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x")))) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r"))))) (.pow (.var "h") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "p")) (.var "r")) (.pow (.var "h") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "q")) (.var "r")) (.pow (.var "h") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .ln (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "p", "q", "r"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 620
  description := "integration.log_product_over_linear"
  provenance := migrated "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:3" "3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m#3"

/-- integration.log_square_product_over_linear -/
def logSqProductOverLin : CRule where
  id := "integration.log_square_product_over_linear"; legacyId := some "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.int 2)) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x")))) (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.int 2))) (.pow (.var "h") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "b")) (.var "p")) (.var "r")) (.pow (.var "h") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "d")) (.var "q")) (.var "r")) (.pow (.var "h") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x")))) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x")))) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r"))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "p", "q", "r"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 630
  description := "integration.log_square_product_over_linear"
  provenance := migrated "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:6" "3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m#6"

/-- integration.log_ratio_over_linear -/
def logRatioOverLin : CRule where
  id := "integration.log_ratio_over_linear"; legacyId := some "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n"))))))) (.pow (.var "g") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B")) (.var "n")) (.pow (.var "g") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "B") (.var "d")) (.var "n")) (.pow (.var "g") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "A", "B", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 640
  description := "integration.log_ratio_over_linear"
  provenance := migrated "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:11" "3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.m#11"

/-- integration.log_linear_over_linear -/
def logLinOverLin : CRule where
  id := "integration.log_linear_over_linear"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int (-1))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.var "g") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.pow (.var "g") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int (-1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int 0)]
  priority := 650
  description := "integration.log_linear_over_linear"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:6" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#6"

/-- integration.log_linear_power_over_linear -/
def logLinPowOverLin : CRule where
  id := "integration.log_linear_power_over_linear"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p")) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int (-1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))) (.pow (.var "g") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.var "p")) (.pow (.var "g") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int (-1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 1)]
  priority := 660
  description := "integration.log_linear_power_over_linear"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:8" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#8"

/-- integration.power_tan_square -/
def powTanSq : CRule where
  id := "integration.power_tan_square"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.11 (e x)^m (a+b tan(c+d x^n))^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))) (.int 2)))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.app2 .mul (.int (-1)) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.var "x") (.var "m"))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "m", "n"]
  priority := 670
  description := "integration.power_tan_square"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.11 (e x)^m (a+b tan(c+d x^n))^p:11" "4 Trig functions/4.3 Tangent/4.3.11 (e x)^m (a+b tan(c+d x^n))^p.m#11"

/-- integration.linear_tan_trinomial -/
def linTanTrinom : CRule where
  id := "integration.linear_tan_trinomial"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.12 (d+e x)^m tan(a+b x+c x^2)^n:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .tan (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app1 .ln (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app1 .tan (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)]
  priority := 680
  description := "integration.linear_tan_trinomial"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.12 (d+e x)^m tan(a+b x+c x^2)^n:5" "4 Trig functions/4.3 Tangent/4.3.12 (d+e x)^m tan(a+b x+c x^2)^n.m#5"

/-- integration.two_linear_factors_times_powers -/
def linFour : CRule where
  id := "integration.two_linear_factors_times_powers"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "d") (.int 2))) (.var "f")) (.var "h")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))))) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "m") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2)) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)) (.int 0)]
  priority := 690
  description := "integration.two_linear_factors_times_powers"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:6" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#6"

/-- Split f + g log(h (i + j x)^m) under the integral -/
def splitLogLog : CRule where
  id := "integration.split_log_linear_factor"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:44"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "i") (.app2 .mul (.var "j") (.var "x"))) (.var "m"))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "f") (.var "I1")) (.app2 .mul (.var "g") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "i") (.app2 .mul (.var "j") (.var "x"))) (.var "m")))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "e") (.var "i")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "j"))) (.int 0)]
  priority := 700
  description := "Split f + g log(h (i + j x)^m) under the integral"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:44" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#44"

/-- Split log(c (d + e x)) for c d > 0 -/
def logLinOverX : CRule where
  id := "integration.log_linear_over_x_split"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.var "d"))))) (.app1 .ln (.var "x"))) (.app2 .mul (.var "b") (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.var "d") (.int (-1)))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.gt (.app2 .mul (.var "c") (.var "d")) (.int 0)]
  priority := 720
  description := "Split log(c (d + e x)) for c d > 0"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:4" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#4"

/-- Antiderivative of (a + b log(c x))/(d + e x) -/
def logOverLin : CRule where
  id := "integration.log_over_linear"; legacyId := some "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.var "x"))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.pow (.var "e") (.int (-1))))))) (.app1 .ln (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.var "e") (.int (-1)))) (.app2 .mul (.var "b") (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "x")) (.pow (.var "d") (.int (-1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.gt (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.pow (.var "e") (.int (-1)))) (.int 0)]
  priority := 730
  description := "Antiderivative of (a + b log(c x))/(d + e x)"
  provenance := migrated "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:3" "3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p.m#3"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_zero (I : Interp 𝕜) : I.toInt? (0 : 𝕜) = some 0 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_one (I : Interp 𝕜) : I.toInt? (1 : 𝕜) = some 1 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem two_linear (C1 C2 t : 𝕜) :
    HasDerivAt ((fun h w => if h = "I1" then w * C1 else w * C2) "I1") C1 t ∧
      HasDerivAt ((fun h w => if h = "I1" then w * C1 else w * C2) "I2") C2 t :=
  ⟨by simpa using hasDerivAt_mul_const C1, by simpa using hasDerivAt_mul_const C2⟩

/-- **Counterexample** to `binomPowLin`: at a = d = e = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but (b e (m + n (p + 1) + 1))^(-1) is not. -/
theorem binomPowLin_not (I : Interp 𝕜)  :
    ¬ AntiderivRecHolds I "x" binomPowLin.conditions binomPowLin.body binomPowLin.result binomPowLin.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "e" then 1 else 0) 0 (by simp [binomPowLin, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one]) (Eventually.of_forall fun _ => by simp [binomPowLin, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one])
    (fun _ w => w * eval I (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "e" then 1 else 0) "x" 0) (binomPowLin.integrals.head!.2)) ?_ ?_
  · simp only [binomPowLin, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [binomPowLin, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one] at h

theorem binomPowLin_counterexample_real : ¬ binomPowLin.Holds .real :=
  binomPowLin_not Interp.real 

theorem binomPowLin_counterexample_complex : ¬ binomPowLin.Holds .complex :=
  binomPowLin_not Interp.complex 

/-- **Counterexample** to `logPowOverSq`: at c = e = p = 1 and the other metavariables 0 the condition p > 0 holds and the integrand is defined near x = 1, but (d (d + e x))^(-1) is not. -/
theorem logPowOverSq_not (I : Interp 𝕜) (h1 : I.lnDefined 1) (hlt01 : I.lt 0 1) :
    ¬ AntiderivRecHolds I "x" logPowOverSq.conditions logPowOverSq.body logPowOverSq.result logPowOverSq.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "p" then 1 else 0) 1 (by simp [logPowOverSq, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1, hlt01]) (by filter_upwards [eventually_ne_nhds (one_ne_zero (α := 𝕜))] with w hw; simp [logPowOverSq, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1, hw])
    (fun _ w => w * eval I (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "p" then 1 else 0) "x" 1) (logPowOverSq.integrals.head!.2)) ?_ ?_
  · simp only [logPowOverSq, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [logPowOverSq, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem logPowOverSq_counterexample_real : ¬ logPowOverSq.Holds .real :=
  logPowOverSq_not Interp.real (show (0 : ℝ) < 1 from one_pos) (show (0 : ℝ) < 1 from one_pos)

theorem logPowOverSq_counterexample_complex : ¬ logPowOverSq.Holds .complex :=
  logPowOverSq_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero) (by simp [Interp.complex])

/-- **Counterexample** to `powLogRatio`: at b = c = e = f = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but (g (m + 1))^(-1) is not. -/
theorem powLogRatio_not (I : Interp 𝕜) (h1 : I.lnDefined 1) (h2 : (2 : 𝕜) ≠ 0) :
    ¬ AntiderivRecHolds I "x" powLogRatio.conditions powLogRatio.body powLogRatio.result powLogRatio.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) 1 (by simp [powLogRatio, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1, h2]) (Eventually.of_forall fun _ => by simp [powLogRatio, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1])
    (fun _ w => w * eval I (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" 1) (powLogRatio.integrals.head!.2)) ?_ ?_
  · simp only [powLogRatio, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [powLogRatio, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem powLogRatio_counterexample_real : ¬ powLogRatio.Holds .real :=
  powLogRatio_not Interp.real (show (0 : ℝ) < 1 from one_pos) two_ne_zero

theorem powLogRatio_counterexample_complex : ¬ powLogRatio.Holds .complex :=
  powLogRatio_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero) two_ne_zero

/-- **Counterexample** to `powLogProduct`: at b = c = e = f = g = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but (h (m + 1))^(-1) is not. -/
theorem powLogProduct_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" powLogProduct.conditions powLogProduct.body powLogProduct.result powLogProduct.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" then 1 else 0) 1 (by simp [powLogProduct, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (Eventually.of_forall fun _ => by simp [powLogProduct, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1])
    (fun h w => if h = "I1" then w * eval I (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" then 1 else 0) "x" 1) (powLogProduct.integrals.head!.2) else w * eval I (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" then 1 else 0) "x" 1) ((powLogProduct.integrals.drop 1).head!.2)) ?_ ?_
  · simp only [powLogProduct, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact two_linear _ _ _
  · intro h
    simp only [powLogProduct, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem powLogProduct_counterexample_real : ¬ powLogProduct.Holds .real :=
  powLogProduct_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem powLogProduct_counterexample_complex : ¬ powLogProduct.Holds .complex :=
  powLogProduct_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `powLogProductPow`: at b = c = e = f = g = s = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but (h (m + 1))^(-1) is not. -/
theorem powLogProductPow_not (I : Interp 𝕜) (h1 : I.lnDefined 1) (hlt01 : I.lt 0 1) :
    ¬ AntiderivRecHolds I "x" powLogProductPow.conditions powLogProductPow.body powLogProductPow.result powLogProductPow.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "s" then 1 else 0) 1 (by simp [powLogProductPow, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1, hlt01]) (Eventually.of_forall fun _ => by simp [powLogProductPow, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1])
    (fun h w => if h = "I1" then w * eval I (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "s" then 1 else 0) "x" 1) (powLogProductPow.integrals.head!.2) else w * eval I (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "s" then 1 else 0) "x" 1) ((powLogProductPow.integrals.drop 1).head!.2)) ?_ ?_
  · simp only [powLogProductPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact two_linear _ _ _
  · intro h
    simp only [powLogProductPow, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem powLogProductPow_counterexample_real : ¬ powLogProductPow.Holds .real :=
  powLogProductPow_not Interp.real (show (0 : ℝ) < 1 from one_pos) (show (0 : ℝ) < 1 from one_pos)

theorem powLogProductPow_counterexample_complex : ¬ powLogProductPow.Holds .complex :=
  powLogProductPow_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero) (by simp [Interp.complex])

/-- **Counterexample** to `linPowLogLin`: at c = e = f = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but (g (q + 1))^(-1) is not. -/
theorem linPowLogLin_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" linPowLogLin.conditions linPowLogLin.body linPowLogLin.result linPowLogLin.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) 1 (by simp [linPowLogLin, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (Eventually.of_forall fun _ => by simp [linPowLogLin, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1])
    (fun _ w => w * eval I (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" 1) (linPowLogLin.integrals.head!.2)) ?_ ?_
  · simp only [linPowLogLin, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [linPowLogLin, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem linPowLogLin_counterexample_real : ¬ linPowLogLin.Holds .real :=
  linPowLogLin_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem linPowLogLin_counterexample_complex : ¬ linPowLogLin.Holds .complex :=
  linPowLogLin_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `powLogLogLin`: at c = f = 1 and the other metavariables 0 the condition q ≠ -1 holds and the integrand is defined everywhere, but (g (q + 1))^(-1) is not. -/
theorem powLogLogLin_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" powLogLogLin.conditions powLogLogLin.body powLogLogLin.result powLogLogLin.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "f" then 1 else 0) 1 (by simp [powLogLogLin, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (Eventually.of_forall fun _ => by simp [powLogLogLin, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1])
    (fun h w => if h = "I1" then w * eval I (Function.update (fun s => if s = "c" ∨ s = "f" then 1 else 0) "x" 1) (powLogLogLin.integrals.head!.2) else w * eval I (Function.update (fun s => if s = "c" ∨ s = "f" then 1 else 0) "x" 1) ((powLogLogLin.integrals.drop 1).head!.2)) ?_ ?_
  · simp only [powLogLogLin, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact two_linear _ _ _
  · intro h
    simp only [powLogLogLin, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem powLogLogLin_counterexample_real : ¬ powLogLogLin.Holds .real :=
  powLogLogLin_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem powLogLogLin_counterexample_complex : ¬ powLogLogLin.Holds .complex :=
  powLogLogLin_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `logLogLinOverX`: at c = f = 1 and the other metavariables 0 the integrand is defined near x = 1, but (2 m)^(-1) is not. -/
theorem logLogLinOverX_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" logLogLinOverX.conditions logLogLinOverX.body logLogLinOverX.result logLogLinOverX.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "f" then 1 else 0) 1 (by simp [logLogLinOverX, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (by filter_upwards [eventually_ne_nhds (one_ne_zero (α := 𝕜))] with w hw; simp [logLogLinOverX, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1, hw])
    (fun _ w => w * eval I (Function.update (fun s => if s = "c" ∨ s = "f" then 1 else 0) "x" 1) (logLogLinOverX.integrals.head!.2)) ?_ ?_
  · simp only [logLogLinOverX, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [logLogLinOverX, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem logLogLinOverX_counterexample_real : ¬ logLogLinOverX.Holds .real :=
  logLogLinOverX_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem logLogLinOverX_counterexample_complex : ¬ logLogLinOverX.Holds .complex :=
  logLogLinOverX_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `logPowLogBinOverX`: at c = f = 1 and the other metavariables 0 the condition m ≠ -1 holds and the integrand is defined near x = 1, but (q (m + 1))^(-1) is not. -/
theorem logPowLogBinOverX_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" logPowLogBinOverX.conditions logPowLogBinOverX.body logPowLogBinOverX.result logPowLogBinOverX.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "f" then 1 else 0) 1 (by simp [logPowLogBinOverX, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (by filter_upwards [eventually_ne_nhds (one_ne_zero (α := 𝕜))] with w hw; simp [logPowLogBinOverX, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1, hw])
    (fun _ w => w * eval I (Function.update (fun s => if s = "c" ∨ s = "f" then 1 else 0) "x" 1) (logPowLogBinOverX.integrals.head!.2)) ?_ ?_
  · simp only [logPowLogBinOverX, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [logPowLogBinOverX, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem logPowLogBinOverX_counterexample_real : ¬ logPowLogBinOverX.Holds .real :=
  logPowLogBinOverX_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem logPowLogBinOverX_counterexample_complex : ¬ logPowLogBinOverX.Holds .complex :=
  logPowLogBinOverX_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `powTwoLogLin`: at c = e = 1 and the other metavariables 0 the integrand is defined everywhere, but the residual integrand, which divides by d + e x, is not defined at x = 0. -/
theorem powTwoLogLin_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" powTwoLogLin.conditions powTwoLogLin.body powTwoLogLin.result powTwoLogLin.integrals := by
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" ∨ s = "e" then 1 else 0) 0 (by simp [powTwoLogLin, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (Eventually.of_forall fun _ => by simp [powTwoLogLin, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) ?_
  simp only [powTwoLogLin, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  intro h
  simp only [Defined, eval, Interp.toInt?_cast] at h
  simp [toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem powTwoLogLin_counterexample_real : ¬ powTwoLogLin.Holds .real :=
  powTwoLogLin_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem powTwoLogLin_counterexample_complex : ¬ powTwoLogLin.Holds .complex :=
  powTwoLogLin_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `twoLogLin`: at c = e = 1 and the other metavariables 0 the integrand is defined everywhere, but the residual integrand, which divides by d + e x, is not defined at x = 0. -/
theorem twoLogLin_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" twoLogLin.conditions twoLogLin.body twoLogLin.result twoLogLin.integrals := by
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" ∨ s = "e" then 1 else 0) 0 (by simp [twoLogLin, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (Eventually.of_forall fun _ => by simp [twoLogLin, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) ?_
  simp only [twoLogLin, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  intro h
  simp only [Defined, eval, Interp.toInt?_cast] at h
  simp [toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem twoLogLin_counterexample_real : ¬ twoLogLin.Holds .real :=
  twoLogLin_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem twoLogLin_counterexample_complex : ¬ twoLogLin.Holds .complex :=
  twoLogLin_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `twoLogLinOverX`: at c = e = 1, d = -1 and the other metavariables 0 the integrand is defined near x = 1, but the residual integrand, which divides by d + e x, is not defined at x = 1. -/
theorem twoLogLinOverX_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" twoLogLinOverX.conditions twoLogLinOverX.body twoLogLinOverX.result twoLogLinOverX.integrals := by
  refine not_antiderivRecHolds_integrand (fun s => if s = "d" then -1 else if s = "c" ∨ s = "e" then 1 else 0) 1 (by simp [twoLogLinOverX, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (by filter_upwards [eventually_ne_nhds (one_ne_zero (α := 𝕜))] with w hw; simp [twoLogLinOverX, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1, hw]) ?_
  simp only [twoLogLinOverX, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  intro h
  simp only [Defined, eval, Interp.toInt?_cast] at h
  simp [toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem twoLogLinOverX_counterexample_real : ¬ twoLogLinOverX.Holds .real :=
  twoLogLinOverX_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem twoLogLinOverX_counterexample_complex : ¬ twoLogLinOverX.Holds .complex :=
  twoLogLinOverX_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `logMonoLogLin`: at c = e = f = 1, d = -1 and the other metavariables 0 the integrand is defined everywhere, but the residual integrand x/(d + e x) is not defined at x = 1. -/
theorem logMonoLogLin_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" logMonoLogLin.conditions logMonoLogLin.body logMonoLogLin.result logMonoLogLin.integrals := by
  refine not_antiderivRecHolds_integrand (fun s => if s = "d" then -1 else if s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) 1 (by simp [logMonoLogLin, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (Eventually.of_forall fun _ => by simp [logMonoLogLin, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) ?_
  simp only [logMonoLogLin, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  left
  intro h
  simp only [Defined, eval, Interp.toInt?_cast] at h
  simp [toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem logMonoLogLin_counterexample_real : ¬ logMonoLogLin.Holds .real :=
  logMonoLogLin_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem logMonoLogLin_counterexample_complex : ¬ logMonoLogLin.Holds .complex :=
  logMonoLogLin_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `logProductPow`: at a = d = e = f = p = s = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but b^(-1) is not. -/
theorem logProductPow_not (I : Interp 𝕜) (h1 : I.lnDefined 1) (hlt01 : I.lt 0 1) (hlt14 : I.lt 1 4) :
    ¬ AntiderivRecHolds I "x" logProductPow.conditions logProductPow.body logProductPow.result logProductPow.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "p" ∨ s = "s" then 1 else 0) 0 (by simp [logProductPow, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1, hlt01, hlt14]) (Eventually.of_forall fun _ => by simp [logProductPow, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1])
    (fun h w => if h = "I1" then w * eval I (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "p" ∨ s = "s" then 1 else 0) "x" 0) (logProductPow.integrals.head!.2) else w * eval I (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "p" ∨ s = "s" then 1 else 0) "x" 0) ((logProductPow.integrals.drop 1).head!.2)) ?_ ?_
  · simp only [logProductPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact two_linear _ _ _
  · intro h
    simp only [logProductPow, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem logProductPow_counterexample_real : ¬ logProductPow.Holds .real :=
  logProductPow_not Interp.real (show (0 : ℝ) < 1 from one_pos) (show (0 : ℝ) < 1 from one_pos) (show (1 : ℝ) < 4 by norm_num)

theorem logProductPow_counterexample_complex : ¬ logProductPow.Holds .complex :=
  logProductPow_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero) (by simp [Interp.complex]) (by simp [Interp.complex])

/-- **Counterexample** to `logProductOverLin`: at b = c = e = f = g = 1 and the other metavariables 0 the condition holds and the integrand is defined everywhere, but h^(-1) is not. -/
theorem logProductOverLin_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" logProductOverLin.conditions logProductOverLin.body logProductOverLin.result logProductOverLin.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" then 1 else 0) 1 (by simp [logProductOverLin, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (Eventually.of_forall fun _ => by simp [logProductOverLin, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1])
    (fun h w => if h = "I1" then w * eval I (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" then 1 else 0) "x" 1) (logProductOverLin.integrals.head!.2) else w * eval I (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" then 1 else 0) "x" 1) ((logProductOverLin.integrals.drop 1).head!.2)) ?_ ?_
  · simp only [logProductOverLin, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact two_linear _ _ _
  · intro h
    simp only [logProductOverLin, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem logProductOverLin_counterexample_real : ¬ logProductOverLin.Holds .real :=
  logProductOverLin_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem logProductOverLin_counterexample_complex : ¬ logProductOverLin.Holds .complex :=
  logProductOverLin_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `logSqProductOverLin`: at b = c = e = f = g = 1 and the other metavariables 0 the condition holds and the integrand is defined everywhere, but h^(-1) is not. -/
theorem logSqProductOverLin_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" logSqProductOverLin.conditions logSqProductOverLin.body logSqProductOverLin.result logSqProductOverLin.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" then 1 else 0) 1 (by simp [logSqProductOverLin, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (Eventually.of_forall fun _ => by simp [logSqProductOverLin, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1])
    (fun h w => if h = "I1" then w * eval I (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" then 1 else 0) "x" 1) (logSqProductOverLin.integrals.head!.2) else w * eval I (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" then 1 else 0) "x" 1) ((logSqProductOverLin.integrals.drop 1).head!.2)) ?_ ?_
  · simp only [logSqProductOverLin, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact two_linear _ _ _
  · intro h
    simp only [logSqProductOverLin, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem logSqProductOverLin_counterexample_real : ¬ logSqProductOverLin.Holds .real :=
  logSqProductOverLin_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem logSqProductOverLin_counterexample_complex : ¬ logSqProductOverLin.Holds .complex :=
  logSqProductOverLin_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `logRatioOverLin`: at b = c = e = f = 1 and the other metavariables 0 the condition holds and the integrand is defined everywhere, but g^(-1) is not. -/
theorem logRatioOverLin_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" logRatioOverLin.conditions logRatioOverLin.body logRatioOverLin.result logRatioOverLin.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) 1 (by simp [logRatioOverLin, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (Eventually.of_forall fun _ => by simp [logRatioOverLin, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1])
    (fun h w => if h = "I1" then w * eval I (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" 1) (logRatioOverLin.integrals.head!.2) else w * eval I (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" 1) ((logRatioOverLin.integrals.drop 1).head!.2)) ?_ ?_
  · simp only [logRatioOverLin, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact two_linear _ _ _
  · intro h
    simp only [logRatioOverLin, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem logRatioOverLin_counterexample_real : ¬ logRatioOverLin.Holds .real :=
  logRatioOverLin_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem logRatioOverLin_counterexample_complex : ¬ logRatioOverLin.Holds .complex :=
  logRatioOverLin_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `logLinOverLin`: at c = e = f = 1 and the other metavariables 0 the condition holds and the integrand is defined everywhere, but g^(-1) is not. -/
theorem logLinOverLin_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivRecHolds I "x" logLinOverLin.conditions logLinOverLin.body logLinOverLin.result logLinOverLin.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) 1 (by simp [logLinOverLin, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1]) (Eventually.of_forall fun _ => by simp [logLinOverLin, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1])
    (fun _ w => w * eval I (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" 1) (logLinOverLin.integrals.head!.2)) ?_ ?_
  · simp only [logLinOverLin, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [logLinOverLin, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem logLinOverLin_counterexample_real : ¬ logLinOverLin.Holds .real :=
  logLinOverLin_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem logLinOverLin_counterexample_complex : ¬ logLinOverLin.Holds .complex :=
  logLinOverLin_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to `logLinPowOverLin`: at c = e = f = 1, p = 2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but g^(-1) is not. -/
theorem logLinPowOverLin_not (I : Interp 𝕜) (h1 : I.lnDefined 1) (hlt12 : I.lt 1 2) :
    ¬ AntiderivRecHolds I "x" logLinPowOverLin.conditions logLinPowOverLin.body logLinPowOverLin.result logLinPowOverLin.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "f" then 1 else if s = "p" then 2 else 0) 1 (by simp [logLinPowOverLin, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1, hlt12]) (Eventually.of_forall fun _ => by simp [logLinPowOverLin, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1])
    (fun _ w => w * eval I (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "f" then 1 else if s = "p" then 2 else 0) "x" 1) (logLinPowOverLin.integrals.head!.2)) ?_ ?_
  · simp only [logLinPowOverLin, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [logLinPowOverLin, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h1] at h

theorem logLinPowOverLin_counterexample_real : ¬ logLinPowOverLin.Holds .real :=
  logLinPowOverLin_not Interp.real (show (0 : ℝ) < 1 from one_pos) (show (1 : ℝ) < 2 by norm_num)

theorem logLinPowOverLin_counterexample_complex : ¬ logLinPowOverLin.Holds .complex :=
  logLinPowOverLin_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero) (by simp [Interp.complex])

/-- **Counterexample** to `powTanSq`: at every metavariable 0 the integrand is defined everywhere, but (d n)^(-1) is not. -/
theorem powTanSq_not (I : Interp 𝕜) (htan : I.tanDefined 0) :
    ¬ AntiderivRecHolds I "x" powTanSq.conditions powTanSq.body powTanSq.result powTanSq.integrals := by
  refine not_antiderivRecHolds_result (fun s => 0) 0 (by simp [powTanSq, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, htan]) (Eventually.of_forall fun _ => by simp [powTanSq, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, htan])
    (fun h w => if h = "I1" then w * eval I (Function.update (fun s => 0) "x" 0) (powTanSq.integrals.head!.2) else w * eval I (Function.update (fun s => 0) "x" 0) ((powTanSq.integrals.drop 1).head!.2)) ?_ ?_
  · simp only [powTanSq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact two_linear _ _ _
  · intro h
    simp only [powTanSq, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, htan] at h

theorem powTanSq_counterexample_real : ¬ powTanSq.Holds .real :=
  powTanSq_not Interp.real (by simp [Interp.real])

theorem powTanSq_counterexample_complex : ¬ powTanSq.Holds .complex :=
  powTanSq_not Interp.complex (by simp [Interp.complex])

/-- **Counterexample** to `linTanTrinom`: at b = e = 1 and the other metavariables 0 the condition 2 c d - b e ≠ 0 holds and the integrand is defined near x = 0, but (2 c)^(-1) is not. -/
theorem linTanTrinom_not (I : Interp 𝕜) (hnear : ∀ᶠ w in 𝓝 (0 : 𝕜), I.tanDefined w) :
    ¬ AntiderivRecHolds I "x" linTanTrinom.conditions linTanTrinom.body linTanTrinom.result linTanTrinom.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" then 1 else 0) 0 (by simp [linTanTrinom, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one]) (by filter_upwards [hnear] with w hw; simpa [linTanTrinom, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one] using hw)
    (fun _ w => w * eval I (Function.update (fun s => if s = "b" ∨ s = "e" then 1 else 0) "x" 0) (linTanTrinom.integrals.head!.2)) ?_ ?_
  · simp only [linTanTrinom, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [linTanTrinom, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one] at h

theorem linTanTrinom_counterexample_real : ¬ linTanTrinom.Holds .real :=
  linTanTrinom_not Interp.real (by simpa [Interp.real] using Real.continuous_cos.continuousAt.eventually_ne (by simp : Real.cos 0 ≠ 0))

theorem linTanTrinom_counterexample_complex : ¬ linTanTrinom.Holds .complex :=
  linTanTrinom_not Interp.complex (by simpa [Interp.complex] using Complex.continuous_cos.continuousAt.eventually_ne (by simp : Complex.cos 0 ≠ 0))

/-- **Counterexample** to `linFour`: at every metavariable 0 the conditions m + n + 2 ≠ 0 and m + n + 3 ≠ 0 hold and the integrand is defined everywhere, but (b^2 d^2 (m + n + 2) (m + n + 3))^(-1) is not. -/
theorem linFour_not (I : Interp 𝕜) (h2 : (2 : 𝕜) ≠ 0) (h3 : (3 : 𝕜) ≠ 0) :
    ¬ AntiderivRecHolds I "x" linFour.conditions linFour.body linFour.result linFour.integrals := by
  refine not_antiderivRecHolds_result (fun s => 0) 0 (by simp [linFour, Cond.Holds, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one, h2, h3]) (Eventually.of_forall fun _ => by simp [linFour, Defined, eval, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one])
    (fun _ w => w * eval I (Function.update (fun s => 0) "x" 0) (linFour.integrals.head!.2)) ?_ ?_
  · simp only [linFour, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [linFour, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, toInt?_zero, toInt?_one, toInt?_two, toInt?_neg_one] at h

theorem linFour_counterexample_real : ¬ linFour.Holds .real :=
  linFour_not Interp.real two_ne_zero three_ne_zero

theorem linFour_counterexample_complex : ¬ linFour.Holds .complex :=
  linFour_not Interp.complex two_ne_zero three_ne_zero

/-- Linearity: `A (f + g L)/x = f (A/x) + g (L A/x)`. -/
theorem splitLogLog_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" splitLogLog.conditions splitLogLog.body splitLogLog.result
      splitLogLog.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [splitLogLog, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · filter_upwards [hF] with w hw
      simp only [splitLogLog, Defined] at hw ⊢
      exact ⟨hw.1.1, hw.2⟩
    · filter_upwards [hF] with w hw
      simp only [splitLogLog, Defined] at hw ⊢
      exact ⟨⟨hw.1.2.2.2, hw.1.1⟩, hw.2⟩
  · exact Eventually.of_forall fun _ => by simp [splitLogLog, Defined]
  · simp only [splitLogLog, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (splitLogLog.integrals.map (·.1)) Φ "x" w)
        splitLogLog.result) = fun w => env "f" * Φ "I1" w + env "g" * Φ "I2" w := by
      funext w
      simp [splitLogLog, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [splitLogLog, eval]
    ring

theorem splitLogLog_real : splitLogLog.Holds .real := splitLogLog_holds Interp.real

theorem splitLogLog_complex : splitLogLog.Holds .complex := splitLogLog_holds Interp.complex

end Proofs

/-- **Counterexample** to `logLinOverX` over ℝ: at `c = d = 1` and the other
metavariables `0`, `c d > 0` and the integrand is defined near `x = -1`, but
`log x` is not defined at `-1`. -/
theorem logLinOverX_counterexample_real : ¬ logLinOverX.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" logLinOverX.conditions logLinOverX.body
    logLinOverX.result logLinOverX.integrals
  have hm1 : intValue? (-1 : ℝ) = some (-1) := by simpa using intValue?_intCast (α := ℝ) (-1)
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" then 1 else 0) (-1)
    (by simp [logLinOverX, Cond.Holds, Defined, eval, Interp.real])
    (by filter_upwards [eventually_ne_nhds (show (-1 : ℝ) ≠ 0 by norm_num)] with w hw
        simp [logLinOverX, Defined, eval, Interp.real, hw, hm1])
    (fun _ w => w * eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" then 1 else 0)
      "x" (-1)) (logLinOverX.integrals.head!.2)) ?_ ?_
  · simp only [logLinOverX, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [logLinOverX, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, Interp.real] at h
    norm_num at h

/-- **Counterexample** to `logOverLin` over ℝ: at `c = d = 1`, `e = -1` and the
other metavariables `0`, `-c d/e = 1 > 0` and the integrand is defined near
`x = 2`, but `log(d + e x) = log(-1)` is not. -/
theorem logOverLin_counterexample_real : ¬ logOverLin.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" logOverLin.conditions logOverLin.body
    logOverLin.result logOverLin.integrals
  have hm1 : intValue? (-1 : ℝ) = some (-1) := by simpa using intValue?_intCast (α := ℝ) (-1)
  refine not_antiderivRecHolds_result
    (fun s => if s = "c" ∨ s = "d" then 1 else if s = "e" then -1 else 0) 2
    (by simp [logOverLin, Cond.Holds, Defined, eval, Interp.real, hm1])
    (by filter_upwards [lt_mem_nhds (show (1 : ℝ) < 2 by norm_num)] with w hw
        simp [logOverLin, Defined, eval, Interp.real, hm1]
        exact ⟨by linarith, fun h => by linarith⟩)
    (fun _ w => w * eval Interp.real (Function.update
      (fun s => if s = "c" ∨ s = "d" then 1 else if s = "e" then -1 else 0) "x" 2)
      (logOverLin.integrals.head!.2)) ?_ ?_
  · simp only [logOverLin, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [logOverLin, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv, Interp.real, hm1] at h

end OSR.IntegrationRec2
