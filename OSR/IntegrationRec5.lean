import OSR.IntegrationRec4

/-!
# Integration (RUBI): refutations found by a wider numerical search

The rules of this module were selected by a numerical search for
counterexamples under the real definedness semantics of the fragment: an
assignment satisfying the conditions, a point near which the integrand is
defined, at which the result or a residual integrand is not.  The search only
proposes; each refutation below is a Lean theorem, stated per domain.  The
rule declarations are transcribed by a tool and checked by the Integration
repository's `scripts/v1_faithfulness.py`.  Variables that RUBI constrains
by numeric predicates (`IntegerQ`, `GtQ`, …) but does not list in `FreeQ` are
declared independent of `x`, with an `independence:` finding.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec5

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.1.1.3 #14 -/
def rubi1113r14 : CRule where
  id := "integration.rubi_1_1_1_3_r14"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "f"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")) (.var "f"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "f")) (.var "x"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "p"]
  conditions := [.gt (.int (-1)) (.var "p")]
  priority := 1500
  description := "RUBI 1.1.1.3 #14"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:14" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#14"

/-- RUBI 1.1.1.4 #3 -/
def rubi1114r3 : CRule where
  id := "integration.rubi_1_1_1_4_r3"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "c")) (.var "d")) (.var "e")) (.var "g")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "c")) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2)))))) (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "d") (.int 2))) (.var "f")) (.var "h")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.pow (.var "d") (.int 2))) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "m") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2)))))) (.var "x"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "d") (.int 2))) (.var "f")) (.var "h")) (.app2 .add (.app2 .add (.int 2) (.app2 .mul (.int 3) (.var "n"))) (.pow (.var "n") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))))) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "h")) (.app2 .add (.app2 .add (.int 2) (.app2 .mul (.int 3) (.var "m"))) (.pow (.var "m") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.app2 .add (.app2 .add (.app2 .add (.int 6) (.pow (.var "m") (.int 2))) (.app2 .mul (.int 5) (.var "n"))) (.pow (.var "n") (.int 2))) (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.int 5))))))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "n"]
  conditions := [.gt (.int (-1)) (.var "m"),
    .gt (.int (-1)) (.var "n")]
  priority := 1510
  description := "RUBI 1.1.1.4 #3"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:3" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#3"

/-- RUBI 1.1.3.5 #24 -/
def rubi1135r24 : CRule where
  id := "integration.rubi_1_1_3_5_r24"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.pow (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 2))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.var "d")) (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "d") (.int 2))) (.var "e"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "c") (.int 2))) (.var "f"))) (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "q", "r"]
  conditions := [.gt (.int (-1)) (.var "q"),
    .gt (.var "r") (.int 1)]
  priority := 1520
  description := "RUBI 1.1.3.5 #24"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:24" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#24"

/-- RUBI 1.1.3.5 #26 -/
def rubi1135r26 : CRule where
  id := "integration.rubi_1_1_3_5_r26"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:26"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 2))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r"))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "r", "q"]
  conditions := [.gt (.int (-1)) (.var "q")]
  priority := 1530
  description := "RUBI 1.1.3.5 #26"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:26" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#26"

/-- RUBI 1.2.1.2 #12 -/
def rubi1212r12 : CRule where
  id := "integration.rubi_1_2_1_2_r12"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.var "x"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "c", "d", "e", "p"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .ne (.var "p") (.app2 .mul (.int (-3)) (.pow (.int 2) (.int (-1))))]
  priority := 1540
  description := "RUBI 1.2.1.2 #12"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:12" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#12"

/-- RUBI 1.2.1.3 #15 -/
def rubi1213r15 : CRule where
  id := "integration.rubi_1_2_1_3_r15"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g")))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "g"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "e")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g"))))) (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e")) (.var "g")))))) (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.var "p") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c")) (.var "e")) (.var "g"))) (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g")))))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.int (-1)) (.var "p")]
  priority := 1550
  description := "RUBI 1.2.1.3 #15"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:15" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#15"

/-- RUBI 1.2.1.3 #16 -/
def rubi1213r16 : CRule where
  id := "integration.rubi_1_2_1_3_r16"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g")))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e")) (.var "g")))) (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "c", "d", "e", "f", "g", "p"]
  conditions := [.gt (.int (-1)) (.var "p")]
  priority := 1560
  description := "RUBI 1.2.1.3 #16"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:16" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#16"

/-- RUBI 1.2.2.2 #17 -/
def rubi1222r17 : CRule where
  id := "integration.rubi_1_2_2_2_r17"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.var "a") (.pow (.var "d") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.app2 .add (.var "b") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 1580
  description := "RUBI 1.2.2.2 #17"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p:17" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p.m#17"

/-- RUBI 1.2.2.4 #55 -/
def rubi1224r55 : CRule where
  id := "integration.rubi_1_2_2_4_r55"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:55"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "d") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.pow (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 4))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 4))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.var "p") (.int 0),
    .gt (.int (-2)) (.var "m")]
  priority := 1590
  description := "RUBI 1.2.2.4 #55"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:55" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#55"

/-- RUBI 1.2.2.4 #56 -/
def rubi1224r56 : CRule where
  id := "integration.rubi_1_2_2_4_r56"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:56"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.pow (.pow (.var "d") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.pow (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 4))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 4))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f", "m", "p"]
  conditions := [.gt (.var "p") (.int 0),
    .gt (.int (-2)) (.var "m")]
  priority := 1600
  description := "RUBI 1.2.2.4 #56"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:56" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#56"

/-- RUBI 1.2.2.4 #59 -/
def rubi1224r59 : CRule where
  id := "integration.rubi_1_2_2_4_r59"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:59"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.int 4))) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 4))) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 4)))) (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 4)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 2)]
  priority := 1610
  description := "RUBI 1.2.2.4 #59"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:59" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#59"

/-- RUBI 1.2.2.4 #60 -/
def rubi1224r60 : CRule where
  id := "integration.rubi_1_2_2_4_r60"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:60"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "f") (.int 4))) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 4))) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 4)))) (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 4)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f", "m", "p"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 2)]
  priority := 1620
  description := "RUBI 1.2.2.4 #60"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:60" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#60"

/-- RUBI 1.2.2.4 #61 -/
def rubi1224r61 : CRule where
  id := "integration.rubi_1_2_2_4_r61"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:61"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")) (.pow (.var "f") (.int 2))) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 0)]
  priority := 1630
  description := "RUBI 1.2.2.4 #61"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:61" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#61"

/-- RUBI 1.2.2.4 #62 -/
def rubi1224r62 : CRule where
  id := "integration.rubi_1_2_2_4_r62"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:62"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")) (.pow (.var "f") (.int 2))) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f", "m", "p"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 0)]
  priority := 1640
  description := "RUBI 1.2.2.4 #62"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:62" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#62"

/-- RUBI 2.3 #24 -/
def rubi23r24 : CRule where
  id := "integration.rubi_2_3_r24"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")))))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.app1 .ln (.var "F"))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")))))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 2),
    .gt (.int (-1)) (.var "m")]
  priority := 1660
  description := "RUBI 2.3 #24"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:24" "2 Exponentials/2.3 Miscellaneous exponentials.m#24"

/-- RUBI 3.1.2 #6 -/
def rubi312r6 : CRule where
  id := "integration.rubi_3_1_2_r6"; legacyId := some "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.ne (.var "m") (.int (-1)),
    .gt (.int (-1)) (.var "p")]
  priority := 1720
  description := "RUBI 3.1.2 #6"
  provenance := migrated "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:6" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#6"

/-- RUBI 3.1.3 #10 -/
def rubi313r10 : CRule where
  id := "integration.rubi_3_1_3_r10"; legacyId := some "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 3)) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))]
  independent := ["a", "b", "c", "d", "e", "n", "q"]
  conditions := [.gt (.int (-1)) (.var "q")]
  priority := 1730
  description := "RUBI 3.1.3 #10"
  provenance := migrated "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:10" "3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p.m#10"

/-- RUBI 3.1.3 #7 -/
def rubi313r7 : CRule where
  id := "integration.rubi_3_1_3_r7"; legacyId := some "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "q")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "n", "p", "q"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .gt (.var "q") (.int 0)]
  priority := 1740
  description := "RUBI 3.1.3 #7"
  provenance := migrated "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:7" "3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p.m#7"

/-- RUBI 3.1.4 #12 -/
def rubi314r12 : CRule where
  id := "integration.rubi_3_1_4_r12"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "m")) (.app2 .mul (.var "b") (.var "n"))) (.app2 .mul (.app2 .mul (.var "b") (.var "m")) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q"]
  conditions := [.int (.var "q"),
    .gt (.int (-1)) (.var "q"),
    .gt (.var "m") (.int 0)]
  priority := 1750
  description := "RUBI 3.1.4 #12"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:12" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#12"

/-- RUBI 3.1.4 #13 -/
def rubi314r13 : CRule where
  id := "integration.rubi_3_1_4_r13"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 3))) (.app2 .mul (.var "b") (.var "n"))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 3))) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q"]
  conditions := [.int (.var "q"),
    .gt (.int (-1)) (.var "q"),
    .int (.var "m"),
    .gt (.int 0) (.var "m")]
  priority := 1760
  description := "RUBI 3.1.4 #13"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:13" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#13"

/-- RUBI 3.1.4 #18 -/
def rubi314r18 : CRule where
  id := "integration.rubi_3_1_4_r18"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "r", "p", "q"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .int (.var "q"),
    .gt (.int (-1)) (.var "q")]
  priority := 1780
  description := "RUBI 3.1.4 #18"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:18" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#18"

/-- RUBI 3.1.5 #17 -/
def rubi315r17 : CRule where
  id := "integration.rubi_3_1_5_r17"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "r", "p", "q"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .int (.var "q"),
    .gt (.int (-1)) (.var "q")]
  priority := 1800
  description := "RUBI 3.1.5 #17"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:17" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#17"

/-- RUBI 3.1.5 #8 -/
def rubi315r8 : CRule where
  id := "integration.rubi_3_1_5_r8"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "m")) (.app2 .mul (.var "b") (.var "n"))) (.app2 .mul (.app2 .mul (.var "b") (.var "m")) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q"]
  conditions := [.int (.var "q"),
    .gt (.int (-1)) (.var "q"),
    .gt (.var "m") (.int 0)]
  priority := 1810
  description := "RUBI 3.1.5 #8"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:8" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#8"

/-- RUBI 3.1.5 #9 -/
def rubi315r9 : CRule where
  id := "integration.rubi_3_1_5_r9"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 3))) (.app2 .mul (.var "b") (.var "n"))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 3))) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q"]
  conditions := [.int (.var "q"),
    .gt (.int (-1)) (.var "q"),
    .int (.var "m"),
    .gt (.int 0) (.var "m")]
  priority := 1820
  description := "RUBI 3.1.5 #9"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:9" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#9"

/-- RUBI 4.1.11 #3 -/
def rubi4111r3 : CRule where
  id := "integration.rubi_4_1_11_r3"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .mul (.int (-1)) (.var "n")) (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.int (-1)) (.var "n")) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .mul (.int (-1)) (.var "n")) (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.int (-1)) (.var "p"),
    .int (.var "n"),
    .gt (.var "n") (.int 2)]
  priority := 1840
  description := "RUBI 4.1.11 #3"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin:3" "4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin.m#3"

/-- RUBI 4.1.11 #4 -/
def rubi4111r4 : CRule where
  id := "integration.rubi_4_1_11_r4"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .mul (.int (-1)) (.var "n")) (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.int (-1)) (.var "n")) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .mul (.int (-1)) (.var "n")) (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.int (-1)) (.var "p"),
    .int (.var "n"),
    .gt (.var "n") (.int 2)]
  priority := 1850
  description := "RUBI 4.1.11 #4"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin:4" "4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin.m#4"

/-- RUBI 4.1.13 #21 -/
def rubi4113r21 : CRule where
  id := "integration.rubi_4_1_13_r21"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:21"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d")))) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 1860
  description := "RUBI 4.1.13 #21"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:21" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#21"

/-- RUBI 4.1.13 #22 -/
def rubi4113r22 : CRule where
  id := "integration.rubi_4_1_13_r22"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:22"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 1870
  description := "RUBI 4.1.13 #22"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:22" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#22"

/-! ## Refutations -/

section
variable {α : Type} [Field α] [CharZero α]
private theorem iv0 : intValue? (0 : α) = some 0 := by simpa using intValue?_intCast (α := α) 0
private theorem iv1 : intValue? (1 : α) = some 1 := by simpa using intValue?_intCast (α := α) 1
private theorem iv2 : intValue? (2 : α) = some 2 := by simpa using intValue?_intCast (α := α) 2
private theorem iv3 : intValue? (3 : α) = some 3 := by simpa using intValue?_intCast (α := α) 3
private theorem iv4 : intValue? (4 : α) = some 4 := by simpa using intValue?_intCast (α := α) 4
private theorem ivm1 : intValue? (-1 : α) = some (-1) := by simpa using intValue?_intCast (α := α) (-1)
private theorem ivm2 : intValue? (-2 : α) = some (-2) := by simpa using intValue?_intCast (α := α) (-2)
private theorem ivm3 : intValue? (-3 : α) = some (-3) := by simpa using intValue?_intCast (α := α) (-3)
private theorem ivnat (n : ℕ) [n.AtLeastTwo] : intValue? (OfNat.ofNat n : α) = some (OfNat.ofNat n) := by
  simpa using intValue?_intCast (α := α) (OfNat.ofNat n : ℤ)
private theorem ivneg (n : ℕ) [n.AtLeastTwo] :
    intValue? (-(OfNat.ofNat n : α)) = some (-(OfNat.ofNat n)) := by
  simpa using intValue?_intCast (α := α) (-(OfNat.ofNat n : ℤ))
end

theorem rubi1113r14_counterexample_real : ¬ rubi1113r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1113r14.conditions rubi1113r14.body rubi1113r14.result rubi1113r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "p" then -2 else if s = "a" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi1113r14, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1113r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1113r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "p" then -2 else if s = "a" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1113r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1113r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1113r14_counterexample_complex : ¬ rubi1113r14.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1113r14.conditions rubi1113r14.body rubi1113r14.result rubi1113r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "p" then -2 else if s = "a" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi1113r14, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1113r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1113r14.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "p" then -2 else if s = "a" ∨ s = "e" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1113r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1113r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1114r3_counterexample_real : ¬ rubi1114r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1114r3.conditions rubi1114r3.body rubi1114r3.result rubi1114r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "n" then -2 else 0) (1 : ℝ) (by simp [rubi1114r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1114r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1114r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "n" then -2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1114r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1114r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1114r3_counterexample_complex : ¬ rubi1114r3.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1114r3.conditions rubi1114r3.body rubi1114r3.result rubi1114r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "n" then -2 else 0) (1 : ℂ) (by simp [rubi1114r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1114r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1114r3.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "n" then -2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1114r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1114r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1135r24_counterexample_real : ¬ rubi1135r24.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1135r24.conditions rubi1135r24.body rubi1135r24.result rubi1135r24.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "q" then -2 else if s = "c" ∨ s = "f" ∨ s = "r" then 2 else 0) (1 : ℝ) (by simp [rubi1135r24, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1135r24, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1135r24.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "q" then -2 else if s = "c" ∨ s = "f" ∨ s = "r" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r24, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1135r24_counterexample_complex : ¬ rubi1135r24.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1135r24.conditions rubi1135r24.body rubi1135r24.result rubi1135r24.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "q" then -2 else if s = "c" ∨ s = "f" ∨ s = "r" then 2 else 0) (1 : ℂ) (by simp [rubi1135r24, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1135r24, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1135r24.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "q" then -2 else if s = "c" ∨ s = "f" ∨ s = "r" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r24, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1135r26_counterexample_real : ¬ rubi1135r26.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1135r26.conditions rubi1135r26.body rubi1135r26.result rubi1135r26.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "q" then -2 else if s = "c" ∨ s = "f" ∨ s = "r" then 1 else 0) (1 : ℝ) (by simp [rubi1135r26, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1135r26, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1135r26.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "q" then -2 else if s = "c" ∨ s = "f" ∨ s = "r" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r26, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1135r26_counterexample_complex : ¬ rubi1135r26.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1135r26.conditions rubi1135r26.body rubi1135r26.result rubi1135r26.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "q" then -2 else if s = "c" ∨ s = "f" ∨ s = "r" then 1 else 0) (1 : ℂ) (by simp [rubi1135r26, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1135r26, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1135r26.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "q" then -2 else if s = "c" ∨ s = "f" ∨ s = "r" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r26, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1212r12_counterexample_real : ¬ rubi1212r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r12.conditions rubi1212r12.body rubi1212r12.result rubi1212r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "p" then -2 else if s = "a" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi1212r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1212r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1212r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "p" then -2 else if s = "a" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1212r12_counterexample_complex : ¬ rubi1212r12.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r12.conditions rubi1212r12.body rubi1212r12.result rubi1212r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "p" then -2 else if s = "a" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi1212r12, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1212r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1212r12.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "p" then -2 else if s = "a" ∨ s = "e" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1213r15_counterexample_real : ¬ rubi1213r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1213r15.conditions rubi1213r15.body rubi1213r15.result rubi1213r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "f" ∨ s = "p" then -2 else if s = "b" ∨ s = "e" ∨ s = "g" then 1 else 0) (1 : ℝ) (by simp [rubi1213r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1213r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1213r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "f" ∨ s = "p" then -2 else if s = "b" ∨ s = "e" ∨ s = "g" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1213r15_counterexample_complex : ¬ rubi1213r15.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1213r15.conditions rubi1213r15.body rubi1213r15.result rubi1213r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "f" ∨ s = "p" then -2 else if s = "b" ∨ s = "e" ∨ s = "g" then 1 else 0) (1 : ℂ) (by simp [rubi1213r15, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1213r15, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1213r15.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "f" ∨ s = "p" then -2 else if s = "b" ∨ s = "e" ∨ s = "g" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r15, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1213r16_counterexample_real : ¬ rubi1213r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1213r16.conditions rubi1213r16.body rubi1213r16.result rubi1213r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "f" ∨ s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "g" then 1 else 0) (1 : ℝ) (by simp [rubi1213r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1213r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1213r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "f" ∨ s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "g" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1213r16_counterexample_complex : ¬ rubi1213r16.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1213r16.conditions rubi1213r16.body rubi1213r16.result rubi1213r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "f" ∨ s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "g" then 1 else 0) (1 : ℂ) (by simp [rubi1213r16, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1213r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1213r16.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "f" ∨ s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "g" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1222r17_counterexample_real : ¬ rubi1222r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1222r17.conditions rubi1222r17.body rubi1222r17.result rubi1222r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "m" then -2 else if s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi1222r17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1222r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1222r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "m" then -2 else if s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1222r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1222r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1222r17_counterexample_complex : ¬ rubi1222r17.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1222r17.conditions rubi1222r17.body rubi1222r17.result rubi1222r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "m" then -2 else if s = "d" then 1 else 0) (1 : ℂ) (by simp [rubi1222r17, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1222r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1222r17.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "m" then -2 else if s = "d" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1222r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1222r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1224r55_counterexample_real : ¬ rubi1224r55.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r55.conditions rubi1224r55.body rubi1224r55.result rubi1224r55.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then -3 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1224r55, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1224r55, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r55.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then -3 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r55, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r55, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1224r55_counterexample_complex : ¬ rubi1224r55.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1224r55.conditions rubi1224r55.body rubi1224r55.result rubi1224r55.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then -3 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1224r55, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1224r55, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r55.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then -3 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r55, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r55, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1224r56_counterexample_real : ¬ rubi1224r56.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r56.conditions rubi1224r56.body rubi1224r56.result rubi1224r56.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "m" then -3 else if s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1224r56, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1224r56, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r56.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "m" then -3 else if s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r56, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r56, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1224r56_counterexample_complex : ¬ rubi1224r56.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1224r56.conditions rubi1224r56.body rubi1224r56.result rubi1224r56.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "m" then -3 else if s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1224r56, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1224r56, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r56.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "m" then -3 else if s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r56, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r56, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1224r59_counterexample_real : ¬ rubi1224r59.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r59.conditions rubi1224r59.body rubi1224r59.result rubi1224r59.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "f" ∨ s = "p" then -2 else if s = "e" ∨ s = "m" then 3 else 0) (1 : ℝ) (by simp [rubi1224r59, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1224r59, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r59.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "f" ∨ s = "p" then -2 else if s = "e" ∨ s = "m" then 3 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r59, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r59, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1224r59_counterexample_complex : ¬ rubi1224r59.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1224r59.conditions rubi1224r59.body rubi1224r59.result rubi1224r59.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "f" ∨ s = "p" then -2 else if s = "e" ∨ s = "m" then 3 else 0) (1 : ℂ) (by simp [rubi1224r59, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1224r59, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r59.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "f" ∨ s = "p" then -2 else if s = "e" ∨ s = "m" then 3 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r59, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r59, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1224r60_counterexample_real : ¬ rubi1224r60.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r60.conditions rubi1224r60.body rubi1224r60.result rubi1224r60.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "f" ∨ s = "p" then -2 else if s = "d" ∨ s = "m" then 3 else 0) (1 : ℝ) (by simp [rubi1224r60, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1224r60, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r60.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "f" ∨ s = "p" then -2 else if s = "d" ∨ s = "m" then 3 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r60, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r60, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1224r60_counterexample_complex : ¬ rubi1224r60.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1224r60.conditions rubi1224r60.body rubi1224r60.result rubi1224r60.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "f" ∨ s = "p" then -2 else if s = "d" ∨ s = "m" then 3 else 0) (1 : ℂ) (by simp [rubi1224r60, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1224r60, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r60.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "f" ∨ s = "p" then -2 else if s = "d" ∨ s = "m" then 3 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r60, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r60, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1224r61_counterexample_real : ¬ rubi1224r61.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r61.conditions rubi1224r61.body rubi1224r61.result rubi1224r61.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "f" ∨ s = "p" then -2 else if s = "e" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi1224r61, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1224r61, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r61.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "f" ∨ s = "p" then -2 else if s = "e" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r61, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r61, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1224r61_counterexample_complex : ¬ rubi1224r61.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1224r61.conditions rubi1224r61.body rubi1224r61.result rubi1224r61.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "f" ∨ s = "p" then -2 else if s = "e" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi1224r61, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1224r61, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r61.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "f" ∨ s = "p" then -2 else if s = "e" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r61, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r61, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1224r62_counterexample_real : ¬ rubi1224r62.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r62.conditions rubi1224r62.body rubi1224r62.result rubi1224r62.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "f" ∨ s = "p" then -2 else if s = "d" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi1224r62, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1224r62, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r62.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "f" ∨ s = "p" then -2 else if s = "d" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r62, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r62, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1224r62_counterexample_complex : ¬ rubi1224r62.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1224r62.conditions rubi1224r62.body rubi1224r62.result rubi1224r62.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "f" ∨ s = "p" then -2 else if s = "d" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi1224r62, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1224r62, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r62.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "f" ∨ s = "p" then -2 else if s = "d" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r62, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r62, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi23r24_counterexample_real : ¬ rubi23r24.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi23r24.conditions rubi23r24.body rubi23r24.result rubi23r24.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "m" then -2 else if s = "F" ∨ s = "c" ∨ s = "e" ∨ s = "n" then 3 else 0) (1 : ℝ) (by simp [rubi23r24, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi23r24, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi23r24.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "m" then -2 else if s = "F" ∨ s = "c" ∨ s = "e" ∨ s = "n" then 3 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi23r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi23r24, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi23r24_counterexample_complex : ¬ rubi23r24.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi23r24.conditions rubi23r24.body rubi23r24.result rubi23r24.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "m" then -2 else if s = "F" ∨ s = "c" ∨ s = "e" ∨ s = "n" then 3 else 0) (1 : ℂ) (by simp [rubi23r24, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi23r24, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi23r24.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "m" then -2 else if s = "F" ∨ s = "c" ∨ s = "e" ∨ s = "n" then 3 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi23r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi23r24, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi312r6_counterexample_real : ¬ rubi312r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi312r6.conditions rubi312r6.body rubi312r6.result rubi312r6.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then -2 else if s = "a" ∨ s = "c" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi312r6, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi312r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi312r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then -2 else if s = "a" ∨ s = "c" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi312r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi312r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi312r6_counterexample_complex : ¬ rubi312r6.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi312r6.conditions rubi312r6.body rubi312r6.result rubi312r6.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then -2 else if s = "a" ∨ s = "c" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi312r6, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi312r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi312r6.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then -2 else if s = "a" ∨ s = "c" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi312r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi312r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi313r10_counterexample_real : ¬ rubi313r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi313r10.conditions rubi313r10.body rubi313r10.result rubi313r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi313r10, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi313r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi313r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "n" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi313r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi313r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi313r10_counterexample_complex : ¬ rubi313r10.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi313r10.conditions rubi313r10.body rubi313r10.result rubi313r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "n" then 2 else 0) (1 : ℂ) (by simp [rubi313r10, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi313r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi313r10.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "n" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi313r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi313r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi313r7_counterexample_real : ¬ rubi313r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi313r7.conditions rubi313r7.body rubi313r7.result rubi313r7.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then -2 else if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi313r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi313r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi313r7.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then -2 else if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi313r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi313r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi313r7_counterexample_complex : ¬ rubi313r7.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi313r7.conditions rubi313r7.body rubi313r7.result rubi313r7.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then -2 else if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "q" then 1 else 0) (1 : ℂ) (by simp [rubi313r7, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi313r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi313r7.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then -2 else if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "q" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi313r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi313r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi314r12_counterexample_real : ¬ rubi314r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi314r12.conditions rubi314r12.body rubi314r12.result rubi314r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi314r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi314r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi314r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi314r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi314r12_counterexample_complex : ¬ rubi314r12.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi314r12.conditions rubi314r12.body rubi314r12.result rubi314r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi314r12, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi314r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi314r12.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi314r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi314r13_counterexample_real : ¬ rubi314r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi314r13.conditions rubi314r13.body rubi314r13.result rubi314r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "m" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi314r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi314r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi314r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "m" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "n" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi314r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi314r13_counterexample_complex : ¬ rubi314r13.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi314r13.conditions rubi314r13.body rubi314r13.result rubi314r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "m" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "n" then 2 else 0) (1 : ℂ) (by simp [rubi314r13, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi314r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi314r13.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "m" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "n" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi314r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi314r18_counterexample_real : ¬ rubi314r18.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi314r18.conditions rubi314r18.body rubi314r18.result rubi314r18.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "p" ∨ s = "r" then 1 else 0) (1 : ℝ) (by simp [rubi314r18, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi314r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi314r18.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "p" ∨ s = "r" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi314r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi314r18_counterexample_complex : ¬ rubi314r18.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi314r18.conditions rubi314r18.body rubi314r18.result rubi314r18.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "p" ∨ s = "r" then 1 else 0) (1 : ℂ) (by simp [rubi314r18, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi314r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi314r18.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "p" ∨ s = "r" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi314r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi315r17_counterexample_real : ¬ rubi315r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi315r17.conditions rubi315r17.body rubi315r17.result rubi315r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "p" ∨ s = "r" then 1 else 0) (1 : ℝ) (by simp [rubi315r17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi315r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "p" ∨ s = "r" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi315r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi315r17_counterexample_complex : ¬ rubi315r17.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi315r17.conditions rubi315r17.body rubi315r17.result rubi315r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "p" ∨ s = "r" then 1 else 0) (1 : ℂ) (by simp [rubi315r17, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi315r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r17.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "p" ∨ s = "r" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi315r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi315r8_counterexample_real : ¬ rubi315r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi315r8.conditions rubi315r8.body rubi315r8.result rubi315r8.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi315r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi315r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi315r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi315r8_counterexample_complex : ¬ rubi315r8.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi315r8.conditions rubi315r8.body rubi315r8.result rubi315r8.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi315r8, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi315r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r8.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi315r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi315r9_counterexample_real : ¬ rubi315r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi315r9.conditions rubi315r9.body rubi315r9.result rubi315r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "m" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi315r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi315r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "m" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "n" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi315r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi315r9_counterexample_complex : ¬ rubi315r9.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi315r9.conditions rubi315r9.body rubi315r9.result rubi315r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "m" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "n" then 2 else 0) (1 : ℂ) (by simp [rubi315r9, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi315r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r9.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "m" ∨ s = "q" then -2 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "n" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi315r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi4111r3_counterexample_real : ¬ rubi4111r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4111r3.conditions rubi4111r3.body rubi4111r3.result rubi4111r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then -2 else if s = "c" ∨ s = "n" then 3 else 0) (1 : ℝ) (by simp [rubi4111r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4111r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4111r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then -2 else if s = "c" ∨ s = "n" then 3 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4111r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4111r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi4111r3_counterexample_complex : ¬ rubi4111r3.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4111r3.conditions rubi4111r3.body rubi4111r3.result rubi4111r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then -2 else if s = "c" ∨ s = "n" then 3 else 0) (1 : ℂ) (by simp [rubi4111r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4111r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4111r3.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then -2 else if s = "c" ∨ s = "n" then 3 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4111r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4111r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi4111r4_counterexample_real : ¬ rubi4111r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4111r4.conditions rubi4111r4.body rubi4111r4.result rubi4111r4.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then -2 else if s = "c" ∨ s = "n" then 3 else 0) (1 : ℝ) (by simp [rubi4111r4, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4111r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4111r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then -2 else if s = "c" ∨ s = "n" then 3 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4111r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4111r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi4111r4_counterexample_complex : ¬ rubi4111r4.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4111r4.conditions rubi4111r4.body rubi4111r4.result rubi4111r4.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then -2 else if s = "c" ∨ s = "n" then 3 else 0) (1 : ℂ) (by simp [rubi4111r4, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4111r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4111r4.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then -2 else if s = "c" ∨ s = "n" then 3 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4111r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4111r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi4113r21_counterexample_real : ¬ rubi4113r21.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r21.conditions rubi4113r21.body rubi4113r21.result rubi4113r21.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "m" then -2 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi4113r21, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4113r21, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4113r21.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "m" then -2 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r21, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi4113r21_counterexample_complex : ¬ rubi4113r21.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4113r21.conditions rubi4113r21.body rubi4113r21.result rubi4113r21.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "m" then -2 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℂ) (by simp [rubi4113r21, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4113r21, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4113r21.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "m" then -2 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r21, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi4113r22_counterexample_real : ¬ rubi4113r22.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r22.conditions rubi4113r22.body rubi4113r22.result rubi4113r22.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "m" then -2 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi4113r22, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4113r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4113r22.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "m" then -2 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r22, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi4113r22_counterexample_complex : ¬ rubi4113r22.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4113r22.conditions rubi4113r22.body rubi4113r22.result rubi4113r22.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "m" then -2 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℂ) (by simp [rubi4113r22, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4113r22, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4113r22.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "m" then -2 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r22, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r22, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec5
