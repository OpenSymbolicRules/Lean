import OSR.IntegrationRec2

/-!
# Integration (RUBI): refutations found by a numerical search

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

namespace OSR.IntegrationRec3

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.1.1.3 #12 -/
def rubi1113r12 : CRule where
  id := "integration.rubi_1_1_1_3_r12"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "p"]
  conditions := [.gt (.var "p") (.int 0)]
  priority := 800
  description := "RUBI 1.1.1.3 #12"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:12" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#12"

/-- RUBI 1.1.1.3 #13 -/
def rubi1113r13 : CRule where
  id := "integration.rubi_1_1_1_3_r13"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "b") (.var "d")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.var "e") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.pow (.var "f") (.int 2)))) (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "d")) (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "f"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")) (.var "f")))) (.var "x"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "p"]
  conditions := [.gt (.var "p") (.int 1)]
  priority := 810
  description := "RUBI 1.1.1.3 #13"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:13" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#13"

/-- RUBI 1.1.1.4 #38 -/
def rubi1114r38 : CRule where
  id := "integration.rubi_1_1_1_4_r38"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:38"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "q"))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "q"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "q", "p"]
  conditions := [.gt (.var "p") (.int 0)]
  priority := 820
  description := "RUBI 1.1.1.4 #38"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:38" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#38"

/-- RUBI 1.1.3.5 #25 -/
def rubi1135r25 : CRule where
  id := "integration.rubi_1_1_3_5_r25"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "r", "q"]
  conditions := [.gt (.var "q") (.int 1)]
  priority := 830
  description := "RUBI 1.1.3.5 #25"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:25" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#25"

/-- RUBI 1.1.3.6 #17 -/
def rubi1136r17 : CRule where
  id := "integration.rubi_1_1_3_6_r17"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.var "e") (.var "I1")) (.app2 .mul (.app2 .mul (.var "f") (.pow (.pow (.var "e") (.var "n")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p", "q", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 840
  description := "RUBI 1.1.3.6 #17"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:17" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#17"

/-- RUBI 1.1.3.6 #18 -/
def rubi1136r18 : CRule where
  id := "integration.rubi_1_1_3_6_r18"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r")))
  result := (.app2 .add (.app2 .mul (.var "e") (.var "I1")) (.app2 .mul (.app2 .mul (.var "f") (.pow (.pow (.var "e") (.var "n")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p", "q", "n", "r"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "r"),
    .gt (.var "r") (.int 0)]
  priority := 850
  description := "RUBI 1.1.3.6 #18"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:18" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#18"

/-- RUBI 1.2.1.1 #5 -/
def rubi1211r5 : CRule where
  id := "integration.rubi_1_2_1_1_r5"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:5"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "p")) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))]
  independent := ["a", "b", "c", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.var "p") (.int 0),
    .int (.app2 .mul (.int 4) (.var "p"))]
  priority := 860
  description := "RUBI 1.2.1.1 #5"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:5" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p.m#5"

/-- RUBI 1.2.1.2 #20 -/
def rubi1212r20 : CRule where
  id := "integration.rubi_1_2_1_2_r20"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "x")) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "e") (.var "p")) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "c") (.var "x"))) (.var "p"))))]
  independent := ["b", "c", "e", "m", "p"]
  conditions := [.int (.var "p")]
  priority := 870
  description := "RUBI 1.2.1.2 #20"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:20" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#20"

/-- RUBI 1.2.1.3 #19 -/
def rubi1213r19 : CRule where
  id := "integration.rubi_1_2_1_3_r19"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "x")) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "e") (.var "p")) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.var "p"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "c") (.var "x"))) (.var "p"))))]
  independent := ["b", "c", "e", "f", "g", "m", "p"]
  conditions := [.int (.var "p")]
  priority := 880
  description := "RUBI 1.2.1.3 #19"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:19" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#19"

/-- RUBI 2.1 #9 -/
def rubi21r9 : CRule where
  id := "integration.rubi_2_1_r9"; legacyId := some "rubi:2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))) (.int (-1)))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 890
  description := "RUBI 2.1 #9"
  provenance := migrated "rubi:2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p:9" "2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p.m#9"

/-- RUBI 2.2 #1 -/
def rubi22r1 : CRule where
  id := "integration.rubi_2_2_r1"; legacyId := some "rubi:2 Exponentials/2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "g")) (.var "n")) (.app1 .ln (.var "F"))) (.int (-1)))) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.var "a") (.int (-1))))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "g")) (.var "n")) (.app1 .ln (.var "F"))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.var "a") (.int (-1))))))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 900
  description := "RUBI 2.2 #1"
  provenance := migrated "rubi:2 Exponentials/2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p:1" "2 Exponentials/2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p.m#1"

/-- RUBI 2.3 #11 -/
def rubi23r11 : CRule where
  id := "integration.rubi_2_3_r11"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:11"
  shape := .antiderivRec; x := "x"
  body := (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")))))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.app1 .ln (.var "F"))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")))))))]
  independent := ["F", "a", "b", "c", "d", "n"]
  conditions := [.int (.app2 .mul (.int 2) (.pow (.var "n") (.int (-1)))),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 910
  description := "RUBI 2.3 #11"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:11" "2 Exponentials/2.3 Miscellaneous exponentials.m#11"

/-- RUBI 3.1.2 #5 -/
def rubi312r5 : CRule where
  id := "integration.rubi_3_1_2_r5"; legacyId := some "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.ne (.var "m") (.int (-1)),
    .gt (.var "p") (.int 0)]
  priority := 920
  description := "RUBI 3.1.2 #5"
  provenance := migrated "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:5" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#5"

/-- RUBI 3.1.3 #4 -/
def rubi313r4 : CRule where
  id := "integration.rubi_3_1_3_r4"; legacyId := some "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.var "d") (.int (-1)))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.var "e") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.var "d") (.int (-1)))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 930
  description := "RUBI 3.1.3 #4"
  provenance := migrated "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:4" "3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p.m#4"

/-- RUBI 3.1.4 #8 -/
def rubi314r8 : CRule where
  id := "integration.rubi_3_1_4_r8"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r"))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "e") (.pow (.var "x") (.var "r"))) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.var "d") (.var "r")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "d") (.var "r")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "e") (.pow (.var "x") (.var "r"))) (.int (-1)))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "n", "r", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 940
  description := "RUBI 3.1.4 #8"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:8" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#8"

/-- RUBI 3.1.5 #13 -/
def rubi315r13 : CRule where
  id := "integration.rubi_3_1_5_r13"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 950
  description := "RUBI 3.1.5 #13"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:13" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#13"

/-- RUBI 3.1.5 #14 -/
def rubi315r14 : CRule where
  id := "integration.rubi_3_1_5_r14"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r"))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "e") (.pow (.var "x") (.var "r"))) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.var "d") (.var "r")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "d") (.var "r")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "e") (.pow (.var "x") (.var "r"))) (.int (-1)))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "n", "r", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 960
  description := "RUBI 3.1.5 #14"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:14" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#14"

/-- RUBI 3.1.5 #28 -/
def rubi315r28 : CRule where
  id := "integration.rubi_3_1_5_r28"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:28"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "r")))))) (.var "q")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "r")))))) (.var "q"))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "q")) (.var "r")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "r")))))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "r")))))) (.var "q"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "r", "p", "q"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .int (.var "q"),
    .gt (.var "q") (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 970
  description := "RUBI 3.1.5 #28"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:28" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#28"

/-- RUBI 3.1.5 #33 -/
def rubi315r33 : CRule where
  id := "integration.rubi_3_1_5_r33"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.var "r")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.var "r")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.var "r")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "r", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .ne (.app2 .mul (.var "d") (.var "e")) (.int 1)]
  priority := 980
  description := "RUBI 3.1.5 #33"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:33" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#33"

/-- RUBI 3.2.1 #1 -/
def rubi321r1 : CRule where
  id := "integration.rubi_3_2_1_r1"; legacyId := some "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))) (.var "p"))) (.pow (.var "b") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "n")) (.var "p")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "b") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 990
  description := "RUBI 3.2.1 #1"
  provenance := migrated "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:1" "3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.m#1"

/-- RUBI 3.3 #31 -/
def rubi33r31 : CRule where
  id := "integration.rubi_3_3_r31"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.int 2) (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.int 2) (.var "m")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "m")))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 1000
  description := "RUBI 3.3 #31"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:31" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#31"

/-- RUBI 3.3 #35 -/
def rubi33r35 : CRule where
  id := "integration.rubi_3_3_r35"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:35"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "i") (.app2 .mul (.var "j") (.var "x"))) (.var "m")))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "i") (.app2 .mul (.var "j") (.var "x"))) (.var "m"))))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.var "j")) (.var "m")) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.var "p")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))) (.pow (.app2 .add (.var "i") (.app2 .mul (.var "j") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "i") (.app2 .mul (.var "j") (.var "x"))) (.var "m"))))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 1010
  description := "RUBI 3.3 #35"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:35" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#35"

/-- RUBI 3.4 #2 -/
def rubi34r2 : CRule where
  id := "integration.rubi_3_4_r2"; legacyId := some "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:2"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int (-1))))) (.var "p")))))) (.var "q"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "e") (.app2 .mul (.var "d") (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int (-1))))) (.var "p")))))) (.var "q"))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "p")) (.var "q")) (.pow (.var "d") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int (-1))))) (.var "p")))))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p", "q"]
  conditions := [.int (.var "q"),
    .gt (.var "q") (.int 0)]
  priority := 1020
  description := "RUBI 3.4 #2"
  provenance := migrated "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:2" "3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p.m#2"

/-- RUBI 3.4 #9 -/
def rubi34r9 : CRule where
  id := "integration.rubi_3_4_r9"; legacyId := some "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "p")))))) (.var "q")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "p")))))) (.var "q"))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.var "p")) (.var "q")) (.pow (.app2 .mul (.pow (.var "f") (.var "n")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "p")))))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p", "n", "q"]
  conditions := [.int (.var "q"),
    .gt (.var "q") (.int 1),
    .int (.var "n"),
    .ne (.var "m") (.int (-1))]
  priority := 1030
  description := "RUBI 3.4 #9"
  provenance := migrated "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:9" "3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p.m#9"

/-- RUBI 4.1.12 #33 -/
def rubi4112r33 : CRule where
  id := "integration.rubi_4_1_12_r33"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "e") (.var "n")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.app2 .add (.var "m") (.int 1)) (.var "n")]
  priority := 1050
  description := "RUBI 4.1.12 #33"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:33" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#33"

/-- RUBI 4.1.12 #34 -/
def rubi4112r34 : CRule where
  id := "integration.rubi_4_1_12_r34"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:34"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "e") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.var "n"))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.app2 .add (.var "m") (.int 1)) (.var "n")]
  priority := 1060
  description := "RUBI 4.1.12 #34"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:34" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#34"

/-- RUBI 4.1.12 #83 -/
def rubi4112r83 : CRule where
  id := "integration.rubi_4_1_12_r83"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:83"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "p", "m", "n"]
  conditions := [.gt (.var "n") (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 1070
  description := "RUBI 4.1.12 #83"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:83" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#83"

/-- RUBI 4.1.12 #84 -/
def rubi4112r84 : CRule where
  id := "integration.rubi_4_1_12_r84"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:84"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "p", "m", "n"]
  conditions := [.gt (.var "n") (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 1080
  description := "RUBI 4.1.12 #84"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:84" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#84"

/-- RUBI 4.1.13 #19 -/
def rubi4113r19 : CRule where
  id := "integration.rubi_4_1_13_r19"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d")))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 1090
  description := "RUBI 4.1.13 #19"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:19" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#19"

/-- RUBI 4.1.13 #20 -/
def rubi4113r20 : CRule where
  id := "integration.rubi_4_1_13_r20"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d")))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 1100
  description := "RUBI 4.1.13 #20"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:20" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#20"

/-- RUBI 4.7.6 #1 -/
def rubi476r1 : CRule where
  id := "integration.rubi_4_7_6_r1"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 1110
  description := "RUBI 4.7.6 #1"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:1" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#1"

/-- RUBI 4.7.6 #16 -/
def rubi476r16 : CRule where
  id := "integration.rubi_4_7_6_r16"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 1120
  description := "RUBI 4.7.6 #16"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:16" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#16"

/-- RUBI 4.7.6 #17 -/
def rubi476r17 : CRule where
  id := "integration.rubi_4_7_6_r17"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 1130
  description := "RUBI 4.7.6 #17"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:17" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#17"

/-- RUBI 4.7.6 #2 -/
def rubi476r2 : CRule where
  id := "integration.rubi_4_7_6_r2"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m"))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 1140
  description := "RUBI 4.7.6 #2"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:2" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#2"

/-- RUBI 4.7.8 #13 -/
def rubi478r13 : CRule where
  id := "integration.rubi_4_7_8_r13"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 1),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int 0)]
  priority := 1160
  description := "RUBI 4.7.8 #13"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:13" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#13"

/-- RUBI 4.7.8 #14 -/
def rubi478r14 : CRule where
  id := "integration.rubi_4_7_8_r14"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 1),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int 0)]
  priority := 1170
  description := "RUBI 4.7.8 #14"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:14" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#14"

/-- RUBI 4.7.9 #1 -/
def rubi479r1 : CRule where
  id := "integration.rubi_4_7_9_r1"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 1180
  description := "RUBI 4.7.9 #1"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:1" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#1"

/-- RUBI 4.7.9 #11 -/
def rubi479r11 : CRule where
  id := "integration.rubi_4_7_9_r11"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "b") (.int (-1)))) (.var "I2"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I3")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))),
    ("I3", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 1),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 1190
  description := "RUBI 4.7.9 #11"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:11" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#11"

/-- RUBI 4.7.9 #12 -/
def rubi479r12 : CRule where
  id := "integration.rubi_4_7_9_r12"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "b") (.int (-1)))) (.var "I2"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I3")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))),
    ("I3", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 1),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 1200
  description := "RUBI 4.7.9 #12"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:12" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#12"

/-- RUBI 4.7.9 #16 -/
def rubi479r16 : CRule where
  id := "integration.rubi_4_7_9_r16"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 1210
  description := "RUBI 4.7.9 #16"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:16" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#16"

/-- RUBI 4.7.9 #2 -/
def rubi479r2 : CRule where
  id := "integration.rubi_4_7_9_r2"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 1220
  description := "RUBI 4.7.9 #2"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:2" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#2"

/-- RUBI 4.7.9 #25 -/
def rubi479r25 : CRule where
  id := "integration.rubi_4_7_9_r25"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 1230
  description := "RUBI 4.7.9 #25"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:25" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#25"

/-- RUBI 4.7.9 #26 -/
def rubi479r26 : CRule where
  id := "integration.rubi_4_7_9_r26"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:26"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 1240
  description := "RUBI 4.7.9 #26"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:26" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#26"

/-- RUBI 4.7.9 #27 -/
def rubi479r27 : CRule where
  id := "integration.rubi_4_7_9_r27"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 1250
  description := "RUBI 4.7.9 #27"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:27" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#27"

/-- RUBI 4.7.9 #30 -/
def rubi479r30 : CRule where
  id := "integration.rubi_4_7_9_r30"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 1260
  description := "RUBI 4.7.9 #30"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:30" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#30"

/-- RUBI 1.2.2.4 #57 -/
def rubi1224r57 : CRule where
  id := "integration.rubi_1_2_2_4_r57"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:57"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "d") (.var "e")) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.pow (.var "f") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.var "p") (.int 0),
    .gt (.int 0) (.var "m")]
  priority := 1320
  description := "RUBI 1.2.2.4 #57"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:57" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#57"

/-- RUBI 1.2.2.4 #58 -/
def rubi1224r58 : CRule where
  id := "integration.rubi_1_2_2_4_r58"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:58"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "d") (.var "e")) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.pow (.var "f") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f", "m", "p"]
  conditions := [.gt (.var "p") (.int 0),
    .gt (.int 0) (.var "m")]
  priority := 1330
  description := "RUBI 1.2.2.4 #58"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:58" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#58"

/-- RUBI 2.1 #10 -/
def rubi21r10 : CRule where
  id := "integration.rubi_2_1_r10"; legacyId := some "rubi:2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))) (.app2 .add (.var "p") (.int 1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))) (.var "p"))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "n", "m", "p"]
  conditions := [.int (.var "p"),
    .gt (.int 0) (.var "p"),
    .int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 1340
  description := "RUBI 2.1 #10"
  provenance := migrated "rubi:2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p:10" "2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p.m#10"

/-- RUBI 4.1.12 #45 -/
def rubi4112r45 : CRule where
  id := "integration.rubi_4_1_12_r45"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:45"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))) (.pow (.var "p") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.gt (.var "p") (.int 1),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))]
  priority := 1360
  description := "RUBI 4.1.12 #45"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:45" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#45"

/-- RUBI 4.1.12 #46 -/
def rubi4112r46 : CRule where
  id := "integration.rubi_4_1_12_r46"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:46"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))) (.pow (.var "p") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.gt (.var "p") (.int 1),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))]
  priority := 1370
  description := "RUBI 4.1.12 #46"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:46" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#46"

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
end

theorem rubi1113r12_counterexample_real : ¬ rubi1113r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1113r12.conditions rubi1113r12.body rubi1113r12.result rubi1113r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1113r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1113r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1113r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1113r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1113r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1113r12_counterexample_complex : ¬ rubi1113r12.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1113r12.conditions rubi1113r12.body rubi1113r12.result rubi1113r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1113r12, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1113r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1113r12.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1113r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1113r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1113r13_counterexample_real : ¬ rubi1113r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1113r13.conditions rubi1113r13.body rubi1113r13.result rubi1113r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi1113r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1113r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1113r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1113r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1113r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1113r13_counterexample_complex : ¬ rubi1113r13.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1113r13.conditions rubi1113r13.body rubi1113r13.result rubi1113r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi1113r13, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1113r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1113r13.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1113r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1113r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1114r38_counterexample_real : ¬ rubi1114r38.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1114r38.conditions rubi1114r38.body rubi1114r38.result rubi1114r38.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi1114r38, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1114r38, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1114r38.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "p" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1114r38, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1114r38, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1114r38_counterexample_complex : ¬ rubi1114r38.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1114r38.conditions rubi1114r38.body rubi1114r38.result rubi1114r38.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℂ) (by simp [rubi1114r38, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1114r38, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1114r38.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "p" ∨ s = "q" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1114r38, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1114r38, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1135r25_counterexample_real : ¬ rubi1135r25.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1135r25.conditions rubi1135r25.body rubi1135r25.result rubi1135r25.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "q" ∨ s = "r" then 2 else 0) (1 : ℝ) (by simp [rubi1135r25, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1135r25, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1135r25.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "q" ∨ s = "r" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r25, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1135r25_counterexample_complex : ¬ rubi1135r25.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1135r25.conditions rubi1135r25.body rubi1135r25.result rubi1135r25.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "q" ∨ s = "r" then 2 else 0) (1 : ℂ) (by simp [rubi1135r25, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1135r25, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1135r25.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "q" ∨ s = "r" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r25, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1136r17_counterexample_real : ¬ rubi1136r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1136r17.conditions rubi1136r17.body rubi1136r17.result rubi1136r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi1136r17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1136r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1136r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1136r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1136r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1136r17_counterexample_complex : ¬ rubi1136r17.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1136r17.conditions rubi1136r17.body rubi1136r17.result rubi1136r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℂ) (by simp [rubi1136r17, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1136r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1136r17.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1136r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1136r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1136r18_counterexample_real : ¬ rubi1136r18.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1136r18.conditions rubi1136r18.body rubi1136r18.result rubi1136r18.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "r" then 1 else 0) (1 : ℝ) (by simp [rubi1136r18, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1136r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1136r18.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "r" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1136r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1136r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1136r18_counterexample_complex : ¬ rubi1136r18.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1136r18.conditions rubi1136r18.body rubi1136r18.result rubi1136r18.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "r" then 1 else 0) (1 : ℂ) (by simp [rubi1136r18, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1136r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1136r18.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "r" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1136r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1136r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1211r5_counterexample_real : ¬ rubi1211r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1211r5.conditions rubi1211r5.body rubi1211r5.result rubi1211r5.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1211r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1211r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1211r5.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1211r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1211r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1211r5_counterexample_complex : ¬ rubi1211r5.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1211r5.conditions rubi1211r5.body rubi1211r5.result rubi1211r5.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1211r5, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1211r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1211r5.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1211r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1211r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1212r20_counterexample_real : ¬ rubi1212r20.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r20.conditions rubi1212r20.body rubi1212r20.result rubi1212r20.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1212r20, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1212r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1212r20.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1212r20_counterexample_complex : ¬ rubi1212r20.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r20.conditions rubi1212r20.body rubi1212r20.result rubi1212r20.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1212r20, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1212r20, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1212r20.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r20, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1213r19_counterexample_real : ¬ rubi1213r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1213r19.conditions rubi1213r19.body rubi1213r19.result rubi1213r19.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1213r19, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1213r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1213r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1213r19_counterexample_complex : ¬ rubi1213r19.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1213r19.conditions rubi1213r19.body rubi1213r19.result rubi1213r19.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1213r19, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1213r19, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1213r19.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r19, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi21r9_counterexample_real : ¬ rubi21r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi21r9.conditions rubi21r9.body rubi21r9.result rubi21r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi21r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi21r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi21r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi21r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi21r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi21r9_counterexample_complex : ¬ rubi21r9.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi21r9.conditions rubi21r9.body rubi21r9.result rubi21r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi21r9, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi21r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi21r9.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi21r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi21r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi22r1_counterexample_real : ¬ rubi22r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi22r1.conditions rubi22r1.body rubi22r1.result rubi22r1.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi22r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi22r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num) ⟨rubi22r1.integrals[0]!, by simp [rubi22r1], ?_⟩
  intro h
  simp [rubi22r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] at h <;> norm_num at h

theorem rubi22r1_counterexample_complex : ¬ rubi22r1.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi22r1.conditions rubi22r1.body rubi22r1.result rubi22r1.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi22r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi22r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num) ⟨rubi22r1.integrals[0]!, by simp [rubi22r1], ?_⟩
  intro h
  simp [rubi22r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] at h <;> norm_num at h

theorem rubi23r11_counterexample_real : ¬ rubi23r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi23r11.conditions rubi23r11.body rubi23r11.result rubi23r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "n" then -1 else 0) (1 : ℝ) (by simp [rubi23r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi23r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi23r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "n" then -1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi23r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi23r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi23r11_counterexample_complex : ¬ rubi23r11.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi23r11.conditions rubi23r11.body rubi23r11.result rubi23r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "n" then -1 else 0) (1 : ℂ) (by simp [rubi23r11, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi23r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi23r11.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "n" then -1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi23r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi23r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi312r5_counterexample_real : ¬ rubi312r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi312r5.conditions rubi312r5.body rubi312r5.result rubi312r5.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi312r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi312r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi312r5.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi312r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi312r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi312r5_counterexample_complex : ¬ rubi312r5.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi312r5.conditions rubi312r5.body rubi312r5.result rubi312r5.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi312r5, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi312r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi312r5.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi312r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi312r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi313r4_counterexample_real : ¬ rubi313r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi313r4.conditions rubi313r4.body rubi313r4.result rubi313r4.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi313r4, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi313r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi313r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi313r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi313r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi313r4_counterexample_complex : ¬ rubi313r4.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi313r4.conditions rubi313r4.body rubi313r4.result rubi313r4.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi313r4, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi313r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi313r4.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi313r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi313r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi314r8_counterexample_real : ¬ rubi314r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi314r8.conditions rubi314r8.body rubi314r8.result rubi314r8.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "n" ∨ s = "p" ∨ s = "r" then 2 else 0) (1 : ℝ) (by simp [rubi314r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi314r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi314r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "n" ∨ s = "p" ∨ s = "r" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi314r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi314r8_counterexample_complex : ¬ rubi314r8.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi314r8.conditions rubi314r8.body rubi314r8.result rubi314r8.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "n" ∨ s = "p" ∨ s = "r" then 2 else 0) (1 : ℂ) (by simp [rubi314r8, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi314r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi314r8.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "n" ∨ s = "p" ∨ s = "r" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi314r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi315r13_counterexample_real : ¬ rubi315r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi315r13.conditions rubi315r13.body rubi315r13.result rubi315r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "n" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi315r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi315r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "n" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi315r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi315r13_counterexample_complex : ¬ rubi315r13.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi315r13.conditions rubi315r13.body rubi315r13.result rubi315r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "n" ∨ s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi315r13, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi315r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r13.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "n" ∨ s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi315r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi315r14_counterexample_real : ¬ rubi315r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi315r14.conditions rubi315r14.body rubi315r14.result rubi315r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "n" ∨ s = "p" ∨ s = "r" then 2 else 0) (1 : ℝ) (by simp [rubi315r14, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi315r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "n" ∨ s = "p" ∨ s = "r" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi315r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi315r14_counterexample_complex : ¬ rubi315r14.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi315r14.conditions rubi315r14.body rubi315r14.result rubi315r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "n" ∨ s = "p" ∨ s = "r" then 2 else 0) (1 : ℂ) (by simp [rubi315r14, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi315r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r14.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "n" ∨ s = "p" ∨ s = "r" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi315r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi315r28_counterexample_real : ¬ rubi315r28.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi315r28.conditions rubi315r28.body rubi315r28.result rubi315r28.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi315r28, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi315r28, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r28.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi315r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r28, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi315r28_counterexample_complex : ¬ rubi315r28.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi315r28.conditions rubi315r28.body rubi315r28.result rubi315r28.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℂ) (by simp [rubi315r28, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi315r28, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r28.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi315r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r28, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi315r33_counterexample_complex : ¬ rubi315r33.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi315r33.conditions rubi315r33.body rubi315r33.result rubi315r33.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "r" then 2 else 0) (1 : ℂ) (by simp [rubi315r33, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi315r33, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi315r33.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "r" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi315r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r33, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi321r1_counterexample_real : ¬ rubi321r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi321r1.conditions rubi321r1.body rubi321r1.result rubi321r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "B" ∨ s = "a" ∨ s = "d" ∨ s = "e" ∨ s = "n" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi321r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi321r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi321r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "B" ∨ s = "a" ∨ s = "d" ∨ s = "e" ∨ s = "n" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi321r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi321r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi321r1_counterexample_complex : ¬ rubi321r1.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi321r1.conditions rubi321r1.body rubi321r1.result rubi321r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "B" ∨ s = "a" ∨ s = "d" ∨ s = "e" ∨ s = "n" ∨ s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi321r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi321r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi321r1.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "B" ∨ s = "a" ∨ s = "d" ∨ s = "e" ∨ s = "n" ∨ s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi321r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi321r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi33r31_counterexample_real : ¬ rubi33r31.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi33r31.conditions rubi33r31.body rubi33r31.result rubi33r31.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" then 2 else 0) (-1 : ℝ) (by simp [rubi33r31, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (-1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi33r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num) ⟨rubi33r31.integrals[0]!, by simp [rubi33r31], ?_⟩
  intro h
  simp [rubi33r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] at h <;> norm_num at h

theorem rubi33r31_counterexample_complex : ¬ rubi33r31.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi33r31.conditions rubi33r31.body rubi33r31.result rubi33r31.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" then 2 else 0) (-1 : ℂ) (by simp [rubi33r31, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (-1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi33r31, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num) ⟨rubi33r31.integrals[0]!, by simp [rubi33r31], ?_⟩
  intro h
  simp [rubi33r31, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] at h <;> norm_num at h

theorem rubi33r35_counterexample_real : ¬ rubi33r35.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi33r35.conditions rubi33r35.body rubi33r35.result rubi33r35.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "i" ∨ s = "j" ∨ s = "n" ∨ s = "p" then 1 else 0) (-1 : ℝ) (by simp [rubi33r35, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi33r35, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num) ⟨rubi33r35.integrals[0]!, by simp [rubi33r35], ?_⟩
  intro h
  simp [rubi33r35, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] at h <;> norm_num at h

theorem rubi33r35_counterexample_complex : ¬ rubi33r35.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi33r35.conditions rubi33r35.body rubi33r35.result rubi33r35.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "i" ∨ s = "j" ∨ s = "n" ∨ s = "p" then 1 else 0) (-1 : ℂ) (by simp [rubi33r35, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi33r35, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num) ⟨rubi33r35.integrals[0]!, by simp [rubi33r35], ?_⟩
  intro h
  simp [rubi33r35, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] at h <;> norm_num at h

theorem rubi34r2_counterexample_real : ¬ rubi34r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi34r2.conditions rubi34r2.body rubi34r2.result rubi34r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "p" ∨ s = "q" then 2 else 0) (1 : ℝ) (by simp [rubi34r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi34r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi34r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "p" ∨ s = "q" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi34r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi34r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi34r2_counterexample_complex : ¬ rubi34r2.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi34r2.conditions rubi34r2.body rubi34r2.result rubi34r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "p" ∨ s = "q" then 2 else 0) (1 : ℂ) (by simp [rubi34r2, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi34r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi34r2.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "p" ∨ s = "q" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi34r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi34r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi34r9_counterexample_real : ¬ rubi34r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi34r9.conditions rubi34r9.body rubi34r9.result rubi34r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 2 else 0) (1 : ℝ) (by simp [rubi34r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi34r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi34r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi34r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi34r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4112r33_counterexample_real : ¬ rubi4112r33.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4112r33.conditions rubi4112r33.body rubi4112r33.result rubi4112r33.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi4112r33, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4112r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4112r33.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4112r33_counterexample_complex : ¬ rubi4112r33.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4112r33.conditions rubi4112r33.body rubi4112r33.result rubi4112r33.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi4112r33, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4112r33, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4112r33.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r33, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4112r34_counterexample_real : ¬ rubi4112r34.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4112r34.conditions rubi4112r34.body rubi4112r34.result rubi4112r34.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi4112r34, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4112r34, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4112r34.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r34, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r34, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4112r34_counterexample_complex : ¬ rubi4112r34.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4112r34.conditions rubi4112r34.body rubi4112r34.result rubi4112r34.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi4112r34, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4112r34, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4112r34.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r34, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r34, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4112r83_counterexample_real : ¬ rubi4112r83.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4112r83.conditions rubi4112r83.body rubi4112r83.result rubi4112r83.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi4112r83, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4112r83, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4112r83.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r83, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r83, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4112r83_counterexample_complex : ¬ rubi4112r83.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4112r83.conditions rubi4112r83.body rubi4112r83.result rubi4112r83.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi4112r83, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4112r83, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4112r83.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r83, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r83, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4112r84_counterexample_real : ¬ rubi4112r84.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4112r84.conditions rubi4112r84.body rubi4112r84.result rubi4112r84.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi4112r84, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4112r84, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4112r84.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r84, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r84, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4112r84_counterexample_complex : ¬ rubi4112r84.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4112r84.conditions rubi4112r84.body rubi4112r84.result rubi4112r84.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi4112r84, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4112r84, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4112r84.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r84, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r84, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4113r19_counterexample_real : ¬ rubi4113r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r19.conditions rubi4113r19.body rubi4113r19.result rubi4113r19.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi4113r19, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4113r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4113r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4113r19_counterexample_complex : ¬ rubi4113r19.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4113r19.conditions rubi4113r19.body rubi4113r19.result rubi4113r19.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi4113r19, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4113r19, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4113r19.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r19, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4113r20_counterexample_real : ¬ rubi4113r20.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r20.conditions rubi4113r20.body rubi4113r20.result rubi4113r20.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi4113r20, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4113r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4113r20.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4113r20_counterexample_complex : ¬ rubi4113r20.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4113r20.conditions rubi4113r20.body rubi4113r20.result rubi4113r20.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi4113r20, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4113r20, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4113r20.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r20, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi476r1_counterexample_real : ¬ rubi476r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi476r1.conditions rubi476r1.body rubi476r1.result rubi476r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi476r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi476r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi476r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi476r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi476r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi476r1_counterexample_complex : ¬ rubi476r1.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi476r1.conditions rubi476r1.body rubi476r1.result rubi476r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi476r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi476r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi476r1.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi476r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi476r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi476r16_counterexample_real : ¬ rubi476r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi476r16.conditions rubi476r16.body rubi476r16.result rubi476r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi476r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi476r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi476r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi476r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi476r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi476r16_counterexample_complex : ¬ rubi476r16.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi476r16.conditions rubi476r16.body rubi476r16.result rubi476r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi476r16, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi476r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi476r16.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi476r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi476r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi476r17_counterexample_real : ¬ rubi476r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi476r17.conditions rubi476r17.body rubi476r17.result rubi476r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi476r17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi476r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi476r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi476r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi476r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi476r17_counterexample_complex : ¬ rubi476r17.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi476r17.conditions rubi476r17.body rubi476r17.result rubi476r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi476r17, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi476r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi476r17.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi476r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi476r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi476r2_counterexample_real : ¬ rubi476r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi476r2.conditions rubi476r2.body rubi476r2.result rubi476r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi476r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi476r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi476r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi476r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi476r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi478r13_counterexample_real : ¬ rubi478r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi478r13.conditions rubi478r13.body rubi478r13.result rubi478r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi478r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi478r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi478r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi478r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi478r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi478r13_counterexample_complex : ¬ rubi478r13.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi478r13.conditions rubi478r13.body rubi478r13.result rubi478r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi478r13, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi478r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi478r13.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi478r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi478r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi478r14_counterexample_real : ¬ rubi478r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi478r14.conditions rubi478r14.body rubi478r14.result rubi478r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi478r14, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi478r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi478r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi478r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi478r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi478r14_counterexample_complex : ¬ rubi478r14.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi478r14.conditions rubi478r14.body rubi478r14.result rubi478r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi478r14, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi478r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi478r14.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi478r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi478r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r1_counterexample_real : ¬ rubi479r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r1.conditions rubi479r1.body rubi479r1.result rubi479r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi479r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r1_counterexample_complex : ¬ rubi479r1.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r1.conditions rubi479r1.body rubi479r1.result rubi479r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi479r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r1.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi479r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r11_counterexample_real : ¬ rubi479r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r11.conditions rubi479r11.body rubi479r11.result rubi479r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi479r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r11_counterexample_complex : ¬ rubi479r11.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r11.conditions rubi479r11.body rubi479r11.result rubi479r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 2 else 0) (1 : ℂ) (by simp [rubi479r11, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r11.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi479r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r12_counterexample_real : ¬ rubi479r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r12.conditions rubi479r12.body rubi479r12.result rubi479r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi479r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r12_counterexample_complex : ¬ rubi479r12.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r12.conditions rubi479r12.body rubi479r12.result rubi479r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 2 else 0) (1 : ℂ) (by simp [rubi479r12, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r12.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi479r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r16_counterexample_real : ¬ rubi479r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r16.conditions rubi479r16.body rubi479r16.result rubi479r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi479r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r16_counterexample_complex : ¬ rubi479r16.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r16.conditions rubi479r16.body rubi479r16.result rubi479r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi479r16, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r16.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi479r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r2_counterexample_real : ¬ rubi479r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r2.conditions rubi479r2.body rubi479r2.result rubi479r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi479r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r2_counterexample_complex : ¬ rubi479r2.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r2.conditions rubi479r2.body rubi479r2.result rubi479r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi479r2, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r2.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi479r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r25_counterexample_real : ¬ rubi479r25.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r25.conditions rubi479r25.body rubi479r25.result rubi479r25.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi479r25, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r25, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r25.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r25, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r25_counterexample_complex : ¬ rubi479r25.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r25.conditions rubi479r25.body rubi479r25.result rubi479r25.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi479r25, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r25, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r25.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi479r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r25, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r26_counterexample_real : ¬ rubi479r26.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r26.conditions rubi479r26.body rubi479r26.result rubi479r26.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi479r26, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r26, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r26.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r26, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r26_counterexample_complex : ¬ rubi479r26.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r26.conditions rubi479r26.body rubi479r26.result rubi479r26.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi479r26, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r26, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r26.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi479r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r26, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r27_counterexample_real : ¬ rubi479r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r27.conditions rubi479r27.body rubi479r27.result rubi479r27.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi479r27, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r27_counterexample_complex : ¬ rubi479r27.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r27.conditions rubi479r27.body rubi479r27.result rubi479r27.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi479r27, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r27, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r27.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi479r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r27, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r30_counterexample_real : ¬ rubi479r30.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r30.conditions rubi479r30.body rubi479r30.result rubi479r30.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi479r30, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r30, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r30.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r30, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi479r30_counterexample_complex : ¬ rubi479r30.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r30.conditions rubi479r30.body rubi479r30.result rubi479r30.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi479r30, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi479r30, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi479r30.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi479r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r30, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1224r57_counterexample_real : ¬ rubi1224r57.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r57.conditions rubi1224r57.body rubi1224r57.result rubi1224r57.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then -1 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1224r57, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1224r57, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r57.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then -1 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r57, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r57, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1224r57_counterexample_complex : ¬ rubi1224r57.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1224r57.conditions rubi1224r57.body rubi1224r57.result rubi1224r57.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then -1 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1224r57, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1224r57, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r57.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "m" then -1 else if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r57, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r57, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1224r58_counterexample_real : ¬ rubi1224r58.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r58.conditions rubi1224r58.body rubi1224r58.result rubi1224r58.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "m" then -1 else if s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1224r58, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1224r58, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r58.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "m" then -1 else if s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r58, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r58, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi1224r58_counterexample_complex : ¬ rubi1224r58.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1224r58.conditions rubi1224r58.body rubi1224r58.result rubi1224r58.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "m" then -1 else if s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1224r58, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1224r58, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1224r58.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "m" then -1 else if s = "c" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1224r58, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1224r58, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi21r10_counterexample_real : ¬ rubi21r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi21r10.conditions rubi21r10.body rubi21r10.result rubi21r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "g" ∨ s = "p" then -1 else if s = "F" ∨ s = "c" ∨ s = "e" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi21r10, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi21r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi21r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "g" ∨ s = "p" then -1 else if s = "F" ∨ s = "c" ∨ s = "e" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi21r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi21r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi21r10_counterexample_complex : ¬ rubi21r10.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi21r10.conditions rubi21r10.body rubi21r10.result rubi21r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "g" ∨ s = "p" then -1 else if s = "F" ∨ s = "c" ∨ s = "e" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi21r10, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi21r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi21r10.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "g" ∨ s = "p" then -1 else if s = "F" ∨ s = "c" ∨ s = "e" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi21r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi21r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4112r45_counterexample_real : ¬ rubi4112r45.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4112r45.conditions rubi4112r45.body rubi4112r45.result rubi4112r45.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "n" then 1 else if s = "m" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi4112r45, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4112r45, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4112r45.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "n" then 1 else if s = "m" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r45, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r45, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4112r45_counterexample_complex : ¬ rubi4112r45.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4112r45.conditions rubi4112r45.body rubi4112r45.result rubi4112r45.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "n" then 1 else if s = "m" ∨ s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi4112r45, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4112r45, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4112r45.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "n" then 1 else if s = "m" ∨ s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r45, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r45, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4112r46_counterexample_real : ¬ rubi4112r46.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4112r46.conditions rubi4112r46.body rubi4112r46.result rubi4112r46.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "n" then 1 else if s = "m" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi4112r46, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4112r46, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4112r46.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "n" then 1 else if s = "m" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r46, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r46, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

theorem rubi4112r46_counterexample_complex : ¬ rubi4112r46.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4112r46.conditions rubi4112r46.body rubi4112r46.result rubi4112r46.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "n" then 1 else if s = "m" ∨ s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi4112r46, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi4112r46, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi4112r46.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "n" then 1 else if s = "m" ∨ s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r46, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r46, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec3
