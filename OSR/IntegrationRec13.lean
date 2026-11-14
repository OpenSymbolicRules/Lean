import OSR.IntegrationRec12

/-!
# Integration (RUBI): rules with `EqQ` conditions, refuted

RUBI rules whose conditions include `EqQ`, stated with `relation1#eq`.
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

namespace OSR.IntegrationRec13

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

def rubi1112r1 : CRule where
  id := "integration.rubi_1_1_1_2_r1"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 2))) (.int (-1))))
  independent := ["a", "b", "c", "d", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.var "m") (.int 2)))) (.int 0)]
  priority := 3000
  description := "RUBI 1.1.1.2 #1"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:1" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.m#1"

def rubi1113r2 : CRule where
  id := "integration.rubi_1_1_1_3_r2"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:2"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2)) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1)))))) (.int 0)]
  priority := 3010
  description := "RUBI 1.1.1.3 #2"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:2" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#2"

def rubi1113r53 : CRule where
  id := "integration.rubi_1_1_1_3_r53"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:53"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.pow (.var "f") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.pow (.pow (.var "f") (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.app2 .add (.var "m") (.var "n")),
    .gt (.app2 .add (.var "m") (.var "n")) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "d")) (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))))) (.int 0)]
  priority := 3020
  description := "RUBI 1.1.1.3 #53"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:53" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#53"

def rubi1113r9 : CRule where
  id := "integration.rubi_1_1_1_3_r9"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:9"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 2)))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.var "x")))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 2))) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2)) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3)) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 2))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "e")) (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1))))))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1))))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 4))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 2)))))))) (.int 0)]
  priority := 3030
  description := "RUBI 1.1.1.3 #9"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:9" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#9"

def rubi1117r6 : CRule where
  id := "integration.rubi_1_1_1_7_r6"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:6"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b1")) (.var "b2")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a1", "b1", "a2", "b2", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)) (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 3040
  description := "RUBI 1.1.1.7 #6"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:6" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#6"

def rubi1131r3 : CRule where
  id := "integration.rubi_1_1_3_1_r3"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.1 (a+b x^n)^p:3"
  shape := .antideriv; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))
  result := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.var "a") (.int (-1))))
  independent := ["a", "b", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.app2 .mul (.int 1) (.pow (.var "n") (.int (-1)))) (.var "p")) (.int 1)) (.int 0)]
  priority := 3050
  description := "RUBI 1.1.3.1 #3"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.1 (a+b x^n)^p:3" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.1 (a+b x^n)^p.m#3"

def rubi1132r3 : CRule where
  id := "integration.rubi_1_1_3_2_r3"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:3"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1))]
  priority := 3060
  description := "RUBI 1.1.3.2 #3"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:3" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.m#3"

def rubi1132r4 : CRule where
  id := "integration.rubi_1_1_3_2_r4"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:4"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b1")) (.var "b2")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a1", "b1", "a2", "b2", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0),
    .eq (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1))]
  priority := 3070
  description := "RUBI 1.1.3.2 #4"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:4" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.m#4"

def rubi1132r6 : CRule where
  id := "integration.rubi_1_1_3_2_r6"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:6"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "c") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "c") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.var "n") (.int (-1)))) (.var "p")) (.int 1)) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 3080
  description := "RUBI 1.1.3.2 #6"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:6" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.m#6"

def rubi1132r7 : CRule where
  id := "integration.rubi_1_1_3_2_r7"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:7"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "c") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "c") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a1") (.var "a2")) (.var "c")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a1", "b1", "a2", "b2", "c", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.app2 .mul (.int 2) (.var "n")) (.int (-1)))) (.var "p")) (.int 1)) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 3090
  description := "RUBI 1.1.3.2 #7"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p:7" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.2 (c x)^m (a+b x^n)^p.m#7"

def rubi1133r10 : CRule where
  id := "integration.rubi_1_1_3_3_r10"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:10"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.var "a") (.int (-1))))
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0)]
  priority := 3100
  description := "RUBI 1.1.3.3 #10"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:10" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#10"

def rubi1133r18 : CRule where
  id := "integration.rubi_1_1_3_3_r18"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "p", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.int 1)) (.int 0),
    .int (.var "n")]
  priority := 3110
  description := "RUBI 1.1.3.3 #18"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:18" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#18"

def rubi1133r5 : CRule where
  id := "integration.rubi_1_1_3_3_r5"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "q")) (.pow (.app2 .mul (.var "a") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "n", "p", "q"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int 1)) (.int 0),
    .gt (.var "q") (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 3120
  description := "RUBI 1.1.3.3 #5"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:5" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#5"

def rubi1133r8 : CRule where
  id := "integration.rubi_1_1_3_3_r8"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:8"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.var "a") (.var "c")) (.int (-1))))
  independent := ["a", "b", "c", "d", "n", "p", "q"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 2))) (.int 1)) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "p") (.int 1))) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "q") (.int 1)))) (.int 0)]
  priority := 3130
  description := "RUBI 1.1.3.3 #8"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:8" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#8"

def rubi1134r14 : CRule where
  id := "integration.rubi_1_1_3_4_r14"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:14"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)))) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 3140
  description := "RUBI 1.1.3.4 #14"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:14" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#14"

def rubi1134r17 : CRule where
  id := "integration.rubi_1_1_3_4_r17"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "e")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 3150
  description := "RUBI 1.1.3.4 #17"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:17" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#17"

def rubi1137r5 : CRule where
  id := "integration.rubi_1_1_3_7_r5"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.pow (.var "B") (.int 3)) (.pow (.var "b") (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.app2 .add (.pow (.var "A") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "B")) (.var "x"))) (.app2 .mul (.pow (.var "B") (.int 2)) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "A", "B"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.pow (.var "B") (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "A") (.int 3)))) (.int 0)]
  priority := 3160
  description := "RUBI 1.1.3.7 #5"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p:5" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p.m#5"

def rubi1211r1 : CRule where
  id := "integration.rubi_1_2_1_1_r1"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:1"
  shape := .antideriv; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))
  result := (.app2 .mul (.app2 .mul (.int 2) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)) (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x")))) (.int (-1))))
  independent := ["a", "b", "c", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.int (-1)) (.var "p")]
  priority := 3170
  description := "RUBI 1.2.1.1 #1"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:1" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p.m#1"

def rubi1211r3 : CRule where
  id := "integration.rubi_1_2_1_1_r3"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:3"
  shape := .antideriv; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))
  result := (.app2 .mul (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.var "p") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))]
  priority := 3180
  description := "RUBI 1.2.1.1 #3"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:3" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p.m#3"

def rubi1212r1 : CRule where
  id := "integration.rubi_1_2_1_2_r1"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.var "x"))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 3190
  description := "RUBI 1.2.1.2 #1"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:1" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#1"

def rubi1212r102 : CRule where
  id := "integration.rubi_1_2_1_2_r102"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:102"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.int 2)) (.var "c")) (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "m")) (.int 2)) (.var "c")) (.var "d")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .gt (.int (-1)) (.var "p")]
  priority := 3200
  description := "RUBI 1.2.1.2 #102"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:102" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#102"

def rubi1212r104 : CRule where
  id := "integration.rubi_1_2_1_2_r104"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:104"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)]
  priority := 3210
  description := "RUBI 1.2.1.2 #104"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:104" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#104"

def rubi1212r39 : CRule where
  id := "integration.rubi_1_2_1_2_r39"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:39"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.pow (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 0),
    .int (.app2 .mul (.int 2) (.var "p"))]
  priority := 3220
  description := "RUBI 1.2.1.2 #39"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:39" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#39"

def rubi1212r4 : CRule where
  id := "integration.rubi_1_2_1_2_r4"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:4"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 3230
  description := "RUBI 1.2.1.2 #4"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:4" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#4"

def rubi1212r40 : CRule where
  id := "integration.rubi_1_2_1_2_r40"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:40"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "c", "d", "e", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 0),
    .int (.app2 .mul (.int 2) (.var "p"))]
  priority := 3240
  description := "RUBI 1.2.1.2 #40"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:40" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#40"

def rubi1212r41 : CRule where
  id := "integration.rubi_1_2_1_2_r41"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:41"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 1),
    .int (.app2 .mul (.int 2) (.var "p"))]
  priority := 3250
  description := "RUBI 1.2.1.2 #41"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:41" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#41"

def rubi1212r42 : CRule where
  id := "integration.rubi_1_2_1_2_r42"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:42"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "c", "d", "e", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 1),
    .int (.app2 .mul (.int 2) (.var "p"))]
  priority := 3260
  description := "RUBI 1.2.1.2 #42"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:42" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#42"

def rubi1212r43 : CRule where
  id := "integration.rubi_1_2_1_2_r43"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:43"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.var "p")) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "p", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 1),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0),
    .int (.app2 .mul (.int 2) (.var "p"))]
  priority := 3270
  description := "RUBI 1.2.1.2 #43"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:43" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#43"

def rubi1212r44 : CRule where
  id := "integration.rubi_1_2_1_2_r44"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:44"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 1),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0),
    .int (.app2 .mul (.int 2) (.var "p"))]
  priority := 3280
  description := "RUBI 1.2.1.2 #44"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:44" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#44"

def rubi1212r45 : CRule where
  id := "integration.rubi_1_2_1_2_r45"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:45"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "p", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int 0) (.var "m"),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0),
    .int (.app2 .mul (.int 2) (.var "p"))]
  priority := 3290
  description := "RUBI 1.2.1.2 #45"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:45" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#45"

def rubi1212r46 : CRule where
  id := "integration.rubi_1_2_1_2_r46"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:46"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int 0) (.var "m"),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0),
    .int (.app2 .mul (.int 2) (.var "p"))]
  priority := 3300
  description := "RUBI 1.2.1.2 #46"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:46" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#46"

def rubi1212r5 : CRule where
  id := "integration.rubi_1_2_1_2_r5"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.var "x"))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)]
  priority := 3310
  description := "RUBI 1.2.1.2 #5"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:5" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#5"

def rubi1212r55 : CRule where
  id := "integration.rubi_1_2_1_2_r55"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:55"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 3320
  description := "RUBI 1.2.1.2 #55"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:55" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#55"

def rubi1213r1 : CRule where
  id := "integration.rubi_1_2_1_3_r1"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "x")) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m"))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "x")) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int (-1))))
  independent := ["b", "c", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0)]
  priority := 3330
  description := "RUBI 1.2.1.3 #1"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:1" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#1"

def rubi1213r13 : CRule where
  id := "integration.rubi_1_2_1_3_r13"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:13"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "g")) (.app2 .add (.var "p") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g")))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "e")) (.var "g")) (.app2 .add (.var "p") (.int 1))) (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "g", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.var "p") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c")) (.var "e")) (.var "g"))) (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g")))))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))) (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 3340
  description := "RUBI 1.2.1.3 #13"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:13" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#13"

def rubi1213r14 : CRule where
  id := "integration.rubi_1_2_1_3_r14"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:14"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g"))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "g")) (.app2 .add (.var "p") (.int 1))) (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int (-1))))
  independent := ["a", "c", "d", "e", "f", "g", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))) (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 3350
  description := "RUBI 1.2.1.3 #14"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:14" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#14"

def rubi1213r20 : CRule where
  id := "integration.rubi_1_2_1_3_r20"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.var "p"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.var "x"))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 3360
  description := "RUBI 1.2.1.3 #20"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:20" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#20"

def rubi1213r24 : CRule where
  id := "integration.rubi_1_2_1_3_r24"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:24"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.var "g") (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.var "f")))) (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))))) (.int 0)]
  priority := 3370
  description := "RUBI 1.2.1.3 #24"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:24" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#24"

def rubi1213r25 : CRule where
  id := "integration.rubi_1_2_1_3_r25"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:25"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int (-1))))
  independent := ["a", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.var "e") (.var "f")))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "f")) (.app2 .add (.var "p") (.int 1)))) (.int 0)]
  priority := 3380
  description := "RUBI 1.2.1.3 #25"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:25" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#25"

def rubi1213r26 : CRule where
  id := "integration.rubi_1_2_1_3_r26"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:26"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "g") (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.var "f"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app2 .add (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.var "g") (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.var "f")))) (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")))))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 0)]
  priority := 3390
  description := "RUBI 1.2.1.3 #26"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:26" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#26"

def rubi1213r27 : CRule where
  id := "integration.rubi_1_2_1_3_r27"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.var "e") (.var "f"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app2 .add (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.var "e") (.var "f")))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "f")) (.app2 .add (.var "p") (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 0)]
  priority := 3400
  description := "RUBI 1.2.1.3 #27"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:27" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#27"

def rubi1213r33 : CRule where
  id := "integration.rubi_1_2_1_3_r33"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.var "e") (.var "f")))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "f")) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0),
    .ne (.var "m") (.int 2)]
  priority := 3410
  description := "RUBI 1.2.1.3 #33"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:33" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#33"

def rubi1213r35 : CRule where
  id := "integration.rubi_1_2_1_3_r35"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:35"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "c") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))),
    ("I2", (.app2 .mul (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "f", "g", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.pow (.var "g") (.int 2))) (.app2 .mul (.pow (.var "f") (.int 2)) (.var "c"))) (.int 0)]
  priority := 3420
  description := "RUBI 1.2.1.3 #35"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:35" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#35"

def rubi1213r36 : CRule where
  id := "integration.rubi_1_2_1_3_r36"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:36"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "f") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "g") (.int (-1)))) (.var "x"))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "f") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "g"))) (.app2 .mul (.var "a") (.pow (.var "g") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 3430
  description := "RUBI 1.2.1.3 #36"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:36" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#36"

def rubi1213r5 : CRule where
  id := "integration.rubi_1_2_1_3_r5"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:5"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "g")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g")))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))) (.int 0)]
  priority := 3440
  description := "RUBI 1.2.1.3 #5"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:5" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#5"

def rubi1213r6 : CRule where
  id := "integration.rubi_1_2_1_3_r6"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "g")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 0)]
  priority := 3450
  description := "RUBI 1.2.1.3 #6"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:6" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#6"

def rubi1213r7 : CRule where
  id := "integration.rubi_1_2_1_3_r7"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-2)) (.var "c")) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g")))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g"))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)]
  priority := 3460
  description := "RUBI 1.2.1.3 #7"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:7" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#7"

def rubi1214r1 : CRule where
  id := "integration.rubi_1_2_1_4_r1"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "n"))) (.app2 .add (.app2 .mul (.var "b") (.var "x")) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .add (.var "m") (.int 2)))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "g") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3))) (.int (-1))))
  independent := ["b", "c", "f", "g", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "m") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)) (.int 0)]
  priority := 3470
  description := "RUBI 1.2.1.4 #1"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:1" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p.m#1"

def rubi1214r65 : CRule where
  id := "integration.rubi_1_2_1_4_r65"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:65"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "p") (.int 1))) (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1)))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)]
  priority := 3480
  description := "RUBI 1.2.1.4 #65"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:65" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p.m#65"

def rubi1214r66 : CRule where
  id := "integration.rubi_1_2_1_4_r66"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:66"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.int (-1))))
  independent := ["a", "c", "d", "e", "m", "p"]
  conditions := [.eq (.app2 .mul (.var "d") (.app2 .add (.var "p") (.int 1))) (.int 0),
    .eq (.app2 .mul (.var "a") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0)]
  priority := 3490
  description := "RUBI 1.2.1.4 #66"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:66" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p.m#66"

def rubi1216r10 : CRule where
  id := "integration.rubi_1_2_1_6_r10"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "x")) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "q")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "f") (.int (-1)))) (.var "x"))) (.var "p")) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "x")) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.var "q")))))]
  independent := ["a", "c", "e", "f", "q", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "e") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "f") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 3500
  description := "RUBI 1.2.1.6 #10"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:10" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#10"

def rubi1216r5 : CRule where
  id := "integration.rubi_1_2_1_6_r5"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "m")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "g")) (.pow (.var "a") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "h")) (.var "x")) (.pow (.var "c") (.int (-1))))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "m") (.var "p")))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")) (.var "h"))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "e")) (.var "g")) (.var "h"))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.pow (.var "h") (.int 2)))) (.int 0),
    .int (.var "m")]
  priority := 3510
  description := "RUBI 1.2.1.6 #5"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:5" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#5"

def rubi1216r6 : CRule where
  id := "integration.rubi_1_2_1_6_r6"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "m")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "g")) (.pow (.var "a") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "h")) (.var "x")) (.pow (.var "c") (.int (-1))))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "m") (.var "p")))))]
  independent := ["a", "c", "d", "e", "f", "g", "h", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "e")) (.var "g")) (.var "h"))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.pow (.var "h") (.int 2)))) (.int 0),
    .int (.var "m")]
  priority := 3520
  description := "RUBI 1.2.1.6 #6"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:6" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#6"

def rubi1216r7 : CRule where
  id := "integration.rubi_1_2_1_6_r7"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "m")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "g")) (.pow (.var "a") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "h")) (.var "x")) (.pow (.var "c") (.int (-1))))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "m") (.var "p")))))]
  independent := ["a", "b", "c", "d", "f", "g", "h", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")) (.var "h"))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.pow (.var "h") (.int 2)))) (.int 0),
    .int (.var "m")]
  priority := 3530
  description := "RUBI 1.2.1.6 #7"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:7" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#7"

def rubi1216r8 : CRule where
  id := "integration.rubi_1_2_1_6_r8"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "m")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "g")) (.pow (.var "a") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "h")) (.var "x")) (.pow (.var "c") (.int (-1))))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "m") (.var "p")))))]
  independent := ["a", "c", "d", "f", "g", "h", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.pow (.var "h") (.int 2)))) (.int 0),
    .int (.var "m")]
  priority := 3540
  description := "RUBI 1.2.1.6 #8"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:8" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#8"

def rubi1216r9 : CRule where
  id := "integration.rubi_1_2_1_6_r9"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "p")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "x")) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "q")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "f") (.int (-1)))) (.var "x"))) (.var "p")) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "x")) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.var "q")))))]
  independent := ["a", "b", "c", "e", "f", "q", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "e") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "f"))) (.app2 .mul (.var "a") (.pow (.var "f") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 3550
  description := "RUBI 1.2.1.6 #9"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:9" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#9"


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
private theorem ivm6 : intValue? (-6 : α) = some (-6) := by simpa using intValue?_intCast (α := α) (-6)
private theorem ivex2 : ∃ n, intValue? (2 : α) = some n ∧ 0 ≤ n := ⟨2, iv2, by norm_num⟩
private theorem ivexInt (z : ℤ) : ∃ n, intValue? (z : α) = some n := ⟨z, intValue?_intCast z⟩
private theorem ivexm1 : ∃ n, intValue? (-1 : α) = some n := ⟨_, ivm1⟩
private theorem ivm4 : intValue? (-4 : α) = some (-4) := by simpa using intValue?_intCast (α := α) (-4)
private theorem ivexm4 : ∃ n, intValue? (-4 : α) = some n := ⟨_, ivm4⟩
private theorem ivexm6 : ∃ n, intValue? (-6 : α) = some n := ⟨_, ivm6⟩
end


private theorem rsin1 : Real.sin 1 ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [Real.pi_gt_three])).ne'

private theorem csin1 : Complex.sin 1 ≠ 0 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sin]; exact_mod_cast rsin1

theorem rubi1112r1_counterexample_real : ¬ rubi1112r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1112r1.conditions rubi1112r1.body rubi1112r1.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi1112r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1112r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1112r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1112r1_counterexample_complex : ¬ rubi1112r1.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1112r1.conditions rubi1112r1.body rubi1112r1.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi1112r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1112r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1112r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1113r2_counterexample_real : ¬ rubi1113r2.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1113r2.conditions rubi1113r2.body rubi1113r2.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1113r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1113r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1113r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1113r2_counterexample_complex : ¬ rubi1113r2.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1113r2.conditions rubi1113r2.body rubi1113r2.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1113r2, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1113r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1113r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1113r53_counterexample_real : ¬ rubi1113r53.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1113r53.conditions rubi1113r53.body rubi1113r53.result rubi1113r53.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi1113r53, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1113r53, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1113r53.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1113r53, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1113r53, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1113r53_counterexample_complex : ¬ rubi1113r53.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1113r53.conditions rubi1113r53.body rubi1113r53.result rubi1113r53.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi1113r53, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1113r53, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1113r53.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1113r53, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1113r53, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1113r9_counterexample_real : ¬ rubi1113r9.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1113r9.conditions rubi1113r9.body rubi1113r9.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1113r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1113r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1113r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1113r9_counterexample_complex : ¬ rubi1113r9.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1113r9.conditions rubi1113r9.body rubi1113r9.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1113r9, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1113r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1113r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1117r6_counterexample_real : ¬ rubi1117r6.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1117r6.conditions rubi1117r6.body rubi1117r6.result
  refine not_antiderivHoldsUnder (fun s => if s = "b2" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1117r6, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1117r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1117r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1117r6_counterexample_complex : ¬ rubi1117r6.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1117r6.conditions rubi1117r6.body rubi1117r6.result
  refine not_antiderivHoldsUnder (fun s => if s = "b2" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1117r6, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1117r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1117r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1131r3_counterexample_real : ¬ rubi1131r3.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1131r3.conditions rubi1131r3.body rubi1131r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" then -1 else 0) (1 : ℝ) (by simp [rubi1131r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1131r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1131r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1131r3_counterexample_complex : ¬ rubi1131r3.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1131r3.conditions rubi1131r3.body rubi1131r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" then -1 else 0) (1 : ℂ) (by simp [rubi1131r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1131r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1131r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1132r3_counterexample_real : ¬ rubi1132r3.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1132r3.conditions rubi1132r3.body rubi1132r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1132r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1132r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1132r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1132r3_counterexample_complex : ¬ rubi1132r3.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1132r3.conditions rubi1132r3.body rubi1132r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1132r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1132r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1132r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1132r4_counterexample_real : ¬ rubi1132r4.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1132r4.conditions rubi1132r4.body rubi1132r4.result
  refine not_antiderivHoldsUnder (fun s => if s = "b2" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1132r4, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1132r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1132r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1132r4_counterexample_complex : ¬ rubi1132r4.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1132r4.conditions rubi1132r4.body rubi1132r4.result
  refine not_antiderivHoldsUnder (fun s => if s = "b2" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1132r4, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1132r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1132r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1132r6_counterexample_real : ¬ rubi1132r6.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1132r6.conditions rubi1132r6.body rubi1132r6.result
  refine not_antiderivHoldsUnder (fun s => if s = "p" then -2 else if s = "a" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi1132r6, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1132r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1132r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1132r6_counterexample_complex : ¬ rubi1132r6.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1132r6.conditions rubi1132r6.body rubi1132r6.result
  refine not_antiderivHoldsUnder (fun s => if s = "p" then -2 else if s = "a" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi1132r6, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1132r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1132r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1132r7_counterexample_real : ¬ rubi1132r7.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1132r7.conditions rubi1132r7.body rubi1132r7.result
  refine not_antiderivHoldsUnder (fun s => if s = "p" then -2 else if s = "a1" ∨ s = "a2" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi1132r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1132r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1132r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1132r7_counterexample_complex : ¬ rubi1132r7.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1132r7.conditions rubi1132r7.body rubi1132r7.result
  refine not_antiderivHoldsUnder (fun s => if s = "p" then -2 else if s = "a1" ∨ s = "a2" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi1132r7, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1132r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1132r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1133r10_counterexample_real : ¬ rubi1133r10.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1133r10.conditions rubi1133r10.body rubi1133r10.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" then -1 else if s = "b" ∨ s = "c" then 1 else 0) (1 : ℝ) (by simp [rubi1133r10, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1133r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1133r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1133r10_counterexample_complex : ¬ rubi1133r10.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1133r10.conditions rubi1133r10.body rubi1133r10.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" then -1 else if s = "b" ∨ s = "c" then 1 else 0) (1 : ℂ) (by simp [rubi1133r10, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1133r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1133r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1133r18_counterexample_real : ¬ rubi1133r18.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1133r18.conditions rubi1133r18.body rubi1133r18.result rubi1133r18.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi1133r18, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1133r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1133r18.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1133r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1133r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1133r18_counterexample_complex : ¬ rubi1133r18.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1133r18.conditions rubi1133r18.body rubi1133r18.result rubi1133r18.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi1133r18, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1133r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1133r18.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1133r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1133r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1133r5_counterexample_real : ¬ rubi1133r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1133r5.conditions rubi1133r5.body rubi1133r5.result rubi1133r5.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "b" ∨ s = "c" ∨ s = "n" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi1133r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1133r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1133r5.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "b" ∨ s = "c" ∨ s = "n" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1133r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1133r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1133r5_counterexample_complex : ¬ rubi1133r5.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1133r5.conditions rubi1133r5.body rubi1133r5.result rubi1133r5.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "b" ∨ s = "c" ∨ s = "n" ∨ s = "q" then 1 else 0) (1 : ℂ) (by simp [rubi1133r5, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1133r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1133r5.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "b" ∨ s = "c" ∨ s = "n" ∨ s = "q" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1133r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1133r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1133r8_counterexample_real : ¬ rubi1133r8.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1133r8.conditions rubi1133r8.body rubi1133r8.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "c" ∨ s = "n" ∨ s = "q" then -1 else 0) (1 : ℝ) (by simp [rubi1133r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1133r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1133r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1133r8_counterexample_complex : ¬ rubi1133r8.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1133r8.conditions rubi1133r8.body rubi1133r8.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "c" ∨ s = "n" ∨ s = "q" then -1 else 0) (1 : ℂ) (by simp [rubi1133r8, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1133r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1133r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1134r14_counterexample_real : ¬ rubi1134r14.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1134r14.conditions rubi1134r14.body rubi1134r14.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else if s = "a" then 2 else 0) (1 : ℝ) (by simp [rubi1134r14, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1134r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1134r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1134r14_counterexample_complex : ¬ rubi1134r14.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1134r14.conditions rubi1134r14.body rubi1134r14.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else if s = "a" then 2 else 0) (1 : ℂ) (by simp [rubi1134r14, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1134r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1134r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1134r17_counterexample_real : ¬ rubi1134r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1134r17.conditions rubi1134r17.body rubi1134r17.result rubi1134r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi1134r17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1134r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1134r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1134r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1134r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1134r17_counterexample_complex : ¬ rubi1134r17.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1134r17.conditions rubi1134r17.body rubi1134r17.result rubi1134r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi1134r17, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1134r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1134r17.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1134r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1134r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1137r5_counterexample_real : ¬ rubi1137r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1137r5.conditions rubi1137r5.body rubi1137r5.result rubi1137r5.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then 1 else 0) (1 : ℝ) (by simp [rubi1137r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1137r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1137r5.integrals[0]!, by simp [rubi1137r5], ?_⟩
  intro h
  simp [rubi1137r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1137r5_counterexample_complex : ¬ rubi1137r5.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1137r5.conditions rubi1137r5.body rubi1137r5.result rubi1137r5.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then 1 else 0) (1 : ℂ) (by simp [rubi1137r5, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1137r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1137r5.integrals[0]!, by simp [rubi1137r5], ?_⟩
  intro h
  simp [rubi1137r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1211r1_counterexample_real : ¬ rubi1211r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1211r1.conditions rubi1211r1.body rubi1211r1.result
  refine not_antiderivHoldsUnder (fun s => if s = "p" then -3 else if s = "a" then 1 else 0) (1 : ℝ) (by simp [rubi1211r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1211r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1211r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1211r1_counterexample_complex : ¬ rubi1211r1.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1211r1.conditions rubi1211r1.body rubi1211r1.result
  refine not_antiderivHoldsUnder (fun s => if s = "p" then -3 else if s = "a" then 1 else 0) (1 : ℂ) (by simp [rubi1211r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1211r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1211r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1211r3_counterexample_real : ¬ rubi1211r3.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1211r3.conditions rubi1211r3.body rubi1211r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1211r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1211r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1211r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1211r3_counterexample_complex : ¬ rubi1211r3.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1211r3.conditions rubi1211r3.body rubi1211r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1211r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1211r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1211r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1212r1_counterexample_real : ¬ rubi1212r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r1.conditions rubi1212r1.body rubi1212r1.result rubi1212r1.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1212r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1212r1.integrals[0]!, by simp [rubi1212r1], ?_⟩
  intro h
  simp [rubi1212r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1212r1_counterexample_complex : ¬ rubi1212r1.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r1.conditions rubi1212r1.body rubi1212r1.result rubi1212r1.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1212r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1212r1.integrals[0]!, by simp [rubi1212r1], ?_⟩
  intro h
  simp [rubi1212r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1212r102_counterexample_real : ¬ rubi1212r102.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r102.conditions rubi1212r102.body rubi1212r102.result rubi1212r102.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi1212r102, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r102, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r102.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r102, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r102, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r102_counterexample_complex : ¬ rubi1212r102.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r102.conditions rubi1212r102.body rubi1212r102.result rubi1212r102.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi1212r102, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r102, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r102.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r102, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r102, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r104_counterexample_real : ¬ rubi1212r104.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r104.conditions rubi1212r104.body rubi1212r104.result rubi1212r104.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then -1 else 0) (1 : ℝ) (by simp [rubi1212r104, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1212r104, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r104.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then -1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r104, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r104, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r104_counterexample_complex : ¬ rubi1212r104.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r104.conditions rubi1212r104.body rubi1212r104.result rubi1212r104.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then -1 else 0) (1 : ℂ) (by simp [rubi1212r104, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1212r104, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r104.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then -1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r104, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r104, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r39_counterexample_real : ¬ rubi1212r39.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r39.conditions rubi1212r39.body rubi1212r39.result rubi1212r39.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "b" ∨ s = "d" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi1212r39, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1212r39, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r39.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "b" ∨ s = "d" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r39, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r39, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r39_counterexample_complex : ¬ rubi1212r39.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r39.conditions rubi1212r39.body rubi1212r39.result rubi1212r39.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "b" ∨ s = "d" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi1212r39, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1212r39, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r39.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "b" ∨ s = "d" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r39, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r39, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r4_counterexample_real : ¬ rubi1212r4.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1212r4.conditions rubi1212r4.body rubi1212r4.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1212r4, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1212r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1212r4_counterexample_complex : ¬ rubi1212r4.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1212r4.conditions rubi1212r4.body rubi1212r4.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1212r4, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1212r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1212r40_counterexample_real : ¬ rubi1212r40.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r40.conditions rubi1212r40.body rubi1212r40.result rubi1212r40.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi1212r40, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r40, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r40.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r40, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r40, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r40_counterexample_complex : ¬ rubi1212r40.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r40.conditions rubi1212r40.body rubi1212r40.result rubi1212r40.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi1212r40, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r40, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r40.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r40, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r40, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r41_counterexample_real : ¬ rubi1212r41.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r41.conditions rubi1212r41.body rubi1212r41.result rubi1212r41.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "b" ∨ s = "e" ∨ s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi1212r41, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1212r41, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r41.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "b" ∨ s = "e" ∨ s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r41, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r41, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r41_counterexample_complex : ¬ rubi1212r41.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r41.conditions rubi1212r41.body rubi1212r41.result rubi1212r41.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "b" ∨ s = "e" ∨ s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi1212r41, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1212r41, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r41.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "b" ∨ s = "e" ∨ s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r41, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r41, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r42_counterexample_real : ¬ rubi1212r42.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r42.conditions rubi1212r42.body rubi1212r42.result rubi1212r42.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi1212r42, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r42, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r42.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r42, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r42_counterexample_complex : ¬ rubi1212r42.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r42.conditions rubi1212r42.body rubi1212r42.result rubi1212r42.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi1212r42, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r42, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r42.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r42, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r43_counterexample_real : ¬ rubi1212r43.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r43.conditions rubi1212r43.body rubi1212r43.result rubi1212r43.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "p" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi1212r43, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r43, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r43.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "p" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r43, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r43, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r43_counterexample_complex : ¬ rubi1212r43.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r43.conditions rubi1212r43.body rubi1212r43.result rubi1212r43.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "p" then 1 else if s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi1212r43, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r43, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r43.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "p" then 1 else if s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r43, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r43, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r44_counterexample_real : ¬ rubi1212r44.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r44.conditions rubi1212r44.body rubi1212r44.result rubi1212r44.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "e" ∨ s = "p" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi1212r44, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r44, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r44.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "e" ∨ s = "p" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r44, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r44, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r44_counterexample_complex : ¬ rubi1212r44.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r44.conditions rubi1212r44.body rubi1212r44.result rubi1212r44.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "e" ∨ s = "p" then 1 else if s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi1212r44, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r44, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r44.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "e" ∨ s = "p" then 1 else if s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r44, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r44, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r45_counterexample_real : ¬ rubi1212r45.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r45.conditions rubi1212r45.body rubi1212r45.result rubi1212r45.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1212r45, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r45, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r45.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r45, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r45, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r45_counterexample_complex : ¬ rubi1212r45.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r45.conditions rubi1212r45.body rubi1212r45.result rubi1212r45.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1212r45, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r45, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r45.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r45, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r45, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r46_counterexample_real : ¬ rubi1212r46.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r46.conditions rubi1212r46.body rubi1212r46.result rubi1212r46.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1212r46, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r46, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r46.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r46, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r46, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r46_counterexample_complex : ¬ rubi1212r46.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r46.conditions rubi1212r46.body rubi1212r46.result rubi1212r46.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "d" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1212r46, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r46, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1212r46.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -3 else if s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r46, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r46, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1212r5_counterexample_real : ¬ rubi1212r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r5.conditions rubi1212r5.body rubi1212r5.result rubi1212r5.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1212r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1212r5.integrals[0]!, by simp [rubi1212r5], ?_⟩
  intro h
  simp [rubi1212r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1212r5_counterexample_complex : ¬ rubi1212r5.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r5.conditions rubi1212r5.body rubi1212r5.result rubi1212r5.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1212r5, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1212r5.integrals[0]!, by simp [rubi1212r5], ?_⟩
  intro h
  simp [rubi1212r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1212r55_counterexample_real : ¬ rubi1212r55.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1212r55.conditions rubi1212r55.body rubi1212r55.result
  refine not_antiderivHoldsUnder (fun s => if s = "m" then -3 else if s = "a" ∨ s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi1212r55, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r55, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1212r55, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1212r55_counterexample_complex : ¬ rubi1212r55.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1212r55.conditions rubi1212r55.body rubi1212r55.result
  refine not_antiderivHoldsUnder (fun s => if s = "m" then -3 else if s = "a" ∨ s = "b" ∨ s = "d" then 1 else 0) (1 : ℂ) (by simp [rubi1212r55, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1212r55, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1212r55, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r1_counterexample_real : ¬ rubi1213r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1213r1.conditions rubi1213r1.body rubi1213r1.result
  refine not_antiderivHoldsUnder (fun s => if s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1213r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1213r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r1_counterexample_complex : ¬ rubi1213r1.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1213r1.conditions rubi1213r1.body rubi1213r1.result
  refine not_antiderivHoldsUnder (fun s => if s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1213r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1213r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r13_counterexample_real : ¬ rubi1213r13.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1213r13.conditions rubi1213r13.body rubi1213r13.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1213r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1213r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r13_counterexample_complex : ¬ rubi1213r13.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1213r13.conditions rubi1213r13.body rubi1213r13.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1213r13, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1213r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r14_counterexample_real : ¬ rubi1213r14.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1213r14.conditions rubi1213r14.body rubi1213r14.result
  refine not_antiderivHoldsUnder (fun s => if s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1213r14, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1213r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r14_counterexample_complex : ¬ rubi1213r14.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1213r14.conditions rubi1213r14.body rubi1213r14.result
  refine not_antiderivHoldsUnder (fun s => if s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1213r14, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1213r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r20_counterexample_real : ¬ rubi1213r20.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1213r20.conditions rubi1213r20.body rubi1213r20.result rubi1213r20.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1213r20, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1213r20.integrals[0]!, by simp [rubi1213r20], ?_⟩
  intro h
  simp [rubi1213r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r20_counterexample_complex : ¬ rubi1213r20.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1213r20.conditions rubi1213r20.body rubi1213r20.result rubi1213r20.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1213r20, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r20, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1213r20.integrals[0]!, by simp [rubi1213r20], ?_⟩
  intro h
  simp [rubi1213r20, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r24_counterexample_real : ¬ rubi1213r24.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1213r24.conditions rubi1213r24.body rubi1213r24.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1213r24, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r24, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1213r24, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r24_counterexample_complex : ¬ rubi1213r24.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1213r24.conditions rubi1213r24.body rubi1213r24.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1213r24, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r24, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1213r24, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r25_counterexample_real : ¬ rubi1213r25.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1213r25.conditions rubi1213r25.body rubi1213r25.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" then -3 else if s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi1213r25, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r25, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1213r25, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r25_counterexample_complex : ¬ rubi1213r25.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1213r25.conditions rubi1213r25.body rubi1213r25.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" then -3 else if s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi1213r25, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r25, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1213r25, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r26_counterexample_real : ¬ rubi1213r26.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1213r26.conditions rubi1213r26.body rubi1213r26.result rubi1213r26.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi1213r26, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1213r26, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1213r26.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r26, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1213r26_counterexample_complex : ¬ rubi1213r26.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1213r26.conditions rubi1213r26.body rubi1213r26.result rubi1213r26.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi1213r26, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1213r26, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1213r26.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r26, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1213r27_counterexample_real : ¬ rubi1213r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1213r27.conditions rubi1213r27.body rubi1213r27.result rubi1213r27.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi1213r27, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1213r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1213r27_counterexample_complex : ¬ rubi1213r27.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1213r27.conditions rubi1213r27.body rubi1213r27.result rubi1213r27.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi1213r27, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r27, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1213r27.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r27, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1213r33_counterexample_real : ¬ rubi1213r33.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1213r33.conditions rubi1213r33.body rubi1213r33.result rubi1213r33.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1213r33, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1213r33.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1213r33_counterexample_complex : ¬ rubi1213r33.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1213r33.conditions rubi1213r33.body rubi1213r33.result rubi1213r33.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1213r33, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r33, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1213r33.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r33, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1213r35_counterexample_real : ¬ rubi1213r35.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1213r35.conditions rubi1213r35.body rubi1213r35.result rubi1213r35.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "g" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1213r35, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r35, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1213r35.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "g" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r35, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r35, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1213r35_counterexample_complex : ¬ rubi1213r35.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1213r35.conditions rubi1213r35.body rubi1213r35.result rubi1213r35.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "g" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1213r35, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r35, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1213r35.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "g" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r35, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r35, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1213r36_counterexample_real : ¬ rubi1213r36.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1213r36.conditions rubi1213r36.body rubi1213r36.result rubi1213r36.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "d" ∨ s = "e" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1213r36, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r36, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1213r36.integrals[0]!, by simp [rubi1213r36], ?_⟩
  intro h
  simp [rubi1213r36, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r36_counterexample_complex : ¬ rubi1213r36.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1213r36.conditions rubi1213r36.body rubi1213r36.result rubi1213r36.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "d" ∨ s = "e" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1213r36, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r36, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1213r36.integrals[0]!, by simp [rubi1213r36], ?_⟩
  intro h
  simp [rubi1213r36, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r5_counterexample_real : ¬ rubi1213r5.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1213r5.conditions rubi1213r5.body rubi1213r5.result
  refine not_antiderivHoldsUnder (fun s => if s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi1213r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1213r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r5_counterexample_complex : ¬ rubi1213r5.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1213r5.conditions rubi1213r5.body rubi1213r5.result
  refine not_antiderivHoldsUnder (fun s => if s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi1213r5, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1213r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1213r6_counterexample_real : ¬ rubi1213r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1213r6.conditions rubi1213r6.body rubi1213r6.result rubi1213r6.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi1213r6, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1213r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1213r6_counterexample_complex : ¬ rubi1213r6.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1213r6.conditions rubi1213r6.body rubi1213r6.result rubi1213r6.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi1213r6, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1213r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1213r6.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1213r7_counterexample_real : ¬ rubi1213r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1213r7.conditions rubi1213r7.body rubi1213r7.result rubi1213r7.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then -1 else 0) (1 : ℝ) (by simp [rubi1213r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1213r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1213r7.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then -1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1213r7_counterexample_complex : ¬ rubi1213r7.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1213r7.conditions rubi1213r7.body rubi1213r7.result rubi1213r7.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then -1 else 0) (1 : ℂ) (by simp [rubi1213r7, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1213r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi1213r7.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then -1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1213r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1213r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi1214r1_counterexample_real : ¬ rubi1214r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1214r1.conditions rubi1214r1.body rubi1214r1.result
  refine not_antiderivHoldsUnder (fun s => if s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi1214r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1214r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1214r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1214r1_counterexample_complex : ¬ rubi1214r1.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1214r1.conditions rubi1214r1.body rubi1214r1.result
  refine not_antiderivHoldsUnder (fun s => if s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi1214r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1214r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1214r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1214r65_counterexample_real : ¬ rubi1214r65.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1214r65.conditions rubi1214r65.body rubi1214r65.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1214r65, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1214r65, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1214r65, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1214r65_counterexample_complex : ¬ rubi1214r65.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1214r65.conditions rubi1214r65.body rubi1214r65.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1214r65, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1214r65, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1214r65, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1214r66_counterexample_real : ¬ rubi1214r66.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1214r66.conditions rubi1214r66.body rubi1214r66.result
  refine not_antiderivHoldsUnder (fun s => if s = "e" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1214r66, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1214r66, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1214r66, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1214r66_counterexample_complex : ¬ rubi1214r66.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1214r66.conditions rubi1214r66.body rubi1214r66.result
  refine not_antiderivHoldsUnder (fun s => if s = "e" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1214r66, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1214r66, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi1214r66, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1216r10_counterexample_real : ¬ rubi1216r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1216r10.conditions rubi1216r10.body rubi1216r10.result rubi1216r10.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "f" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi1216r10, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1216r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1216r10.integrals[0]!, by simp [rubi1216r10], ?_⟩
  intro h
  simp [rubi1216r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1216r10_counterexample_complex : ¬ rubi1216r10.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1216r10.conditions rubi1216r10.body rubi1216r10.result rubi1216r10.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "f" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℂ) (by simp [rubi1216r10, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1216r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1216r10.integrals[0]!, by simp [rubi1216r10], ?_⟩
  intro h
  simp [rubi1216r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1216r5_counterexample_real : ¬ rubi1216r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1216r5.conditions rubi1216r5.body rubi1216r5.result rubi1216r5.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1216r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1216r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1216r5.integrals[0]!, by simp [rubi1216r5], ?_⟩
  intro h
  simp [rubi1216r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1216r5_counterexample_complex : ¬ rubi1216r5.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1216r5.conditions rubi1216r5.body rubi1216r5.result rubi1216r5.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1216r5, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1216r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1216r5.integrals[0]!, by simp [rubi1216r5], ?_⟩
  intro h
  simp [rubi1216r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1216r6_counterexample_real : ¬ rubi1216r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1216r6.conditions rubi1216r6.body rubi1216r6.result rubi1216r6.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1216r6, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1216r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1216r6.integrals[0]!, by simp [rubi1216r6], ?_⟩
  intro h
  simp [rubi1216r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1216r6_counterexample_complex : ¬ rubi1216r6.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1216r6.conditions rubi1216r6.body rubi1216r6.result rubi1216r6.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1216r6, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1216r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1216r6.integrals[0]!, by simp [rubi1216r6], ?_⟩
  intro h
  simp [rubi1216r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1216r7_counterexample_real : ¬ rubi1216r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1216r7.conditions rubi1216r7.body rubi1216r7.result rubi1216r7.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1216r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1216r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1216r7.integrals[0]!, by simp [rubi1216r7], ?_⟩
  intro h
  simp [rubi1216r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1216r7_counterexample_complex : ¬ rubi1216r7.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1216r7.conditions rubi1216r7.body rubi1216r7.result rubi1216r7.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1216r7, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1216r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1216r7.integrals[0]!, by simp [rubi1216r7], ?_⟩
  intro h
  simp [rubi1216r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1216r8_counterexample_real : ¬ rubi1216r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1216r8.conditions rubi1216r8.body rubi1216r8.result rubi1216r8.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1216r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1216r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1216r8.integrals[0]!, by simp [rubi1216r8], ?_⟩
  intro h
  simp [rubi1216r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1216r8_counterexample_complex : ¬ rubi1216r8.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1216r8.conditions rubi1216r8.body rubi1216r8.result rubi1216r8.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1216r8, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1216r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1216r8.integrals[0]!, by simp [rubi1216r8], ?_⟩
  intro h
  simp [rubi1216r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1216r9_counterexample_real : ¬ rubi1216r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1216r9.conditions rubi1216r9.body rubi1216r9.result rubi1216r9.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "f" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi1216r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1216r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1216r9.integrals[0]!, by simp [rubi1216r9], ?_⟩
  intro h
  simp [rubi1216r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1216r9_counterexample_complex : ¬ rubi1216r9.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1216r9.conditions rubi1216r9.body rubi1216r9.result rubi1216r9.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "f" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℂ) (by simp [rubi1216r9, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1216r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1216r9.integrals[0]!, by simp [rubi1216r9], ?_⟩
  intro h
  simp [rubi1216r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

end OSR.IntegrationRec13
