import OSR.IntegrationRec28

/-!
# Integration (RUBI): a wider pass over the registered-head rules

An inventory of the RUBI 4.16.1 rules whose heads are all registered, whose
conditions are expressible (FreeQ, NeQ, EqQ, GtQ, LtQ, IntegerQ, IntegersQ,
IGtQ, ILtQ) and whose metavariables are independent of `x` found 213 rules not
yet considered.  The numerical search proposed a counterexample for 69 of them (39 kept here; the
refutations of 22 rules using `Sqrt` wait for the converter's `arith1#root`
convention);
each refutation below is a Lean theorem, stated per domain.  Variables that
RUBI constrains by numeric predicates but does not list in `FreeQ` are
declared independent of `x`, with an `independence:` finding.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec29

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.1.1.4 #44 -/
def rubi1114r44 : CRule where
  id := "integration.rubi_1_1_1_4_r44"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:44"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "i") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "q"))) (.var "r"))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "i") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "q"))) (.var "r")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "m") (.var "r"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .mul (.var "n") (.var "r")))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .mul (.var "p") (.var "r")))) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .mul (.var "q") (.var "r")))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "m") (.var "r"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .mul (.var "n") (.var "r")))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .mul (.var "p") (.var "r")))) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .mul (.var "q") (.var "r")))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "m", "n", "p", "q", "r"]
  priority := 5000
  description := "RUBI 1.1.1.4 #44"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:44" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#44"

/-- RUBI 1.1.3.3 #11 -/
def rubi1133r11 : CRule where
  id := "integration.rubi_1_1_3_3_r11"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:11"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "non2")))) (.var "p")) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "non2")))) (.var "p"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "a1") (.var "a2")) (.int (-1))))
  independent := ["a1", "b1", "a2", "b2", "c", "d", "n", "p", "non2"]
  conditions := [.eq (.var "non2") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1)))),
    .eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a1") (.var "a2")) (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b1")) (.var "b2")) (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0)]
  priority := 5010
  description := "RUBI 1.1.3.3 #11"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:11" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#11"

/-- RUBI 1.1.3.3 #15 -/
def rubi1133r15 : CRule where
  id := "integration.rubi_1_1_3_3_r15"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))))) (.pow (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)) (.int 0)]
  priority := 5020
  description := "RUBI 1.1.3.3 #15"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:15" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#15"

/-- RUBI 1.1.3.3 #16 -/
def rubi1133r16 : CRule where
  id := "integration.rubi_1_1_3_3_r16"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "non2")))) (.var "p")) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "non2")))) (.var "p"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b1") (.var "b2")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "a1") (.var "a2")) (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b1")) (.var "b2")) (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b1") (.var "b2")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.var "p")) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.var "p"))))]
  independent := ["a1", "b1", "a2", "b2", "c", "d", "n", "p", "non2"]
  conditions := [.eq (.var "non2") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1)))),
    .eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)) (.int 0)]
  priority := 5030
  description := "RUBI 1.1.3.3 #16"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:16" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#16"

/-- RUBI 1.1.3.4 #15 -/
def rubi1134r15 : CRule where
  id := "integration.rubi_1_1_3_4_r15"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:15"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "non2")))) (.var "p"))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "non2")))) (.var "p"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a1") (.var "a2")) (.var "e")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a1", "b1", "a2", "b2", "c", "d", "e", "m", "n", "p", "non2"]
  conditions := [.eq (.var "non2") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1)))),
    .eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a1") (.var "a2")) (.var "d")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b1")) (.var "b2")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)))) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 5040
  description := "RUBI 1.1.3.4 #15"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:15" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#15"

/-- RUBI 1.1.3.4 #25 -/
def rubi1134r25 : CRule where
  id := "integration.rubi_1_1_3_4_r25"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "non2")))) (.var "p"))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "non2")))) (.var "p"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b1") (.var "b2")) (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a1") (.var "a2")) (.var "d")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b1")) (.var "b2")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b1") (.var "b2")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.var "p"))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.var "p"))))]
  independent := ["a1", "b1", "a2", "b2", "c", "d", "e", "m", "n", "p", "non2"]
  conditions := [.eq (.var "non2") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1)))),
    .eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)) (.int 0)]
  priority := 5050
  description := "RUBI 1.1.3.4 #25"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:25" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#25"

/-- RUBI 1.1.3.5 #30 -/
def rubi1135r30 : CRule where
  id := "integration.rubi_1_1_3_5_r30"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r"))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "r", "p", "q"]
  conditions := [.int (.var "p"),
    .gt (.int 0) (.var "p"),
    .gt (.var "q") (.int 0)]
  priority := 5110
  description := "RUBI 1.1.3.5 #30"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:30" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#30"

/-- RUBI 1.1.3.6 #28 -/
def rubi1136r28 : CRule where
  id := "integration.rubi_1_1_3_6_r28"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:28"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.var "e") (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m"))) (.pow (.pow (.var "x") (.var "m")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "p", "q"]
  priority := 5120
  description := "RUBI 1.1.3.6 #28"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:28" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#28"

/-- RUBI 1.1.3.7 #16 -/
def rubi1137r16 : CRule where
  id := "integration.rubi_1_1_3_7_r16"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p:16"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "g") (.pow (.var "x") (.var "n2")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "a") (.var "c")) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "g", "n", "p", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d")))) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e")) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0)]
  priority := 5130
  description := "RUBI 1.1.3.7 #16"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p:16" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p.m#16"

/-- RUBI 1.1.3.7 #17 -/
def rubi1137r17 : CRule where
  id := "integration.rubi_1_1_3_7_r17"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p:17"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "e") (.app2 .mul (.var "g") (.pow (.var "x") (.var "n2")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "a") (.var "c")) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "g", "n", "p", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e")) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0)]
  priority := 5140
  description := "RUBI 1.1.3.7 #17"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p:17" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.7 P(x) (a+b x^n)^p.m#17"

/-- RUBI 1.1.3.8 #18 -/
def rubi1138r18 : CRule where
  id := "integration.rubi_1_1_3_8_r18"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.8 P(x) (c x)^m (a+b x^n)^p:18"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "h") (.var "x")) (.var "m")) (.app2 .add (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "g") (.pow (.var "x") (.var "n2"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .mul (.var "h") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "n", "p", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d")))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "g")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1)))) (.int 1)))) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 5150
  description := "RUBI 1.1.3.8 #18"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.8 P(x) (c x)^m (a+b x^n)^p:18" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.8 P(x) (c x)^m (a+b x^n)^p.m#18"

/-- RUBI 1.1.3.8 #19 -/
def rubi1138r19 : CRule where
  id := "integration.rubi_1_1_3_8_r19"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.8 P(x) (c x)^m (a+b x^n)^p:19"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "h") (.var "x")) (.var "m")) (.app2 .add (.var "e") (.app2 .mul (.var "g") (.pow (.var "x") (.var "n2"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .mul (.var "h") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "g", "h", "m", "n", "p", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "g")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1)))) (.int 1)))) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 5160
  description := "RUBI 1.1.3.8 #19"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.8 P(x) (c x)^m (a+b x^n)^p:19" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.8 P(x) (c x)^m (a+b x^n)^p.m#19"

/-- RUBI 1.2.1.2 #96 -/
def rubi1212r96 : CRule where
  id := "integration.rubi_1_2_1_2_r96"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:96"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0),
    .gt (.int (-1)) (.var "p")]
  priority := 5190
  description := "RUBI 1.2.1.2 #96"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:96" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#96"

/-- RUBI 1.2.3.1 #3 -/
def rubi1231r3 : CRule where
  id := "integration.rubi_1_2_3_1_r3"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p:3"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p"))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p")) (.pow (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.var "x") (.var "n")))) (.app2 .mul (.int 2) (.var "p"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.var "x") (.var "n")))) (.app2 .mul (.int 2) (.var "p"))))]
  independent := ["a", "b", "c", "n", "p", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)]
  priority := 5260
  description := "RUBI 1.2.3.1 #3"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p:3" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p.m#3"

/-- RUBI 1.2.3.1 #5 -/
def rubi1231r5 : CRule where
  id := "integration.rubi_1_2_3_1_r5"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p:5"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.app2 .add (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c"))) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c"))) (.app2 .mul (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 1))) (.pow (.var "x") (.var "n")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "p"),
    .gt (.int (-1)) (.var "p")]
  priority := 5270
  description := "RUBI 1.2.3.1 #5"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p:5" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p.m#5"

/-- RUBI 1.2.3.2 #10 -/
def rubi1232r10 : CRule where
  id := "integration.rubi_1_2_3_2_r10"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.var "d") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "n") (.var "p")) (.pow (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1)) (.int 0)]
  priority := 5280
  description := "RUBI 1.2.3.2 #10"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:10" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p.m#10"

/-- RUBI 1.2.3.2 #18 -/
def rubi1232r18 : CRule where
  id := "integration.rubi_1_2_3_2_r18"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "d") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.app2 .mul (.int 2) (.var "n")))) (.pow (.var "c") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))]
  priority := 5290
  description := "RUBI 1.2.3.2 #18"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:18" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p.m#18"

/-- RUBI 1.2.3.3 #11 -/
def rubi1233r11 : CRule where
  id := "integration.rubi_1_2_3_3_r11"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.var "q"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.var "n")))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "q", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 5300
  description := "RUBI 1.2.3.3 #11"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:11" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#11"

/-- RUBI 1.2.3.3 #12 -/
def rubi1233r12 : CRule where
  id := "integration.rubi_1_2_3_3_r12"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.var "q"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.var "n")))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "n", "q", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 5310
  description := "RUBI 1.2.3.3 #12"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:12" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#12"

/-- RUBI 1.2.3.3 #19 -/
def rubi1233r19 : CRule where
  id := "integration.rubi_1_2_3_3_r19"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "n", "q", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)]
  priority := 5320
  description := "RUBI 1.2.3.3 #19"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:19" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#19"

/-- RUBI 1.2.3.3 #20 -/
def rubi1233r20 : CRule where
  id := "integration.rubi_1_2_3_3_r20"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "c", "d", "e", "n", "q", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)]
  priority := 5330
  description := "RUBI 1.2.3.3 #20"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:20" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#20"

/-- RUBI 1.2.3.3 #27 -/
def rubi1233r27 : CRule where
  id := "integration.rubi_1_2_3_3_r27"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.app2 .mul (.int 2) (.var "n"))) (.int 1))) (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.app2 .mul (.int 3) (.var "n"))) (.int 1))) (.pow (.var "x") (.var "n")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "c", "d", "e", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .int (.var "p"),
    .gt (.int (-1)) (.var "p")]
  priority := 5340
  description := "RUBI 1.2.3.3 #27"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:27" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#27"

/-- RUBI 1.2.3.3 #50 -/
def rubi1233r50 : CRule where
  id := "integration.rubi_1_2_3_3_r50"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:50"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.var "n")))) (.var "r"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.var "q"))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.var "n")))) (.var "r"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.var "n")))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "n", "q", "r", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 5350
  description := "RUBI 1.2.3.3 #50"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:50" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#50"

/-- RUBI 1.2.3.3 #51 -/
def rubi1233r51 : CRule where
  id := "integration.rubi_1_2_3_3_r51"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:51"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.var "n")))) (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.var "q"))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.var "n")))) (.var "r"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.var "n")))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "f", "g", "n", "q", "r", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 5360
  description := "RUBI 1.2.3.3 #51"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:51" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#51"

/-- RUBI 1.2.3.4 #17 -/
def rubi1234r17 : CRule where
  id := "integration.rubi_1_2_3_4_r17"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.var "p")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.var "n")))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 5370
  description := "RUBI 1.2.3.4 #17"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:17" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#17"

/-- RUBI 1.2.3.4 #18 -/
def rubi1234r18 : CRule where
  id := "integration.rubi_1_2_3_4_r18"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.var "p")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.var "n")))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "f", "q", "m", "n", "q", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 5380
  description := "RUBI 1.2.3.4 #18"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:18" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#18"

/-- RUBI 1.2.3.4 #38 -/
def rubi1234r38 : CRule where
  id := "integration.rubi_1_2_3_4_r38"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:38"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.var "f") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.var "n"))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "c", "d", "e", "f", "p", "m", "n", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1)) (.int 0),
    .int (.var "p")]
  priority := 5390
  description := "RUBI 1.2.3.4 #38"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:38" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#38"

/-- RUBI 1.2.3.5 #2 -/
def rubi1235r2 : CRule where
  id := "integration.rubi_1_2_3_5_r2"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:2"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "f") (.pow (.var "x") (.var "n2")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.var "a") (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "n", "p", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "a") (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0)]
  priority := 5400
  description := "RUBI 1.2.3.5 #2"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:2" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p.m#2"

/-- RUBI 1.2.3.5 #3 -/
def rubi1235r3 : CRule where
  id := "integration.rubi_1_2_3_5_r3"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:3"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n2")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.var "a") (.int (-1))))
  independent := ["a", "b", "c", "d", "f", "n", "p", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.var "a") (.var "f"))) (.int 0)]
  priority := 5410
  description := "RUBI 1.2.3.5 #3"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:3" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p.m#3"

/-- RUBI 1.2.3.6 #3 -/
def rubi1236r3 : CRule where
  id := "integration.rubi_1_2_3_6_r3"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.6 P(x) (d x)^m (a+b x^n+c x^(2 n))^p:3"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "f") (.pow (.var "x") (.var "n2"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "g")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "p", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1)))) (.int 1)))) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 5420
  description := "RUBI 1.2.3.6 #3"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.6 P(x) (d x)^m (a+b x^n+c x^(2 n))^p:3" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.6 P(x) (d x)^m (a+b x^n+c x^(2 n))^p.m#3"

/-- RUBI 1.2.3.6 #4 -/
def rubi1236r4 : CRule where
  id := "integration.rubi_1_2_3_6_r4"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.6 P(x) (d x)^m (a+b x^n+c x^(2 n))^p:4"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n2"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "g")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "f", "g", "m", "n", "p", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.var "a") (.var "f"))) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 5430
  description := "RUBI 1.2.3.6 #4"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.6 P(x) (d x)^m (a+b x^n+c x^(2 n))^p:4" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.6 P(x) (d x)^m (a+b x^n+c x^(2 n))^p.m#4"

/-- RUBI 2.1 #7 -/
def rubi21r7 : CRule where
  id := "integration.rubi_2_1_r7"; legacyId := some "rubi:2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .mul (.var "b") (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "b") (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n")) (.pow (.pow (.var "F") (.app2 .mul (.app2 .mul (.var "g") (.var "n")) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .mul (.app2 .mul (.var "g") (.var "n")) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))]
  independent := ["F", "b", "c", "d", "e", "f", "g", "m", "n"]
  priority := 5480
  description := "RUBI 2.1 #7"
  provenance := migrated "rubi:2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p:7" "2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p.m#7"

/-- RUBI 2.3 #13 -/
def rubi23r13 : CRule where
  id := "integration.rubi_2_3_r13"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:13"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))))))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "n")) (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "n")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.app1 .ln (.var "F"))) (.int (-1))))
  independent := ["F", "a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .eq (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.int 0)]
  priority := 5490
  description := "RUBI 2.3 #13"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:13" "2 Exponentials/2.3 Miscellaneous exponentials.m#13"

/-- RUBI 2.3 #37 -/
def rubi23r37 : CRule where
  id := "integration.rubi_2_3_r37"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:37"
  shape := .antiderivRec; x := "x"
  body := (.pow (.var "F") (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))
  result := (.app2 .mul (.pow (.var "F") (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1)))))) (.var "I1"))
  integrals := [("I1", (.pow (.var "F") (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))))]
  independent := ["F", "a", "b", "c"]
  priority := 5500
  description := "RUBI 2.3 #37"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:37" "2 Exponentials/2.3 Miscellaneous exponentials.m#37"

/-- RUBI 3.1.2 #11 -/
def rubi312r11 : CRule where
  id := "integration.rubi_3_1_2_r11"; legacyId := some "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.pow (.var "x") (.var "q"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.pow (.var "x") (.var "q"))) (.var "m")) (.pow (.pow (.var "x") (.app2 .mul (.var "m") (.var "q"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .mul (.var "m") (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "m", "n", "p", "q"]
  priority := 5520
  description := "RUBI 3.1.2 #11"
  provenance := migrated "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:11" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#11"

/-- RUBI 3.2.1 #12 -/
def rubi321r12 : CRule where
  id := "integration.rubi_3_2_1_r12"; legacyId := some "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "mn")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.int (-1)))))))) (.pow (.var "g") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B")) (.var "n")) (.pow (.var "g") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "B") (.var "d")) (.var "n")) (.pow (.var "g") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "A", "B", "n", "mn"]
  conditions := [.eq (.app2 .add (.var "n") (.var "mn")) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 5550
  description := "RUBI 3.2.1 #12"
  provenance := migrated "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:12" "3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.m#12"

/-- RUBI 3.2.1 #2 -/
def rubi321r2 : CRule where
  id := "integration.rubi_3_2_1_r2"; legacyId := some "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:2"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "mn")))))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.int (-1))))))) (.var "p"))) (.pow (.var "b") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "n")) (.var "p")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "b") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.int (-1))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "n", "mn", "p"]
  conditions := [.eq (.app2 .add (.var "n") (.var "mn")) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 5560
  description := "RUBI 3.2.1 #2"
  provenance := migrated "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:2" "3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.m#2"

/-- RUBI 3.2.2 #17 -/
def rubi322r17 : CRule where
  id := "integration.rubi_3_2_2_r17"; legacyId := some "rubi:3 Logarithms/3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .mul (.var "h") (.pow (.var "x") (.int 2)))) (.var "m")) (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "mn")))))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.var "h") (.var "m")) (.pow (.app2 .mul (.pow (.var "b") (.var "m")) (.pow (.var "d") (.var "m"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.int (-1))))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "A", "B", "n", "p", "m", "mn"]
  conditions := [.eq (.app2 .add (.var "n") (.var "mn")) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "h"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "h")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))))) (.int 0),
    .int (.var "m")]
  priority := 5570
  description := "RUBI 3.2.2 #17"
  provenance := migrated "rubi:3 Logarithms/3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p:17" "3 Logarithms/3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p.m#17"

/-- RUBI 3.5 #8 -/
def rubi35r8 : CRule where
  id := "integration.rubi_3_5_r8"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app1 .ln (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.var "n"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .ln (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.var "n")))))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "e") (.pow (.var "d") (.int (-1)))) (.pow (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.var "n")))))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int (-1))))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "e") (.pow (.var "d") (.int (-1)))) (.pow (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.var "n")))))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "n", "m"]
  conditions := [.gt (.var "m") (.int 0),
    .ne (.var "d") (.int 1)]
  priority := 5620
  description := "RUBI 3.5 #8"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:8" "3 Logarithms/3.5 Miscellaneous logarithms.m#8"

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
private theorem ivexnat (n : ℕ) [n.AtLeastTwo] : ∃ k, intValue? (OfNat.ofNat n : α) = some k :=
  ⟨_, ivnat n⟩
private theorem ivexneg (n : ℕ) [n.AtLeastTwo] : ∃ k, intValue? (-(OfNat.ofNat n : α)) = some k :=
  ⟨_, ivneg n⟩
end

theorem rubi1114r44_counterexample_real : ¬ rubi1114r44.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1114r44.conditions rubi1114r44.body rubi1114r44.result rubi1114r44.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "i" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "r" then 1 else 0) (1 : ℝ) (by simp [rubi1114r44, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1114r44, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1114r44.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "i" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "r" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1114r44, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1114r44, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1114r44_counterexample_complex : ¬ rubi1114r44.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1114r44.conditions rubi1114r44.body rubi1114r44.result rubi1114r44.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "i" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "r" then 1 else 0) (1 : ℂ) (by simp [rubi1114r44, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1114r44, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1114r44.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "i" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "r" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1114r44, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1114r44, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1133r11_counterexample_real : ¬ rubi1133r11.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1133r11.conditions rubi1133r11.body rubi1133r11.result
  refine not_antiderivHoldsUnder (fun s => if s = "b2" ∨ s = "c" ∨ s = "d" ∨ s = "non2" ∨ s = "p" then 1 else if s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi1133r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1133r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1133r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1133r11_counterexample_complex : ¬ rubi1133r11.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1133r11.conditions rubi1133r11.body rubi1133r11.result
  refine not_antiderivHoldsUnder (fun s => if s = "b2" ∨ s = "c" ∨ s = "d" ∨ s = "non2" ∨ s = "p" then 1 else if s = "n" then 2 else 0) (1 : ℂ) (by simp [rubi1133r11, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1133r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1133r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1133r15_counterexample_real : ¬ rubi1133r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1133r15.conditions rubi1133r15.body rubi1133r15.result rubi1133r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1133r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1133r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1133r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1133r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1133r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1133r15_counterexample_complex : ¬ rubi1133r15.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1133r15.conditions rubi1133r15.body rubi1133r15.result rubi1133r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1133r15, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1133r15, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1133r15.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1133r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1133r15, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1133r16_counterexample_real : ¬ rubi1133r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1133r16.conditions rubi1133r16.body rubi1133r16.result rubi1133r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b2" ∨ s = "c" ∨ s = "d" ∨ s = "non2" ∨ s = "p" then 1 else if s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi1133r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1133r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1133r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b2" ∨ s = "c" ∨ s = "d" ∨ s = "non2" ∨ s = "p" then 1 else if s = "n" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1133r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1133r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1133r16_counterexample_complex : ¬ rubi1133r16.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1133r16.conditions rubi1133r16.body rubi1133r16.result rubi1133r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b2" ∨ s = "c" ∨ s = "d" ∨ s = "non2" ∨ s = "p" then 1 else if s = "n" then 2 else 0) (1 : ℂ) (by simp [rubi1133r16, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1133r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1133r16.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b2" ∨ s = "c" ∨ s = "d" ∨ s = "non2" ∨ s = "p" then 1 else if s = "n" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1133r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1133r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1134r15_counterexample_real : ¬ rubi1134r15.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1134r15.conditions rubi1134r15.body rubi1134r15.result
  refine not_antiderivHoldsUnder (fun s => if s = "b2" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "non2" ∨ s = "p" then 1 else if s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi1134r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1134r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1134r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1134r15_counterexample_complex : ¬ rubi1134r15.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1134r15.conditions rubi1134r15.body rubi1134r15.result
  refine not_antiderivHoldsUnder (fun s => if s = "b2" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "non2" ∨ s = "p" then 1 else if s = "n" then 2 else 0) (1 : ℂ) (by simp [rubi1134r15, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1134r15, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1134r15, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1134r25_counterexample_real : ¬ rubi1134r25.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1134r25.conditions rubi1134r25.body rubi1134r25.result rubi1134r25.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b2" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "non2" ∨ s = "p" then 1 else if s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi1134r25, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1134r25, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1134r25.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b2" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "non2" ∨ s = "p" then 1 else if s = "n" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1134r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1134r25, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1134r25_counterexample_complex : ¬ rubi1134r25.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1134r25.conditions rubi1134r25.body rubi1134r25.result rubi1134r25.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b2" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "non2" ∨ s = "p" then 1 else if s = "n" then 2 else 0) (1 : ℂ) (by simp [rubi1134r25, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1134r25, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1134r25.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b2" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "non2" ∨ s = "p" then 1 else if s = "n" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1134r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1134r25, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1135r30_counterexample_real : ¬ rubi1135r30.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1135r30.conditions rubi1135r30.body rubi1135r30.result rubi1135r30.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "n" ∨ s = "q" ∨ s = "r" then 1 else 0) (1 : ℝ) (by simp [rubi1135r30, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1135r30, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1135r30.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "n" ∨ s = "q" ∨ s = "r" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r30, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1135r30_counterexample_complex : ¬ rubi1135r30.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1135r30.conditions rubi1135r30.body rubi1135r30.result rubi1135r30.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "n" ∨ s = "q" ∨ s = "r" then 1 else 0) (1 : ℂ) (by simp [rubi1135r30, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1135r30, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1135r30.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "n" ∨ s = "q" ∨ s = "r" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r30, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1136r28_counterexample_real : ¬ rubi1136r28.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1136r28.conditions rubi1136r28.body rubi1136r28.result rubi1136r28.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else 0) (0 : ℝ) (by simp [rubi1136r28, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1136r28, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1136r28.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else 0) "x" (0 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1136r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1136r28, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1136r28_counterexample_complex : ¬ rubi1136r28.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1136r28.conditions rubi1136r28.body rubi1136r28.result rubi1136r28.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else 0) (0 : ℂ) (by simp [rubi1136r28, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1136r28, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1136r28.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else 0) "x" (0 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1136r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1136r28, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1137r16_counterexample_real : ¬ rubi1137r16.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1137r16.conditions rubi1137r16.body rubi1137r16.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1137r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1137r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1137r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1137r16_counterexample_complex : ¬ rubi1137r16.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1137r16.conditions rubi1137r16.body rubi1137r16.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1137r16, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1137r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1137r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1137r17_counterexample_real : ¬ rubi1137r17.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1137r17.conditions rubi1137r17.body rubi1137r17.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "g" ∨ s = "n" then -1 else if s = "n2" then -2 else 0) (1 : ℝ) (by simp [rubi1137r17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1137r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, hw] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1137r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1137r17_counterexample_complex : ¬ rubi1137r17.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1137r17.conditions rubi1137r17.body rubi1137r17.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "g" ∨ s = "n" then -1 else if s = "n2" then -2 else 0) (1 : ℂ) (by simp [rubi1137r17, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1137r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, hw] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1137r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1138r18_counterexample_real : ¬ rubi1138r18.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1138r18.conditions rubi1138r18.body rubi1138r18.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1138r18, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1138r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1138r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1138r18_counterexample_complex : ¬ rubi1138r18.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1138r18.conditions rubi1138r18.body rubi1138r18.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1138r18, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1138r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1138r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1138r19_counterexample_real : ¬ rubi1138r19.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1138r19.conditions rubi1138r19.body rubi1138r19.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" then -1 else if s = "b" ∨ s = "d" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "n2" ∨ s = "p" then -2 else 0) (1 : ℝ) (by simp [rubi1138r19, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1138r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, hw] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1138r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1138r19_counterexample_complex : ¬ rubi1138r19.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1138r19.conditions rubi1138r19.body rubi1138r19.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" then -1 else if s = "b" ∨ s = "d" ∨ s = "g" ∨ s = "h" ∨ s = "m" ∨ s = "n2" ∨ s = "p" then -2 else 0) (1 : ℂ) (by simp [rubi1138r19, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1138r19, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, hw] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1138r19, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1212r96_counterexample_real : ¬ rubi1212r96.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r96.conditions rubi1212r96.body rubi1212r96.result rubi1212r96.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi1212r96, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1212r96, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1212r96.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r96, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r96, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1212r96_counterexample_complex : ¬ rubi1212r96.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1212r96.conditions rubi1212r96.body rubi1212r96.result rubi1212r96.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi1212r96, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1212r96, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1212r96.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -2 else if s = "a" ∨ s = "e" ∨ s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1212r96, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1212r96, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1231r3_counterexample_real : ¬ rubi1231r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1231r3.conditions rubi1231r3.body rubi1231r3.result rubi1231r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1231r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1231r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1231r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1231r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1231r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1231r3_counterexample_complex : ¬ rubi1231r3.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1231r3.conditions rubi1231r3.body rubi1231r3.result rubi1231r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1231r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1231r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1231r3.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1231r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1231r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1231r5_counterexample_real : ¬ rubi1231r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1231r5.conditions rubi1231r5.body rubi1231r5.result rubi1231r5.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "b" ∨ s = "c" then 1 else 0) (1 : ℝ) (by simp [rubi1231r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1231r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1231r5.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "b" ∨ s = "c" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1231r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1231r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1231r5_counterexample_complex : ¬ rubi1231r5.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1231r5.conditions rubi1231r5.body rubi1231r5.result rubi1231r5.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "b" ∨ s = "c" then 1 else 0) (1 : ℂ) (by simp [rubi1231r5, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1231r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1231r5.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "b" ∨ s = "c" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1231r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1231r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1232r10_counterexample_real : ¬ rubi1232r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1232r10.conditions rubi1232r10.body rubi1232r10.result rubi1232r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1232r10, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1232r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1232r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1232r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1232r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1232r10_counterexample_complex : ¬ rubi1232r10.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1232r10.conditions rubi1232r10.body rubi1232r10.result rubi1232r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1232r10, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1232r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1232r10.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1232r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1232r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1232r18_counterexample_real : ¬ rubi1232r18.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1232r18.conditions rubi1232r18.body rubi1232r18.result rubi1232r18.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then 1 else if s = "b" ∨ s = "m" ∨ s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1232r18, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1232r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1232r18.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then 1 else if s = "b" ∨ s = "m" ∨ s = "n2" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1232r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1232r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1232r18_counterexample_complex : ¬ rubi1232r18.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1232r18.conditions rubi1232r18.body rubi1232r18.result rubi1232r18.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then 1 else if s = "b" ∨ s = "m" ∨ s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1232r18, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1232r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1232r18.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "n" then 1 else if s = "b" ∨ s = "m" ∨ s = "n2" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1232r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1232r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1233r11_counterexample_real : ¬ rubi1233r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1233r11.conditions rubi1233r11.body rubi1233r11.result rubi1233r11.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1233r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi1233r11.integrals[0]!, by simp [rubi1233r11], ?_⟩
  intro h
  simp [rubi1233r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1233r11_counterexample_complex : ¬ rubi1233r11.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1233r11.conditions rubi1233r11.body rubi1233r11.result rubi1233r11.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1233r11, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi1233r11.integrals[0]!, by simp [rubi1233r11], ?_⟩
  intro h
  simp [rubi1233r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1233r12_counterexample_real : ¬ rubi1233r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1233r12.conditions rubi1233r12.body rubi1233r12.result rubi1233r12.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1233r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi1233r12.integrals[0]!, by simp [rubi1233r12], ?_⟩
  intro h
  simp [rubi1233r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1233r12_counterexample_complex : ¬ rubi1233r12.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1233r12.conditions rubi1233r12.body rubi1233r12.result rubi1233r12.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1233r12, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi1233r12.integrals[0]!, by simp [rubi1233r12], ?_⟩
  intro h
  simp [rubi1233r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1233r19_counterexample_real : ¬ rubi1233r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1233r19.conditions rubi1233r19.body rubi1233r19.result rubi1233r19.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1233r19, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1233r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else if s = "n2" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1233r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1233r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1233r19_counterexample_complex : ¬ rubi1233r19.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1233r19.conditions rubi1233r19.body rubi1233r19.result rubi1233r19.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1233r19, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r19, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1233r19.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else if s = "n2" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1233r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1233r19, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1233r20_counterexample_real : ¬ rubi1233r20.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1233r20.conditions rubi1233r20.body rubi1233r20.result rubi1233r20.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "n" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1233r20, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1233r20.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "n" then 1 else if s = "n2" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1233r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1233r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1233r20_counterexample_complex : ¬ rubi1233r20.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1233r20.conditions rubi1233r20.body rubi1233r20.result rubi1233r20.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "n" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1233r20, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r20, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1233r20.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "n" then 1 else if s = "n2" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1233r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1233r20, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1233r27_counterexample_real : ¬ rubi1233r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1233r27.conditions rubi1233r27.body rubi1233r27.result rubi1233r27.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "c" ∨ s = "d" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi1233r27, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1233r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "c" ∨ s = "d" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1233r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1233r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1233r27_counterexample_complex : ¬ rubi1233r27.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1233r27.conditions rubi1233r27.body rubi1233r27.result rubi1233r27.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "c" ∨ s = "d" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi1233r27, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r27, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1233r27.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "c" ∨ s = "d" ∨ s = "e" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1233r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1233r27, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1233r50_counterexample_real : ¬ rubi1233r50.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1233r50.conditions rubi1233r50.body rubi1233r50.result rubi1233r50.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "r" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1233r50, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r50, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi1233r50.integrals[0]!, by simp [rubi1233r50], ?_⟩
  intro h
  simp [rubi1233r50, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1233r50_counterexample_complex : ¬ rubi1233r50.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1233r50.conditions rubi1233r50.body rubi1233r50.result rubi1233r50.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "r" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1233r50, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r50, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi1233r50.integrals[0]!, by simp [rubi1233r50], ?_⟩
  intro h
  simp [rubi1233r50, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1233r51_counterexample_real : ¬ rubi1233r51.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1233r51.conditions rubi1233r51.body rubi1233r51.result rubi1233r51.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "r" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1233r51, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r51, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi1233r51.integrals[0]!, by simp [rubi1233r51], ?_⟩
  intro h
  simp [rubi1233r51, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1233r51_counterexample_complex : ¬ rubi1233r51.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1233r51.conditions rubi1233r51.body rubi1233r51.result rubi1233r51.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "r" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1233r51, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1233r51, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi1233r51.integrals[0]!, by simp [rubi1233r51], ?_⟩
  intro h
  simp [rubi1233r51, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1234r17_counterexample_real : ¬ rubi1234r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r17.conditions rubi1234r17.body rubi1234r17.result rubi1234r17.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1234r17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1234r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi1234r17.integrals[0]!, by simp [rubi1234r17], ?_⟩
  intro h
  simp [rubi1234r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1234r17_counterexample_complex : ¬ rubi1234r17.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1234r17.conditions rubi1234r17.body rubi1234r17.result rubi1234r17.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1234r17, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1234r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi1234r17.integrals[0]!, by simp [rubi1234r17], ?_⟩
  intro h
  simp [rubi1234r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1234r18_counterexample_real : ¬ rubi1234r18.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r18.conditions rubi1234r18.body rubi1234r18.result rubi1234r18.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1234r18, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1234r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi1234r18.integrals[0]!, by simp [rubi1234r18], ?_⟩
  intro h
  simp [rubi1234r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1234r18_counterexample_complex : ¬ rubi1234r18.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1234r18.conditions rubi1234r18.body rubi1234r18.result rubi1234r18.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1234r18, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1234r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi1234r18.integrals[0]!, by simp [rubi1234r18], ?_⟩
  intro h
  simp [rubi1234r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1234r38_counterexample_real : ¬ rubi1234r38.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r38.conditions rubi1234r38.body rubi1234r38.result rubi1234r38.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1234r38, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1234r38, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r38.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r38, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r38, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1234r38_counterexample_complex : ¬ rubi1234r38.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1234r38.conditions rubi1234r38.body rubi1234r38.result rubi1234r38.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1234r38, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1234r38, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r38.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r38, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r38, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi1235r2_counterexample_real : ¬ rubi1235r2.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1235r2.conditions rubi1235r2.body rubi1235r2.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1235r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1235r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1235r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1235r2_counterexample_complex : ¬ rubi1235r2.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1235r2.conditions rubi1235r2.body rubi1235r2.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1235r2, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1235r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1235r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1235r3_counterexample_real : ¬ rubi1235r3.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1235r3.conditions rubi1235r3.body rubi1235r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "n" then -1 else if s = "n2" then -2 else 0) (1 : ℝ) (by simp [rubi1235r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1235r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, hw] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1235r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1235r3_counterexample_complex : ¬ rubi1235r3.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1235r3.conditions rubi1235r3.body rubi1235r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "n" then -1 else if s = "n2" then -2 else 0) (1 : ℂ) (by simp [rubi1235r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1235r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, hw] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1235r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1236r3_counterexample_real : ¬ rubi1236r3.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1236r3.conditions rubi1236r3.body rubi1236r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℝ) (by simp [rubi1236r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1236r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1236r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1236r3_counterexample_complex : ¬ rubi1236r3.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1236r3.conditions rubi1236r3.body rubi1236r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else if s = "n2" then 2 else 0) (1 : ℂ) (by simp [rubi1236r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1236r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1236r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1236r4_counterexample_real : ¬ rubi1236r4.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1236r4.conditions rubi1236r4.body rubi1236r4.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" then -1 else if s = "c" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n2" ∨ s = "p" then -2 else 0) (1 : ℝ) (by simp [rubi1236r4, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1236r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, hw] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1236r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi1236r4_counterexample_complex : ¬ rubi1236r4.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1236r4.conditions rubi1236r4.body rubi1236r4.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" then -1 else if s = "c" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n2" ∨ s = "p" then -2 else 0) (1 : ℂ) (by simp [rubi1236r4, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1236r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, hw] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1236r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi21r7_counterexample_real : ¬ rubi21r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi21r7.conditions rubi21r7.body rubi21r7.result rubi21r7.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "g" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi21r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi21r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi21r7.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "g" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi21r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi21r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi21r7_counterexample_complex : ¬ rubi21r7.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi21r7.conditions rubi21r7.body rubi21r7.result rubi21r7.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "g" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi21r7, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi21r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi21r7.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "g" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi21r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi21r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi23r13_counterexample_real : ¬ rubi23r13.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi23r13.conditions rubi23r13.body rubi23r13.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" then 1 else if s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi23r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi23r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi23r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi23r13_counterexample_complex : ¬ rubi23r13.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi23r13.conditions rubi23r13.body rubi23r13.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" then 1 else if s = "n" then 2 else 0) (1 : ℂ) (by simp [rubi23r13, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi23r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi23r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi23r37_counterexample_real : ¬ rubi23r37.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi23r37.conditions rubi23r37.body rubi23r37.result rubi23r37.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then 1 else 0) (1 : ℝ) (by simp [rubi23r37, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi23r37, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi23r37.integrals[0]!, by simp [rubi23r37], ?_⟩
  intro h
  simp [rubi23r37, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi23r37_counterexample_complex : ¬ rubi23r37.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi23r37.conditions rubi23r37.body rubi23r37.result rubi23r37.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then 1 else 0) (1 : ℂ) (by simp [rubi23r37, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi23r37, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi23r37.integrals[0]!, by simp [rubi23r37], ?_⟩
  intro h
  simp [rubi23r37, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi312r11_counterexample_real : ¬ rubi312r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi312r11.conditions rubi312r11.body rubi312r11.result rubi312r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else 0) (0 : ℝ) (by simp [rubi312r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi312r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi312r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else 0) "x" (0 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi312r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi312r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi312r11_counterexample_complex : ¬ rubi312r11.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi312r11.conditions rubi312r11.body rubi312r11.result rubi312r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else 0) (0 : ℂ) (by simp [rubi312r11, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi312r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi312r11.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else 0) "x" (0 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi312r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi312r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi321r12_counterexample_real : ¬ rubi321r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi321r12.conditions rubi321r12.body rubi321r12.result rubi321r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" then -3 else if s = "A" ∨ s = "B" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" then 1 else 0) (1 : ℝ) (by simp [rubi321r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi321r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi321r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then -3 else if s = "A" ∨ s = "B" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi321r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi321r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi321r12_counterexample_complex : ¬ rubi321r12.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi321r12.conditions rubi321r12.body rubi321r12.result rubi321r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" then -3 else if s = "A" ∨ s = "B" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" then 1 else 0) (1 : ℂ) (by simp [rubi321r12, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi321r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi321r12.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" then -3 else if s = "A" ∨ s = "B" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi321r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi321r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi321r2_counterexample_real : ¬ rubi321r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi321r2.conditions rubi321r2.body rubi321r2.result rubi321r2.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then -3 else if s = "B" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "p" then 1 else 0) (-1 : ℝ) (by simp [rubi321r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi321r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi321r2.integrals[0]!, by simp [rubi321r2], ?_⟩
  intro h
  simp [rubi321r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi321r2_counterexample_complex : ¬ rubi321r2.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi321r2.conditions rubi321r2.body rubi321r2.result rubi321r2.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then -3 else if s = "B" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "p" then 1 else 0) (-1 : ℂ) (by simp [rubi321r2, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi321r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi321r2.integrals[0]!, by simp [rubi321r2], ?_⟩
  intro h
  simp [rubi321r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

theorem rubi322r17_counterexample_real : ¬ rubi322r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi322r17.conditions rubi322r17.body rubi322r17.result rubi322r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "mn" then -1 else if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi322r17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi322r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi322r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "mn" then -1 else if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi322r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi322r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi322r17_counterexample_complex : ¬ rubi322r17.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi322r17.conditions rubi322r17.body rubi322r17.result rubi322r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "mn" then -1 else if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi322r17, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi322r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi322r17.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "mn" then -1 else if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi322r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi322r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg, recEnv] at h <;> norm_num at h

theorem rubi35r8_counterexample_real : ¬ rubi35r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi35r8.conditions rubi35r8.body rubi35r8.result rubi35r8.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "d" then -1 else if s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi35r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi35r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] <;> first | positivity | norm_num) ⟨rubi35r8.integrals[0]!, by simp [rubi35r8], ?_⟩
  intro h
  simp [rubi35r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivexnat, ivexneg] at h <;> norm_num at h

end OSR.IntegrationRec29
