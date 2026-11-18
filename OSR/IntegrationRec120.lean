import OSR.IntegrationRec91

/-!
# Integration (RUBI): refutations of rules not considered before

RUBI rules transcribed as stated.  Each is refuted by an explicit assignment:
the conditions hold and the integrand is defined near a point where the
result or a residual integrand is not (RUBI excludes these cases by its rule
order).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec120

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.1.1.4 #16 -/
def rubi1114r16 : CRule where
  id := "integration.rubi_1_1_1_4_r16"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x")))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h"))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "h")))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "p"]
  priority := 9501
  description := "RUBI 1.1.1.4 #16"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:16" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#16"

/-- RUBI 1.1.3.5 #12 -/
def rubi1135r12 : CRule where
  id := "integration.rubi_1_1_3_5_r12"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  priority := 9502
  description := "RUBI 1.1.3.5 #12"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:12" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#12"

/-- RUBI 1.1.3.5 #13 -/
def rubi1135r13 : CRule where
  id := "integration.rubi_1_1_3_5_r13"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "c") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.int 0)]
  priority := 9503
  description := "RUBI 1.1.3.5 #13"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:13" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#13"

/-- RUBI 1.1.3.5 #28 -/
def rubi1135r28 : CRule where
  id := "integration.rubi_1_1_3_5_r28"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:28"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "c")) (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "a") (.int 2))) (.var "d")) (.var "f"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "x") (.int 2)))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  priority := 9504
  description := "RUBI 1.1.3.5 #28"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:28" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#28"

/-- RUBI 1.1.3.5 #29 -/
def rubi1135r29 : CRule where
  id := "integration.rubi_1_1_3_5_r29"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "x")) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "f")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "c")) (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int 3) (.pow (.var "a") (.int 2))) (.var "d")) (.var "f"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "b")) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.var "c") (.var "f"))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  priority := 9505
  description := "RUBI 1.1.3.5 #29"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:29" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#29"

/-- RUBI 1.1.3.5 #3 -/
def rubi1135r3 : CRule where
  id := "integration.rubi_1_1_3_5_r3"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "f") (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n"]
  priority := 9506
  description := "RUBI 1.1.3.5 #3"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:3" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#3"

/-- RUBI 1.1.4.1 #11 -/
def rubi1141r11 : CRule where
  id := "integration.rubi_1_1_4_1_r11"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.4 Improper/1.1.4.1 (a x^j+b x^n)^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "j"))) (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-2)) (.app2 .root (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "j"))) (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.var "x") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.var "j"))) (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.var "x") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.var "j")))) (.app2 .root (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "j"))) (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "j", "n"]
  conditions := [.gt (.var "j") (.app2 .mul (.int 2) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))]
  priority := 9507
  description := "RUBI 1.1.4.1 #11"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.4 Improper/1.1.4.1 (a x^j+b x^n)^p:11" "1 Algebraic functions/1.1 Binomial products/1.1.4 Improper/1.1.4.1 (a x^j+b x^n)^p.m#11"

/-- RUBI 1.2.1.1 #2 -/
def rubi1211r2 : CRule where
  id := "integration.rubi_1_2_1_1_r2"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.pow (.int 2) (.int (-1)))) (.app2 .mul (.var "c") (.var "x"))) (.pow (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.app2 .mul (.var "b") (.pow (.int 2) (.int (-1)))) (.app2 .mul (.var "c") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)]
  priority := 9508
  description := "RUBI 1.2.1.1 #2"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:2" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p.m#2"

/-- RUBI 1.2.1.5 #18 -/
def rubi1215r18 : CRule where
  id := "integration.rubi_1_2_1_5_r18"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.5 (a+b x+c x^2)^p (d+e x+f x^2)^q:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "f") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "f") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.var "x"))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2))))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0)]
  priority := 9509
  description := "RUBI 1.2.1.5 #18"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.5 (a+b x+c x^2)^p (d+e x+f x^2)^q:18" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.5 (a+b x+c x^2)^p (d+e x+f x^2)^q.m#18"

/-- RUBI 1.2.1.7 #31 -/
def rubi1217r31 : CRule where
  id := "integration.rubi_1_2_1_7_r31"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.7 (a+b x+c x^2)^p (d+e x+f x^2)^q (A+B x+C x^2):31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.var "x"))) (.app2 .mul (.var "C") (.pow (.var "x") (.int 2)))) (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "C") (.pow (.var "c") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C"))) (.app2 .mul (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.var "x"))) (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "f", "A", "B", "C"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)]
  priority := 9510
  description := "RUBI 1.2.1.7 #31"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.7 (a+b x+c x^2)^p (d+e x+f x^2)^q (A+B x+C x^2):31" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.7 (a+b x+c x^2)^p (d+e x+f x^2)^q (A+B x+C x^2).m#31"

/-- RUBI 1.2.1.7 #32 -/
def rubi1217r32 : CRule where
  id := "integration.rubi_1_2_1_7_r32"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.7 (a+b x+c x^2)^p (d+e x+f x^2)^q (A+B x+C x^2):32"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.var "x") (.int 2)))) (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "C") (.pow (.var "c") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C")) (.var "x"))) (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "f", "A", "C"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)]
  priority := 9511
  description := "RUBI 1.2.1.7 #32"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.7 (a+b x+c x^2)^p (d+e x+f x^2)^q (A+B x+C x^2):32" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.7 (a+b x+c x^2)^p (d+e x+f x^2)^q (A+B x+C x^2).m#32"

/-- RUBI 1.2.2.3 #42 -/
def rubi1223r42 : CRule where
  id := "integration.rubi_1_2_2_3_r42"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:42"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2)) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.pow (.var "e") (.int 2))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "e") (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.pow (.var "e") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "x") (.int 2)))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)]
  priority := 9512
  description := "RUBI 1.2.2.3 #42"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:42" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#42"

/-- RUBI 1.2.2.7 #14 -/
def rubi1227r14 : CRule where
  id := "integration.rubi_1_2_2_7_r14"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.pow (.var "x") (.int 2)))) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "A") (.app2 .mul (.var "B") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.app2 .mul (.var "a") (.pow (.var "A") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))) (.pow (.var "B") (.int (-1))))) (.int 2))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .root (.app2 .add (.var "A") (.app2 .mul (.var "B") (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.app2 .mul (.var "a") (.pow (.var "A") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))) (.pow (.var "B") (.int (-1))))) (.int 2))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "A", "B"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "A") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "B") (.int 2)))) (.int 0)]
  priority := 9513
  description := "RUBI 1.2.2.7 #14"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p:14" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p.m#14"

/-- RUBI 1.3.3 #22 -/
def rubi133r22 : CRule where
  id := "integration.rubi_1_3_3_r22"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:22"
  shape := .antideriv; x := "x"
  body := (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int 2))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "b") (.int 2))) (.var "d")) (.pow (.var "x") (.int 3))) (.pow (.app2 .mul (.int 3) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)))) (.app2 .mul (.int 3) (.pow (.int 2) (.int (-1)))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int 2)) (.int (-1)))))
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.var "c"))) (.int 0)]
  priority := 9514
  description := "RUBI 1.3.3 #22"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:22" "1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions.m#22"

/-- RUBI 1.3.3 #35 -/
def rubi133r35 : CRule where
  id := "integration.rubi_1_3_3_r35"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:35"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.pow (.pow (.var "d") (.int 3)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "x"))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.pow (.var "c") (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "d") (.int 3)))) (.int 0)]
  priority := 9515
  description := "RUBI 1.3.3 #35"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:35" "1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions.m#35"

/-- RUBI 1.3.3 #5 -/
def rubi133r5 : CRule where
  id := "integration.rubi_1_3_3_r5"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))) (.app2 .mul (.var "c") (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "p")))) (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "I1")) (.app2 .mul (.var "c") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "c") (.int 2))) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.pow (.var "c") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.int 2))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "c") (.int 2))) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.pow (.var "c") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.eq (.var "p") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.app2 .mul (.var "b") (.pow (.var "c") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)]
  priority := 9516
  description := "RUBI 1.3.3 #5"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:5" "1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions.m#5"

/-- RUBI 1.3.3 #7 -/
def rubi133r7 : CRule where
  id := "integration.rubi_1_3_3_r7"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:7"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.app2 .root (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int 2)))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.app2 .add (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 5) (.var "b")) (.var "c")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.pow (.var "b") (.int 2))) (.var "g")) (.var "h"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 3)) (.var "a")) (.var "c")) (.var "g")) (.var "h"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.pow (.var "h") (.int 2))))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 10) (.var "c")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")) (.var "h"))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2))))) (.var "x"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 9) (.pow (.var "c") (.int 2))) (.var "f")) (.var "g")) (.var "h")) (.pow (.var "x") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 3) (.pow (.var "c") (.int 2))) (.var "f")) (.pow (.var "h") (.int 2))) (.pow (.var "x") (.int 3)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "e") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "h")))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 5) (.var "c")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "b")) (.var "h"))) (.app2 .mul (.app2 .mul (.var "c") (.var "h")) (.var "x")))) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 15) (.pow (.var "c") (.int 2))) (.var "f")) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x")))) (.int (-1)))) (.app2 .root (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int 2)))
  independent := ["a", "b", "c", "d", "e", "f", "g", "h"]
  conditions := [.eq (.app2 .add (.pow (.app2 .add (.app2 .mul (.var "e") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "h"))) (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.int 2))) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")) (.var "h"))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "e") (.int 2))) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "d")) (.var "e")) (.var "h"))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.int 2))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "h"))))) (.int 0)]
  priority := 9517
  description := "RUBI 1.3.3 #7"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:7" "1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions.m#7"

/-- RUBI 3.1.5 #1 -/
def rubi315r1 : CRule where
  id := "integration.rubi_3_1_5_r1"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "B") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.int 2))) (.pow (.app2 .mul (.var "b") (.var "e")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "A")) (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.app2 .mul (.var "b") (.var "n"))))) (.pow (.app2 .mul (.int 2) (.var "b")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "n"]
  priority := 9518
  description := "RUBI 3.1.5 #1"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:1" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#1"

/-- RUBI 3.5 #10 -/
def rubi35r10 : CRule where
  id := "integration.rubi_3_5_r10"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:10"
  shape := .antiderivRec; x := "x"
  body := (.app1 .ln (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .ln (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.pow (.var "f") (.int 2))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.var "x") (.pow (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))) (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.var "x")))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f"]
  conditions := [.eq (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.var "f") (.int 2)))) (.int 0)]
  priority := 9519
  description := "RUBI 3.5 #10"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:10" "3 Logarithms/3.5 Miscellaneous logarithms.m#10"

/-- RUBI 3.5 #11 -/
def rubi35r11 : CRule where
  id := "integration.rubi_3_5_r11"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.app1 .ln (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app1 .ln (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)))))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "g")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "f") (.int 2)))) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "e"))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.var "x")))) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m"]
  conditions := [.eq (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.var "f") (.int 2)))) (.int 0),
    .ne (.var "m") (.int (-1)),
    .int (.app2 .mul (.int 2) (.var "m"))]
  priority := 9520
  description := "RUBI 3.5 #11"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:11" "3 Logarithms/3.5 Miscellaneous logarithms.m#11"

/-- RUBI 3.5 #12 -/
def rubi35r12 : CRule where
  id := "integration.rubi_3_5_r12"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.app1 .ln (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app1 .ln (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)))))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.pow (.var "f") (.int 2))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))) (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.var "x")))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f", "g", "m"]
  conditions := [.eq (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.var "f") (.int 2)))) (.int 0),
    .ne (.var "m") (.int (-1)),
    .int (.app2 .mul (.int 2) (.var "m"))]
  priority := 9521
  description := "RUBI 3.5 #12"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:12" "3 Logarithms/3.5 Miscellaneous logarithms.m#12"

/-- RUBI 3.5 #9 -/
def rubi35r9 : CRule where
  id := "integration.rubi_3_5_r9"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:9"
  shape := .antiderivRec; x := "x"
  body := (.app1 .ln (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .ln (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)))))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.pow (.int 2) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.var "x") (.pow (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "f") (.int 2)))) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "e"))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.var "x")))) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.eq (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.var "f") (.int 2)))) (.int 0)]
  priority := 9522
  description := "RUBI 3.5 #9"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:9" "3 Logarithms/3.5 Miscellaneous logarithms.m#9"

/-- RUBI 4.7.6 #6 -/
def rubi476r6 : CRule where
  id := "integration.rubi_4_7_6_r6"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app2 .mul (.var "b") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "b") (.var "n")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .sec (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))))]
  independent := ["a", "b", "c", "d", "n", "m", "p"]
  conditions := [.eq (.var "p") (.int 1),
    .gt (.var "m") (.int 0)]
  priority := 9523
  description := "RUBI 4.7.6 #6"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:6" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#6"

/-- RUBI 4.7.6 #8 -/
def rubi476r8 : CRule where
  id := "integration.rubi_4_7_6_r8"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.int 2))) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 9524
  description := "RUBI 4.7.6 #8"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:8" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#8"

/-- RUBI 4.7.7 #33 -/
def rubi477r33 : CRule where
  id := "integration.rubi_4_7_7_r33"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "m"))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.pow (.var "f") (.var "n")) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .cot (.app2 .add (.app2 .mul (.var "d") (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.int 2) (.int (-1)))))) (.var "m"))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "m", "n"]
  conditions := [.eq (.app2 .add (.var "f") (.var "g")) (.int 0),
    .int (.var "m"),
    .int (.var "n"),
    .eq (.app2 .add (.var "m") (.var "n")) (.int 0)]
  priority := 9525
  description := "RUBI 4.7.7 #33"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:33" "4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m#33"

/-- RUBI 4.7.9 #13 -/
def rubi479r13 : CRule where
  id := "integration.rubi_4_7_9_r13"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9526
  description := "RUBI 4.7.9 #13"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:13" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#13"

/-- RUBI 4.7.9 #22 -/
def rubi479r22 : CRule where
  id := "integration.rubi_4_7_9_r22"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:22"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9527
  description := "RUBI 4.7.9 #22"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:22" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#22"

/-- RUBI 4.7.9 #32 -/
def rubi479r32 : CRule where
  id := "integration.rubi_4_7_9_r32"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:32"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9528
  description := "RUBI 4.7.9 #32"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:32" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#32"

/-- RUBI 4.7.9 #85 -/
def rubi479r85 : CRule where
  id := "integration.rubi_4_7_9_r85"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:85"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "b") (.var "x")) (.var "m")) (.pow (.app1 .sec (.app2 .mul (.var "a") (.var "x"))) (.var "n"))) (.pow (.pow (.app2 .add (.app2 .mul (.var "c") (.app1 .cos (.app2 .mul (.var "a") (.var "x")))) (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app1 .sin (.app2 .mul (.var "a") (.var "x"))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.app2 .mul (.var "b") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app1 .sec (.app2 .mul (.var "a") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.app2 .mul (.var "c") (.app1 .cos (.app2 .mul (.var "a") (.var "x")))) (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app1 .sin (.app2 .mul (.var "a") (.var "x")))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.var "n") (.int 1))) (.pow (.pow (.var "d") (.int 2)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "b") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app1 .sec (.app2 .mul (.var "a") (.var "x"))) (.app2 .add (.var "n") (.int 2)))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.int (-1)) (.var "d"))) (.int 0),
    .eq (.var "m") (.app2 .add (.var "n") (.int 2))]
  priority := 9529
  description := "RUBI 4.7.9 #85"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:85" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#85"

/-- RUBI 5.1.1 #3 -/
def rubi511r3 : CRule where
  id := "integration.rubi_5_1_1_r3"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n:3"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "n"]
  conditions := [.gt (.int (-1)) (.var "n")]
  priority := 9530
  description := "RUBI 5.1.1 #3"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n:3" "5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n.m#3"

/-- RUBI 5.1.1 #4 -/
def rubi511r4 : CRule where
  id := "integration.rubi_5_1_1_r4"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n:4"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "n"]
  conditions := [.gt (.int (-1)) (.var "n")]
  priority := 9531
  description := "RUBI 5.1.1 #4"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n:4" "5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n.m#4"

/-- RUBI 5.1.2 #10 -/
def rubi512r10 : CRule where
  id := "integration.rubi_5_1_2_r10"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.var "m"))) (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "m") (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .gt (.int (-2)) (.var "n")]
  priority := 9532
  description := "RUBI 5.1.2 #10"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:10" "5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n.m#10"

/-- RUBI 5.1.2 #3 -/
def rubi512r3 : CRule where
  id := "integration.rubi_5_1_2_r3"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 9533
  description := "RUBI 5.1.2 #3"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:3" "5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n.m#3"

/-- RUBI 5.1.2 #4 -/
def rubi512r4 : CRule where
  id := "integration.rubi_5_1_2_r4"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 9534
  description := "RUBI 5.1.2 #4"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:4" "5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n.m#4"

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
private theorem ivm4 : intValue? (-4 : α) = some (-4) := by simpa using intValue?_intCast (α := α) (-4)
private theorem ivm5 : intValue? (-5 : α) = some (-5) := by simpa using intValue?_intCast (α := α) (-5)
private theorem ivm6 : intValue? (-6 : α) = some (-6) := by simpa using intValue?_intCast (α := α) (-6)
private theorem ivm7 : intValue? (-7 : α) = some (-7) := by simpa using intValue?_intCast (α := α) (-7)
private theorem ivm8 : intValue? (-8 : α) = some (-8) := by simpa using intValue?_intCast (α := α) (-8)
private theorem ivm9 : intValue? (-9 : α) = some (-9) := by simpa using intValue?_intCast (α := α) (-9)
private theorem ivm10 : intValue? (-10 : α) = some (-10) := by simpa using intValue?_intCast (α := α) (-10)
private theorem ivm11 : intValue? (-11 : α) = some (-11) := by simpa using intValue?_intCast (α := α) (-11)
private theorem ivm12 : intValue? (-12 : α) = some (-12) := by simpa using intValue?_intCast (α := α) (-12)
private theorem ivnat (n : ℕ) [n.AtLeastTwo] : intValue? (OfNat.ofNat n : α) = some (OfNat.ofNat n) := by
  simpa using intValue?_intCast (α := α) (OfNat.ofNat n : ℤ)
private theorem ivneg (n : ℕ) [n.AtLeastTwo] :
    intValue? (-(OfNat.ofNat n : α)) = some (-(OfNat.ofNat n)) := by
  simpa using intValue?_intCast (α := α) (-(OfNat.ofNat n : ℤ))
end


theorem rubi1114r16_counterexample_real : ¬ rubi1114r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1114r16.conditions rubi1114r16.body rubi1114r16.result rubi1114r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi1114r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi1114r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi1114r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1114r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1114r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1114r16_counterexample_complex : ¬ rubi1114r16.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1114r16.conditions rubi1114r16.body rubi1114r16.result rubi1114r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi1114r16, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi1114r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi1114r16.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1114r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1114r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1135r12_counterexample_real : ¬ rubi1135r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1135r12.conditions rubi1135r12.body rubi1135r12.result rubi1135r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi1135r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi1135r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi1135r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1135r13_counterexample_real : ¬ rubi1135r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1135r13.conditions rubi1135r13.body rubi1135r13.result rubi1135r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi1135r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1135r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi1135r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1135r28_counterexample_real : ¬ rubi1135r28.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1135r28.conditions rubi1135r28.body rubi1135r28.result rubi1135r28.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi1135r28, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi1135r28, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi1135r28.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r28, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1135r29_counterexample_real : ¬ rubi1135r29.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1135r29.conditions rubi1135r29.body rubi1135r29.result rubi1135r29.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi1135r29, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi1135r29, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi1135r29.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r29, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1135r3_counterexample_real : ¬ rubi1135r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1135r3.conditions rubi1135r3.body rubi1135r3.result rubi1135r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "e" ∨ s = "f" then 1 else 0) (1 : ℝ) (by simp [rubi1135r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi1135r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi1135r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1135r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1135r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1141r11_counterexample_real : ¬ rubi1141r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1141r11.conditions rubi1141r11.body rubi1141r11.result rubi1141r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" then 1 else 0) (0 : ℝ) (by simp [rubi1141r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi1141r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi1141r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then 1 else 0) "x" (0 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1141r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1141r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1211r2_counterexample_real : ¬ rubi1211r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1211r2.conditions rubi1211r2.body rubi1211r2.result rubi1211r2.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then 1 else 0) (1 : ℝ) (by simp [rubi1211r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi1211r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi1211r2.integrals[0]!, by simp [rubi1211r2], ?_⟩
  intro h
  simp [rubi1211r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1215r18_counterexample_real : ¬ rubi1215r18.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1215r18.conditions rubi1215r18.body rubi1215r18.result rubi1215r18.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi1215r18, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1215r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi1215r18.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1215r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1215r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1217r31_counterexample_real : ¬ rubi1217r31.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1217r31.conditions rubi1217r31.body rubi1217r31.result rubi1217r31.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "A" ∨ s = "B" ∨ s = "C" ∨ s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi1217r31, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1217r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi1217r31.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" ∨ s = "B" ∨ s = "C" ∨ s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1217r31, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1217r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1217r32_counterexample_real : ¬ rubi1217r32.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1217r32.conditions rubi1217r32.body rubi1217r32.result rubi1217r32.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "A" ∨ s = "C" ∨ s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi1217r32, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1217r32, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi1217r32.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" ∨ s = "C" ∨ s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1217r32, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1217r32, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1223r42_counterexample_real : ¬ rubi1223r42.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1223r42.conditions rubi1223r42.body rubi1223r42.result rubi1223r42.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi1223r42, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1223r42, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi1223r42.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1223r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1223r42, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1227r14_counterexample_real : ¬ rubi1227r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1227r14.conditions rubi1227r14.body rubi1227r14.result rubi1227r14.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "A" ∨ s = "a" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi1227r14, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1227r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi1227r14.integrals[0]!, by simp [rubi1227r14], ?_⟩
  intro h
  simp [rubi1227r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi133r22_counterexample_real : ¬ rubi133r22.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi133r22.conditions rubi133r22.body rubi133r22.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" then 1 else 0) (1 : ℝ) (by simp [rubi133r22, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi133r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi133r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi133r35_counterexample_real : ¬ rubi133r35.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi133r35.conditions rubi133r35.body rubi133r35.result rubi133r35.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" then 1 else 0) (1 : ℝ) (by simp [rubi133r35, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi133r35, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi133r35.integrals[0]!, by simp [rubi133r35], ?_⟩
  intro h
  simp [rubi133r35, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi133r5_counterexample_real : ¬ rubi133r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi133r5.conditions rubi133r5.body rubi133r5.result rubi133r5.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi133r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi133r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi133r5.integrals[0]!, by simp [rubi133r5], ?_⟩
  intro h
  simp [rubi133r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi133r7_counterexample_real : ¬ rubi133r7.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi133r7.conditions rubi133r7.body rubi133r7.result
  refine not_antiderivHoldsUnder (fun s => if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "h" then 1 else 0) (1 : ℝ) (by simp [rubi133r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi133r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi133r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi315r1_counterexample_real : ¬ rubi315r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi315r1.conditions rubi315r1.body rubi315r1.result rubi315r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi315r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi315r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi315r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi315r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi35r10_counterexample_real : ¬ rubi35r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi35r10.conditions rubi35r10.body rubi35r10.result rubi35r10.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "d" ∨ s = "f" then 1 else 0) (1 : ℝ) (by simp [rubi35r10, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi35r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi35r10.integrals[0]!, by simp [rubi35r10], ?_⟩
  intro h
  simp [rubi35r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi35r11_counterexample_real : ¬ rubi35r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi35r11.conditions rubi35r11.body rubi35r11.result rubi35r11.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi35r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi35r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi35r11.integrals[0]!, by simp [rubi35r11], ?_⟩
  intro h
  simp [rubi35r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi35r12_counterexample_real : ¬ rubi35r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi35r12.conditions rubi35r12.body rubi35r12.result rubi35r12.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi35r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi35r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi35r12.integrals[0]!, by simp [rubi35r12], ?_⟩
  intro h
  simp [rubi35r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi35r9_counterexample_real : ¬ rubi35r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi35r9.conditions rubi35r9.body rubi35r9.result rubi35r9.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "d" ∨ s = "f" then 1 else 0) (1 : ℝ) (by simp [rubi35r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi35r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi35r9.integrals[0]!, by simp [rubi35r9], ?_⟩
  intro h
  simp [rubi35r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi476r6_counterexample_real : ¬ rubi476r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi476r6.conditions rubi476r6.body rubi476r6.result rubi476r6.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi476r6, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi476r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi476r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi476r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi476r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi476r8_counterexample_real : ¬ rubi476r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi476r8.conditions rubi476r8.body rubi476r8.result rubi476r8.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi476r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi476r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi476r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi476r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi476r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi477r33_counterexample_real : ¬ rubi477r33.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi477r33.conditions rubi477r33.body rubi477r33.result rubi477r33.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "f" then -1 else if s = "F" ∨ s = "a" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "g" then 1 else 0) (-1 : ℝ) (by simp [rubi477r33, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi477r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi477r33.integrals[0]!, by simp [rubi477r33], ?_⟩
  intro h
  simp [rubi477r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi477r33_counterexample_complex : ¬ rubi477r33.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi477r33.conditions rubi477r33.body rubi477r33.result rubi477r33.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "f" then -1 else if s = "F" ∨ s = "a" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "g" then 1 else 0) (-1 : ℂ) (by simp [rubi477r33, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi477r33, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi477r33.integrals[0]!, by simp [rubi477r33], ?_⟩
  intro h
  simp [rubi477r33, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi479r13_counterexample_real : ¬ rubi479r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r13.conditions rubi479r13.body rubi479r13.result rubi479r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi479r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi479r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi479r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi479r13_counterexample_complex : ¬ rubi479r13.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r13.conditions rubi479r13.body rubi479r13.result rubi479r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi479r13, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi479r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi479r13.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi479r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi479r22_counterexample_real : ¬ rubi479r22.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r22.conditions rubi479r22.body rubi479r22.result rubi479r22.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi479r22, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi479r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi479r22.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r22, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi479r32_counterexample_real : ¬ rubi479r32.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r32.conditions rubi479r32.body rubi479r32.result rubi479r32.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi479r32, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi479r32, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi479r32.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r32, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r32, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi479r85_counterexample_real : ¬ rubi479r85.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r85.conditions rubi479r85.body rubi479r85.result rubi479r85.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "n" then 1 else if s = "m" then 3 else 0) (1 : ℝ) (by simp [rubi479r85, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi479r85, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi479r85.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "n" then 1 else if s = "m" then 3 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r85, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r85, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi511r3_counterexample_real : ¬ rubi511r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi511r3.conditions rubi511r3.body rubi511r3.result rubi511r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then -3 else if s = "a" then 1 else 0) (1 : ℝ) (by simp [rubi511r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi511r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi511r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then -3 else if s = "a" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi511r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi511r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi511r4_counterexample_real : ¬ rubi511r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi511r4.conditions rubi511r4.body rubi511r4.result rubi511r4.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then -3 else if s = "b" then 1 else 0) (1 : ℝ) (by simp [rubi511r4, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi511r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi511r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then -3 else if s = "b" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi511r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi511r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi512r10_counterexample_real : ¬ rubi512r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi512r10.conditions rubi512r10.body rubi512r10.result rubi512r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then -3 else if s = "b" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi512r10, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi512r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi512r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then -3 else if s = "b" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi512r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi512r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi512r3_counterexample_real : ¬ rubi512r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi512r3.conditions rubi512r3.body rubi512r3.result rubi512r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi512r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi512r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi512r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi512r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi512r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi512r4_counterexample_real : ¬ rubi512r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi512r4.conditions rubi512r4.body rubi512r4.result rubi512r4.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi512r4, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi512r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi512r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi512r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi512r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec120
