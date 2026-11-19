import OSR.IntegrationRec91

/-!
# Integration (RUBI): `F^(c (a + b x))` times a hyperbolic function

The fragment interprets `F^(c (a + b x))` for integer exponents only, so an
integrand defined on a neighbourhood forces `c (a + b x)` to be an integer on
an interval, hence `b c = 0` (`int_valued_const`): the power is a constant.
6.7.7 #1, #2 and the reduction formulas 6.7.7 #3, #4, #7 and 4.7.7 #13, #14,
#17, #18 (of `sinh^n`, `cosh^n`, `sec^n` and `csc^n`) are proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec155

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 6.7.7 #1 -/
def rubi677r1 : CRule where
  id := "integration.rubi_6_7_7_r1"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1)))))
  independent := ["F", "a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int 0)]
  priority := 11857
  description := "RUBI 6.7.7 #1"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:1" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m#1"

/-- RUBI 6.7.7 #2 -/
def rubi677r2 : CRule where
  id := "integration.rubi_6_7_7_r2"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:2"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1)))))
  independent := ["F", "a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int 0)]
  priority := 11858
  description := "RUBI 6.7.7 #2"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:2" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m#2"

/-- RUBI 6.7.7 #3 -/
def rubi677r3 : CRule where
  id := "integration.rubi_6_7_7_r3"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "n")) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "n")) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.var "e") (.int 2))) (.pow (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["F", "a", "b", "c", "d", "e", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int 0),
    .gt (.var "n") (.int 1)]
  priority := 11859
  description := "RUBI 6.7.7 #3"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:3" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m#3"

/-- RUBI 6.7.7 #4 -/
def rubi677r4 : CRule where
  id := "integration.rubi_6_7_7_r4"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "n")) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "n") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.var "e") (.int 2))) (.pow (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["F", "a", "b", "c", "d", "e", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int 0),
    .gt (.var "n") (.int 1)]
  priority := 11860
  description := "RUBI 6.7.7 #4"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:4" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m#4"

/-- RUBI 6.7.7 #7 -/
def rubi677r7 : CRule where
  id := "integration.rubi_6_7_7_r7"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.app2 .add (.var "n") (.int 2)) (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 2)))))]
  independent := ["F", "a", "b", "c", "d", "e", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.app2 .add (.var "n") (.int 2)) (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "n"),
    .ne (.var "n") (.int (-2))]
  priority := 11861
  description := "RUBI 6.7.7 #7"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:7" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m#7"

/-- RUBI 4.7.7 #13 -/
def rubi477r13 : CRule where
  id := "integration.rubi_4_7_7_r13"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "n")) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.var "n")) (.app2 .add (.var "n") (.int 1))) (.pow (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 2)))))]
  independent := ["F", "a", "b", "c", "d", "e", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 11862
  description := "RUBI 4.7.7 #13"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:13" "4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m#13"

/-- RUBI 4.7.7 #14 -/
def rubi477r14 : CRule where
  id := "integration.rubi_4_7_7_r14"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .csc (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .csc (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "n")) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .csc (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.var "n")) (.app2 .add (.var "n") (.int 1))) (.pow (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .csc (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 2)))))]
  independent := ["F", "a", "b", "c", "d", "e", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 11863
  description := "RUBI 4.7.7 #14"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:14" "4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m#14"

/-- RUBI 4.7.7 #17 -/
def rubi477r17 : CRule where
  id := "integration.rubi_4_7_7_r17"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))) (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["F", "a", "b", "c", "d", "e", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2))) (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))) (.int 2)))) (.int 0),
    .gt (.var "n") (.int 1),
    .ne (.var "n") (.int 2)]
  priority := 11864
  description := "RUBI 4.7.7 #17"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:17" "4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m#17"

/-- RUBI 4.7.7 #18 -/
def rubi477r18 : CRule where
  id := "integration.rubi_4_7_7_r18"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .csc (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .csc (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .csc (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))) (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .csc (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["F", "a", "b", "c", "d", "e", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2))) (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))) (.int 2)))) (.int 0),
    .gt (.var "n") (.int 1),
    .ne (.var "n") (.int 2)]
  priority := 11865
  description := "RUBI 4.7.7 #18"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:18" "4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m#18"

/-! ## Proofs -/

/-- An affine function that takes integer values on a neighbourhood is constant. -/
theorem int_valued_const {a b c t : ℝ}
    (h : ∀ᶠ w in 𝓝 t, ∃ k : ℤ, intValue? (c * (a + b * w)) = some k) : c * b = 0 := by
  by_contra hcb
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.1 h
  have hpos : 0 < |c * b| := abs_pos.2 hcb
  set δ := min (ε / 2) (1 / (2 * |c * b|)) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδc : |c * b| * δ ≤ 1 / 2 := by
    have := min_le_right (ε / 2) (1 / (2 * |c * b|))
    calc |c * b| * δ ≤ |c * b| * (1 / (2 * |c * b|)) := by gcongr
      _ = 1 / 2 := by field_simp
  obtain ⟨k1, hk1⟩ := hb (y := t) (by simp [hε])
  obtain ⟨k2, hk2⟩ := hb (y := t + δ) (by
    rw [Real.dist_eq, show t + δ - t = δ by ring, abs_of_pos hδpos]; exact hδε)
  rw [intValue?_eq] at hk1 hk2
  have hdiff : ((k2 - k1 : ℤ) : ℝ) = c * b * δ := by push_cast; rw [← hk1, ← hk2]; ring
  have habs : |((k2 - k1 : ℤ) : ℝ)| < 1 := by
    rw [hdiff, abs_mul, abs_of_pos hδpos]; linarith
  have hk : k2 - k1 = 0 := by
    have : |k2 - k1| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.1 this
  rw [hk] at hdiff
  push_cast at hdiff
  have : c * b * δ ≠ 0 := mul_ne_zero hcb hδpos.ne'
  exact this hdiff.symm

theorem rubi677r1_real : rubi677r1.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi677r1.conditions rubi677r1.body rubi677r1.result
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hk : ∀ᶠ w in 𝓝 t, ∃ k : ℤ, intValue? (env "c" * (env "a" + env "b" * w)) = some k := hF.mono fun w hw => by
    simp only [rubi677r1, Defined] at hw
    obtain ⟨n, hn, -⟩ := hw.1.2.2
    exact ⟨n, by simpa [eval, Interp.real] using hn⟩
  have hcb := int_valued_const hk
  have hlin : ∀ w : ℝ, env "c" * (env "a" + env "b" * w) = env "c" * env "a" := fun w => by
    linear_combination w * hcb
  obtain ⟨k0, hk0⟩ : ∃ k : ℤ, intValue? (env "c" * env "a") = some k := by
    have := hk.self_of_nhds; rwa [hlin] at this
  have hcd := hc _ (List.mem_singleton_self _)
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  obtain ⟨hF0, hD⟩ := hcd
  have hbc : env "b" * env "c" = 0 := by linear_combination hcb
  have hbc2 : env "b" ^ 2 * env "c" ^ 2 = 0 := by rw [← mul_pow, hbc]; ring
  have hD' := hD
  rw [hbc2] at hD
  have he : env "e" ≠ 0 := by intro h; apply hD; rw [h]; ring
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    simp [rubi677r1, Defined, eval, Interp.real, i2, im1, hlin, hk0] at hw ⊢
    first | tauto | (simp_all; done) | (trace_state; sorry)
  · simp [rubi677r1, eval, Interp.real, i2, im1, hlin, hk0, hbc, hbc2]
    have hu : HasDerivAt (fun v : ℝ => env "d" + env "e" * v) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    refine HasDerivAt.congr_deriv (by
      first
        | exact (((Real.hasDerivAt_cosh _).comp t hu).const_mul _).mul_const _
        | exact (((Real.hasDerivAt_sinh _).comp t hu).const_mul _).mul_const _) ?_
    field_simp

theorem rubi677r2_real : rubi677r2.Holds .real := by
  show AntiderivHoldsUnder Interp.real "x" rubi677r2.conditions rubi677r2.body rubi677r2.result
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hk : ∀ᶠ w in 𝓝 t, ∃ k : ℤ, intValue? (env "c" * (env "a" + env "b" * w)) = some k := hF.mono fun w hw => by
    simp only [rubi677r2, Defined] at hw
    obtain ⟨n, hn, -⟩ := hw.1.2.2
    exact ⟨n, by simpa [eval, Interp.real] using hn⟩
  have hcb := int_valued_const hk
  have hlin : ∀ w : ℝ, env "c" * (env "a" + env "b" * w) = env "c" * env "a" := fun w => by
    linear_combination w * hcb
  obtain ⟨k0, hk0⟩ : ∃ k : ℤ, intValue? (env "c" * env "a") = some k := by
    have := hk.self_of_nhds; rwa [hlin] at this
  have hcd := hc _ (List.mem_singleton_self _)
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  obtain ⟨hF0, hD⟩ := hcd
  have hbc : env "b" * env "c" = 0 := by linear_combination hcb
  have hbc2 : env "b" ^ 2 * env "c" ^ 2 = 0 := by rw [← mul_pow, hbc]; ring
  have hD' := hD
  rw [hbc2] at hD
  have he : env "e" ≠ 0 := by intro h; apply hD; rw [h]; ring
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    simp [rubi677r2, Defined, eval, Interp.real, i2, im1, hlin, hk0] at hw ⊢
    first | tauto | (simp_all; done) | (trace_state; sorry)
  · simp [rubi677r2, eval, Interp.real, i2, im1, hlin, hk0, hbc, hbc2]
    have hu : HasDerivAt (fun v : ℝ => env "d" + env "e" * v) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    refine HasDerivAt.congr_deriv (by
      first
        | exact (((Real.hasDerivAt_sinh _).comp t hu).const_mul _).mul_const _
        | exact (((Real.hasDerivAt_cosh _).comp t hu).const_mul _).mul_const _) ?_
    field_simp

theorem rubi677r3_real : rubi677r3.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi677r3.conditions rubi677r3.body rubi677r3.result rubi677r3.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi677r3, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n6 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n7 : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n8 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hk : ∀ᶠ w in 𝓝 t, ∃ k : ℤ, intValue? (env "c" * (env "a" + env "b" * w)) = some k := hF.mono fun w hw => by
    simp only [rubi677r3, Defined] at hw
    obtain ⟨n, hn, -⟩ := hw.1.2.2
    exact ⟨n, by simpa [eval, Interp.real] using hn⟩
  have hcb := int_valued_const hk
  have hlin : ∀ w : ℝ, env "c" * (env "a" + env "b" * w) = env "c" * env "a" := fun w => by
    linear_combination w * hcb
  obtain ⟨k0, hk0⟩ : ∃ k : ℤ, intValue? (env "c" * env "a") = some k := by
    have := hk.self_of_nhds; rwa [hlin] at this
  have hbc : env "b" * env "c" = 0 := by linear_combination hcb
  have hbc2 : env "b" ^ 2 * env "c" ^ 2 = 0 := by rw [← mul_pow, hbc]; ring
  have hcd := hc _ List.mem_cons_self
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  have hcn := hc _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp [Cond.Holds, Defined, eval, Interp.real, hkn] at hcn
  have hkb : 1 < kn := by exact_mod_cast hcn
  have hn0 : ¬ env "n" = 0 := by rw [hkn]; norm_cast; omega
  have hn1 : ¬ env "n" + 1 = 0 := by rw [hkn]; norm_cast; omega
  have hn2 : ¬ env "n" + 2 = 0 := by rw [hkn]; norm_cast; omega
  have hnm1 : ¬ env "n" + -1 = 0 := by rw [hkn]; norm_cast; omega
  have hcd' := hcd.2
  rw [hbc2] at hcd'
  have he : ¬ env "e" = 0 := by intro h; apply hcd'; rw [h]; ring
  have hF0 := hcd.1
  have ha1 : ¬ kn ≤ 1 := by omega
  have ha2 : ¬ kn < 1 := by omega
  have ha3 : ¬ kn < 0 := by omega
  have ha4 : ¬ kn - 2 < 0 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi677r3, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi677r3, Defined, eval, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0] at hw ⊢
    have hch : ¬ Real.cosh (env "d" + env "e" * w) = 0 := (Real.cosh_pos _).ne'
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi677r3, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0] at hw ⊢
    have hch : ¬ Real.cosh (env "d" + env "e" * w) = 0 := (Real.cosh_pos _).ne'
    tauto
  · simp only [rubi677r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi677r3, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, hbc, hbc2] at ht hΦ ⊢
    have hu : HasDerivAt (fun v : ℝ => env "d" + env "e" * v) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    have hS := (Real.hasDerivAt_sinh _).comp t hu
    have hC := (Real.hasDerivAt_cosh _).comp t hu
    have hP := (hasDerivAt_zpow (kn - 1) _ (Or.inr (by omega))).comp t hS
    refine HasDerivAt.congr_deriv ((((hC.const_mul _).mul hP).mul_const _).add ((hΦ.const_mul _).neg)) ?_
    simp only [Function.comp_def]
    rw [hkn]
    have r0 : (kn : ℝ) ≠ 0 := by norm_cast; omega
    have r1 : (kn : ℝ) + 1 ≠ 0 := by norm_cast; omega
    have r2 : (kn : ℝ) + -1 ≠ 0 := by norm_cast; omega
    have hr := Real.cosh_sq_sub_sinh_sq (env "d" + env "e" * t)
    have e1 : Real.sinh (env "d" + env "e" * t) ^ (kn - 1) = Real.sinh (env "d" + env "e" * t) ^ (kn - 2) * Real.sinh (env "d" + env "e" * t) := by
      rw [show kn - 1 = (kn - 2) + 1 by ring, zpow_add' (Or.inr (Or.inl (by omega))), zpow_one]
    have e2 : Real.sinh (env "d" + env "e" * t) ^ kn = Real.sinh (env "d" + env "e" * t) ^ (kn - 2) * Real.sinh (env "d" + env "e" * t) ^ 2 := by
      conv_lhs => rw [show kn = (kn - 2) + 2 by ring]
      rw [zpow_add' (Or.inr (Or.inl (by omega)))]; norm_cast
    rw [show kn - 1 - 1 = kn - 2 by ring, e1, e2]
    generalize Real.sinh (env "d" + env "e" * t) ^ (kn - 2) = P
    push_cast
    generalize Real.sinh (env "d" + env "e" * t) = S at *
    generalize Real.cosh (env "d" + env "e" * t) = C at *
    generalize env "F" ^ k0 = K
    field_simp
    linear_combination (K*P*((kn:ℝ) - 1)) * hr

theorem rubi677r4_real : rubi677r4.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi677r4.conditions rubi677r4.body rubi677r4.result rubi677r4.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi677r4, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n6 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n7 : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n8 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hk : ∀ᶠ w in 𝓝 t, ∃ k : ℤ, intValue? (env "c" * (env "a" + env "b" * w)) = some k := hF.mono fun w hw => by
    simp only [rubi677r4, Defined] at hw
    obtain ⟨n, hn, -⟩ := hw.1.2.2
    exact ⟨n, by simpa [eval, Interp.real] using hn⟩
  have hcb := int_valued_const hk
  have hlin : ∀ w : ℝ, env "c" * (env "a" + env "b" * w) = env "c" * env "a" := fun w => by
    linear_combination w * hcb
  obtain ⟨k0, hk0⟩ : ∃ k : ℤ, intValue? (env "c" * env "a") = some k := by
    have := hk.self_of_nhds; rwa [hlin] at this
  have hbc : env "b" * env "c" = 0 := by linear_combination hcb
  have hbc2 : env "b" ^ 2 * env "c" ^ 2 = 0 := by rw [← mul_pow, hbc]; ring
  have hcd := hc _ List.mem_cons_self
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  have hcn := hc _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp [Cond.Holds, Defined, eval, Interp.real, hkn] at hcn
  have hkb : 1 < kn := by exact_mod_cast hcn
  have hn0 : ¬ env "n" = 0 := by rw [hkn]; norm_cast; omega
  have hn1 : ¬ env "n" + 1 = 0 := by rw [hkn]; norm_cast; omega
  have hn2 : ¬ env "n" + 2 = 0 := by rw [hkn]; norm_cast; omega
  have hnm1 : ¬ env "n" + -1 = 0 := by rw [hkn]; norm_cast; omega
  have hcd' := hcd.2
  rw [hbc2] at hcd'
  have he : ¬ env "e" = 0 := by intro h; apply hcd'; rw [h]; ring
  have hF0 := hcd.1
  have ha1 : ¬ kn ≤ 1 := by omega
  have ha2 : ¬ kn < 1 := by omega
  have ha3 : ¬ kn < 0 := by omega
  have ha4 : ¬ kn - 2 < 0 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi677r4, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi677r4, Defined, eval, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0] at hw ⊢
    have hch : ¬ Real.cosh (env "d" + env "e" * w) = 0 := (Real.cosh_pos _).ne'
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi677r4, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0] at hw ⊢
    have hch : ¬ Real.cosh (env "d" + env "e" * w) = 0 := (Real.cosh_pos _).ne'
    tauto
  · simp only [rubi677r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi677r4, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, hbc, hbc2] at ht hΦ ⊢
    have hu : HasDerivAt (fun v : ℝ => env "d" + env "e" * v) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    have hS := (Real.hasDerivAt_sinh _).comp t hu
    have hC := (Real.hasDerivAt_cosh _).comp t hu
    have hB : Real.cosh (env "d" + env "e" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hP := (hasDerivAt_zpow (kn - 1) _ (Or.inr (by omega))).comp t hC
    refine HasDerivAt.congr_deriv ((((hS.const_mul _).mul hP).mul_const _).add (hΦ.const_mul _)) ?_
    simp only [Function.comp_def]
    rw [hkn]
    have r0 : (kn : ℝ) ≠ 0 := by norm_cast; omega
    have r1 : (kn : ℝ) + 1 ≠ 0 := by norm_cast; omega
    have r2 : (kn : ℝ) + -1 ≠ 0 := by norm_cast; omega
    have hr := Real.cosh_sq_sub_sinh_sq (env "d" + env "e" * t)
    simp only [zpow_sub₀ hB, zpow_add₀ hB, zpow_neg, zpow_one, zpow_ofNat]
    have hP0 : Real.cosh (env "d" + env "e" * t) ^ kn ≠ 0 := zpow_ne_zero _ hB
    generalize Real.cosh (env "d" + env "e" * t) ^ kn = P at *
    push_cast
    generalize Real.sinh (env "d" + env "e" * t) = S at *
    generalize Real.cosh (env "d" + env "e" * t) = C at *
    generalize env "F" ^ k0 = K
    field_simp
    linear_combination (-K*((kn:ℝ) - 1)) * hr

theorem rubi677r7_real : rubi677r7.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi677r7.conditions rubi677r7.body rubi677r7.result rubi677r7.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi677r7, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n6 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n7 : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n8 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hk : ∀ᶠ w in 𝓝 t, ∃ k : ℤ, intValue? (env "c" * (env "a" + env "b" * w)) = some k := hF.mono fun w hw => by
    simp only [rubi677r7, Defined] at hw
    obtain ⟨n, hn, -⟩ := hw.1.2.2
    exact ⟨n, by simpa [eval, Interp.real] using hn⟩
  have hcb := int_valued_const hk
  have hlin : ∀ w : ℝ, env "c" * (env "a" + env "b" * w) = env "c" * env "a" := fun w => by
    linear_combination w * hcb
  obtain ⟨k0, hk0⟩ : ∃ k : ℤ, intValue? (env "c" * env "a") = some k := by
    have := hk.self_of_nhds; rwa [hlin] at this
  have hbc : env "b" * env "c" = 0 := by linear_combination hcb
  have hbc2 : env "b" ^ 2 * env "c" ^ 2 = 0 := by rw [← mul_pow, hbc]; ring
  have hcd := hc _ List.mem_cons_self
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  have hcn := hc _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp [Cond.Holds, Defined, eval, Interp.real, hkn] at hcn
  have hkb : kn < -1 := by exact_mod_cast hcn
  have hcm := hc _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp [Cond.Holds, Defined, eval, Interp.real, hkn] at hcm
  have hk2 : kn ≠ -2 := by intro h; apply hcm; rw [h]; norm_num
  have hn0 : ¬ env "n" = 0 := by rw [hkn]; norm_cast; omega
  have hn1 : ¬ env "n" + 1 = 0 := by rw [hkn]; norm_cast; omega
  have hn2 : ¬ env "n" + 2 = 0 := by rw [hkn]; norm_cast; omega
  have hnm1 : ¬ env "n" + -1 = 0 := by rw [hkn]; norm_cast; omega
  have hnm2 : ¬ env "n" + -2 = 0 := by rw [hkn]; norm_cast; omega
  have hcd' := hcd.2
  rw [hbc2] at hcd'
  have he : ¬ env "e" = 0 := by intro h; apply hcd'; rw [h]; ring
  have hF0 := hcd.1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi677r7, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi677r7, Defined, eval, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0] at hw ⊢
    have hu0 : ¬ (env "d" + env "e" * w) = 0 := hw.2 (by omega)
    have hch : ¬ Real.cosh (env "d" + env "e" * w) = 0 := (Real.cosh_pos _).ne'
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi677r7, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0] at hw ⊢
    have hu0 : ¬ (env "d" + env "e" * w) = 0 := hw.2 (by omega)
    have hch : ¬ Real.cosh (env "d" + env "e" * w) = 0 := (Real.cosh_pos _).ne'
    tauto
  · simp only [rubi677r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi677r7, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, hbc, hbc2] at ht hΦ ⊢
    have hu : HasDerivAt (fun v : ℝ => env "d" + env "e" * v) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    have hS := (Real.hasDerivAt_sinh _).comp t hu
    have hC := (Real.hasDerivAt_cosh _).comp t hu
    have hB : Real.sinh (env "d" + env "e" * t) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; exact ht.2 (by omega) h
    have hP := (hasDerivAt_zpow (kn + 1) _ (Or.inl hB)).comp t hS
    refine HasDerivAt.congr_deriv ((((hC.const_mul _).mul hP).mul_const _).add ((hΦ.const_mul _).neg)) ?_
    simp only [Function.comp_def]
    rw [hkn]
    have r0 : (kn : ℝ) ≠ 0 := by norm_cast; omega
    have r1 : (kn : ℝ) + 1 ≠ 0 := by norm_cast; omega
    have r2 : (kn : ℝ) + -1 ≠ 0 := by norm_cast; omega
    have r3 : (kn : ℝ) + 2 ≠ 0 := by norm_cast; omega
    have hr := Real.cosh_sq_sub_sinh_sq (env "d" + env "e" * t)
    simp only [zpow_sub₀ hB, zpow_add₀ hB, zpow_neg, zpow_one, zpow_ofNat]
    have hP0 : Real.sinh (env "d" + env "e" * t) ^ kn ≠ 0 := zpow_ne_zero _ hB
    generalize Real.sinh (env "d" + env "e" * t) ^ kn = P at *
    push_cast
    generalize Real.sinh (env "d" + env "e" * t) = S at *
    generalize Real.cosh (env "d" + env "e" * t) = C at *
    generalize env "F" ^ k0 = K
    field_simp
    linear_combination (K*((kn:ℝ) + 1)) * hr

theorem rubi477r13_real : rubi477r13.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi477r13.conditions rubi477r13.body rubi477r13.result rubi477r13.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi477r13, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n6 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n7 : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n8 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hk : ∀ᶠ w in 𝓝 t, ∃ k : ℤ, intValue? (env "c" * (env "a" + env "b" * w)) = some k := hF.mono fun w hw => by
    simp only [rubi477r13, Defined] at hw
    obtain ⟨n, hn, -⟩ := hw.1.2.2
    exact ⟨n, by simpa [eval, Interp.real] using hn⟩
  have hcb := int_valued_const hk
  have hlin : ∀ w : ℝ, env "c" * (env "a" + env "b" * w) = env "c" * env "a" := fun w => by
    linear_combination w * hcb
  obtain ⟨k0, hk0⟩ : ∃ k : ℤ, intValue? (env "c" * env "a") = some k := by
    have := hk.self_of_nhds; rwa [hlin] at this
  have hbc : env "b" * env "c" = 0 := by linear_combination hcb
  have hbc2 : env "b" ^ 2 * env "c" ^ 2 = 0 := by rw [← mul_pow, hbc]; ring
  have hcd := hc _ List.mem_cons_self
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  have hcn := hc _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp [Cond.Holds, Defined, eval, Interp.real, hkn] at hcn
  have hkb : kn < -1 := by exact_mod_cast hcn
  have hn0 : ¬ env "n" = 0 := by rw [hkn]; norm_cast; omega
  have hn1 : ¬ env "n" + 1 = 0 := by rw [hkn]; norm_cast; omega
  have hnm1 : ¬ env "n" + -1 = 0 := by rw [hkn]; norm_cast; omega
  have hnm2 : ¬ env "n" + -2 = 0 := by rw [hkn]; norm_cast; omega
  have hcd' := hcd.2
  rw [hbc2] at hcd'
  have he : ¬ env "e" = 0 := by intro h; apply hcd'; rw [h]; ring
  have hF0 := hcd.1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi477r13, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi477r13, Defined, eval, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, Fn.sec, Fn.csc] at hw ⊢
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi477r13, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, Fn.sec, Fn.csc] at hw ⊢
    tauto
  · simp only [rubi477r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi477r13, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, hbc, hbc2, Fn.sec, Fn.csc] at ht hΦ ⊢
    have hu : HasDerivAt (fun v : ℝ => env "d" + env "e" * v) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    have hS := (Real.hasDerivAt_sin _).comp t hu
    have hC := (Real.hasDerivAt_cos _).comp t hu
    have hB : Real.cos (env "d" + env "e" * t) ≠ 0 := ht.2.1
    have hP := (hasDerivAt_zpow (-1 + -kn) _ (Or.inl hB)).comp t hC
    refine HasDerivAt.congr_deriv (((((hP.const_mul _).mul hS).mul_const _).neg).add (hΦ.const_mul _)) ?_
    simp only [Function.comp_def]
    rw [hkn]
    have r0 : (kn : ℝ) ≠ 0 := by norm_cast; omega
    have r1 : (kn : ℝ) + 1 ≠ 0 := by norm_cast; omega
    have r2 : (kn : ℝ) + -1 ≠ 0 := by norm_cast; omega
    have hr := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    simp only [zpow_sub₀ hB, zpow_add₀ hB, zpow_neg, zpow_one, zpow_ofNat]
    have hP0 : Real.cos (env "d" + env "e" * t) ^ kn ≠ 0 := zpow_ne_zero _ hB
    generalize Real.cos (env "d" + env "e" * t) ^ kn = P at *
    push_cast
    generalize Real.sin (env "d" + env "e" * t) = S at *
    generalize Real.cos (env "d" + env "e" * t) = C at *
    generalize env "F" ^ k0 = K
    field_simp
    linear_combination (-K*((kn:ℝ) + 1)) * hr

theorem rubi477r14_real : rubi477r14.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi477r14.conditions rubi477r14.body rubi477r14.result rubi477r14.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi477r14, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n6 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n7 : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n8 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hk : ∀ᶠ w in 𝓝 t, ∃ k : ℤ, intValue? (env "c" * (env "a" + env "b" * w)) = some k := hF.mono fun w hw => by
    simp only [rubi477r14, Defined] at hw
    obtain ⟨n, hn, -⟩ := hw.1.2.2
    exact ⟨n, by simpa [eval, Interp.real] using hn⟩
  have hcb := int_valued_const hk
  have hlin : ∀ w : ℝ, env "c" * (env "a" + env "b" * w) = env "c" * env "a" := fun w => by
    linear_combination w * hcb
  obtain ⟨k0, hk0⟩ : ∃ k : ℤ, intValue? (env "c" * env "a") = some k := by
    have := hk.self_of_nhds; rwa [hlin] at this
  have hbc : env "b" * env "c" = 0 := by linear_combination hcb
  have hbc2 : env "b" ^ 2 * env "c" ^ 2 = 0 := by rw [← mul_pow, hbc]; ring
  have hcd := hc _ List.mem_cons_self
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  have hcn := hc _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp [Cond.Holds, Defined, eval, Interp.real, hkn] at hcn
  have hkb : kn < -1 := by exact_mod_cast hcn
  have hn0 : ¬ env "n" = 0 := by rw [hkn]; norm_cast; omega
  have hn1 : ¬ env "n" + 1 = 0 := by rw [hkn]; norm_cast; omega
  have hnm1 : ¬ env "n" + -1 = 0 := by rw [hkn]; norm_cast; omega
  have hnm2 : ¬ env "n" + -2 = 0 := by rw [hkn]; norm_cast; omega
  have hcd' := hcd.2
  rw [hbc2] at hcd'
  have he : ¬ env "e" = 0 := by intro h; apply hcd'; rw [h]; ring
  have hF0 := hcd.1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi477r14, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi477r14, Defined, eval, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, Fn.sec, Fn.csc] at hw ⊢
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi477r14, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, Fn.sec, Fn.csc] at hw ⊢
    tauto
  · simp only [rubi477r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi477r14, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, hbc, hbc2, Fn.sec, Fn.csc] at ht hΦ ⊢
    have hu : HasDerivAt (fun v : ℝ => env "d" + env "e" * v) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    have hS := (Real.hasDerivAt_sin _).comp t hu
    have hC := (Real.hasDerivAt_cos _).comp t hu
    have hB : Real.sin (env "d" + env "e" * t) ≠ 0 := ht.2.1
    have hP := (hasDerivAt_zpow (-1 + -kn) _ (Or.inl hB)).comp t hS
    refine HasDerivAt.congr_deriv ((((hP.const_mul _).mul hC).mul_const _).add (hΦ.const_mul _)) ?_
    simp only [Function.comp_def]
    rw [hkn]
    have r0 : (kn : ℝ) ≠ 0 := by norm_cast; omega
    have r1 : (kn : ℝ) + 1 ≠ 0 := by norm_cast; omega
    have r2 : (kn : ℝ) + -1 ≠ 0 := by norm_cast; omega
    have hr := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    simp only [zpow_sub₀ hB, zpow_add₀ hB, zpow_neg, zpow_one, zpow_ofNat]
    have hP0 : Real.sin (env "d" + env "e" * t) ^ kn ≠ 0 := zpow_ne_zero _ hB
    generalize Real.sin (env "d" + env "e" * t) ^ kn = P at *
    push_cast
    generalize Real.sin (env "d" + env "e" * t) = S at *
    generalize Real.cos (env "d" + env "e" * t) = C at *
    generalize env "F" ^ k0 = K
    field_simp
    linear_combination (-K*((kn:ℝ) + 1)) * hr

theorem rubi477r17_real : rubi477r17.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi477r17.conditions rubi477r17.body rubi477r17.result rubi477r17.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi477r17, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n6 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n7 : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n8 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hk : ∀ᶠ w in 𝓝 t, ∃ k : ℤ, intValue? (env "c" * (env "a" + env "b" * w)) = some k := hF.mono fun w hw => by
    simp only [rubi477r17, Defined] at hw
    obtain ⟨n, hn, -⟩ := hw.1.2.2
    exact ⟨n, by simpa [eval, Interp.real] using hn⟩
  have hcb := int_valued_const hk
  have hlin : ∀ w : ℝ, env "c" * (env "a" + env "b" * w) = env "c" * env "a" := fun w => by
    linear_combination w * hcb
  obtain ⟨k0, hk0⟩ : ∃ k : ℤ, intValue? (env "c" * env "a") = some k := by
    have := hk.self_of_nhds; rwa [hlin] at this
  have hbc : env "b" * env "c" = 0 := by linear_combination hcb
  have hbc2 : env "b" ^ 2 * env "c" ^ 2 = 0 := by rw [← mul_pow, hbc]; ring
  have hcd := hc _ List.mem_cons_self
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  have hcn := hc _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp [Cond.Holds, Defined, eval, Interp.real, hkn] at hcn
  have hkb : 1 < kn := by exact_mod_cast hcn
  have hcm := hc _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp [Cond.Holds, Defined, eval, Interp.real, hkn] at hcm
  have hk2 : kn ≠ 2 := by intro h; apply hcm; rw [h]; norm_num
  have hn0 : ¬ env "n" = 0 := by rw [hkn]; norm_cast; omega
  have hn1 : ¬ env "n" + 1 = 0 := by rw [hkn]; norm_cast; omega
  have hn2 : ¬ env "n" + 2 = 0 := by rw [hkn]; norm_cast; omega
  have hnm1 : ¬ env "n" + -1 = 0 := by rw [hkn]; norm_cast; omega
  have hnm2 : ¬ env "n" + -2 = 0 := by rw [hkn]; norm_cast; omega
  have hcd' := hcd.2
  rw [hbc2] at hcd'
  have he : ¬ env "e" = 0 := by intro h; apply hcd'; rw [h]; ring
  have hF0 := hcd.1
  have ha1 : ¬ kn ≤ 1 := by omega
  have ha2 : ¬ kn < 1 := by omega
  have ha3 : ¬ kn < 0 := by omega
  have ha4 : ¬ kn - 2 < 0 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi477r17, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi477r17, Defined, eval, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, Fn.sec, Fn.csc] at hw ⊢
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi477r17, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, Fn.sec, Fn.csc] at hw ⊢
    tauto
  · simp only [rubi477r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi477r17, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, hbc, hbc2, Fn.sec, Fn.csc] at ht hΦ ⊢
    have hu : HasDerivAt (fun v : ℝ => env "d" + env "e" * v) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    have hS := (Real.hasDerivAt_sin _).comp t hu
    have hC := (Real.hasDerivAt_cos _).comp t hu
    have hB : Real.cos (env "d" + env "e" * t) ≠ 0 := ht.2.1
    have hP := (hasDerivAt_zpow (1 - kn) _ (Or.inl hB)).comp t hC
    refine HasDerivAt.congr_deriv ((((hP.const_mul _).mul hS).mul_const _).add (hΦ.const_mul _)) ?_
    simp only [Function.comp_def]
    rw [hkn]
    have r0 : (kn : ℝ) ≠ 0 := by norm_cast; omega
    have r1 : (kn : ℝ) + 1 ≠ 0 := by norm_cast; omega
    have r2 : (kn : ℝ) + -1 ≠ 0 := by norm_cast; omega
    have r3 : (kn : ℝ) + -2 ≠ 0 := by norm_cast; omega
    have hr := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    simp only [zpow_sub₀ hB, zpow_add₀ hB, zpow_neg, zpow_one, zpow_ofNat]
    have hP0 : Real.cos (env "d" + env "e" * t) ^ kn ≠ 0 := zpow_ne_zero _ hB
    generalize Real.cos (env "d" + env "e" * t) ^ kn = P at *
    push_cast
    generalize Real.sin (env "d" + env "e" * t) = S at *
    generalize Real.cos (env "d" + env "e" * t) = C at *
    generalize env "F" ^ k0 = K
    field_simp
    linear_combination (K*((kn:ℝ) - 1)) * hr

theorem rubi477r18_real : rubi477r18.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi477r18.conditions rubi477r18.body rubi477r18.result rubi477r18.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi477r18, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + -1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" - 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n6 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n7 : intValue? (env "n" + -1 * 1) = some (kn - 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n8 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hk : ∀ᶠ w in 𝓝 t, ∃ k : ℤ, intValue? (env "c" * (env "a" + env "b" * w)) = some k := hF.mono fun w hw => by
    simp only [rubi477r18, Defined] at hw
    obtain ⟨n, hn, -⟩ := hw.1.2.2
    exact ⟨n, by simpa [eval, Interp.real] using hn⟩
  have hcb := int_valued_const hk
  have hlin : ∀ w : ℝ, env "c" * (env "a" + env "b" * w) = env "c" * env "a" := fun w => by
    linear_combination w * hcb
  obtain ⟨k0, hk0⟩ : ∃ k : ℤ, intValue? (env "c" * env "a") = some k := by
    have := hk.self_of_nhds; rwa [hlin] at this
  have hbc : env "b" * env "c" = 0 := by linear_combination hcb
  have hbc2 : env "b" ^ 2 * env "c" ^ 2 = 0 := by rw [← mul_pow, hbc]; ring
  have hcd := hc _ List.mem_cons_self
  simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at hcd
  have hcn := hc _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp [Cond.Holds, Defined, eval, Interp.real, hkn] at hcn
  have hkb : 1 < kn := by exact_mod_cast hcn
  have hcm := hc _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp [Cond.Holds, Defined, eval, Interp.real, hkn] at hcm
  have hk2 : kn ≠ 2 := by intro h; apply hcm; rw [h]; norm_num
  have hn0 : ¬ env "n" = 0 := by rw [hkn]; norm_cast; omega
  have hn1 : ¬ env "n" + 1 = 0 := by rw [hkn]; norm_cast; omega
  have hn2 : ¬ env "n" + 2 = 0 := by rw [hkn]; norm_cast; omega
  have hnm1 : ¬ env "n" + -1 = 0 := by rw [hkn]; norm_cast; omega
  have hnm2 : ¬ env "n" + -2 = 0 := by rw [hkn]; norm_cast; omega
  have hcd' := hcd.2
  rw [hbc2] at hcd'
  have he : ¬ env "e" = 0 := by intro h; apply hcd'; rw [h]; ring
  have hF0 := hcd.1
  have ha1 : ¬ kn ≤ 1 := by omega
  have ha2 : ¬ kn < 1 := by omega
  have ha3 : ¬ kn < 0 := by omega
  have ha4 : ¬ kn - 2 < 0 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi477r18, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi477r18, Defined, eval, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, Fn.sec, Fn.csc] at hw ⊢
    tauto
  · filter_upwards [hF] with w hw
    simp [rubi477r18, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, Fn.sec, Fn.csc] at hw ⊢
    tauto
  · simp only [rubi477r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    simp [rubi477r18, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n1, n2, n3, n4, n5, n6, n7, n8, hlin, hk0, hbc, hbc2, Fn.sec, Fn.csc] at ht hΦ ⊢
    have hu : HasDerivAt (fun v : ℝ => env "d" + env "e" * v) (env "e") t := by
      simpa using ((hasDerivAt_id t).const_mul (env "e")).const_add (env "d")
    have hS := (Real.hasDerivAt_sin _).comp t hu
    have hC := (Real.hasDerivAt_cos _).comp t hu
    have hB : Real.sin (env "d" + env "e" * t) ≠ 0 := ht.2.1
    have hP := (hasDerivAt_zpow (1 - kn) _ (Or.inl hB)).comp t hS
    refine HasDerivAt.congr_deriv (((((hP.const_mul _).mul hC).mul_const _).neg).add (hΦ.const_mul _)) ?_
    simp only [Function.comp_def]
    rw [hkn]
    have r0 : (kn : ℝ) ≠ 0 := by norm_cast; omega
    have r1 : (kn : ℝ) + 1 ≠ 0 := by norm_cast; omega
    have r2 : (kn : ℝ) + -1 ≠ 0 := by norm_cast; omega
    have r3 : (kn : ℝ) + -2 ≠ 0 := by norm_cast; omega
    have hr := Real.sin_sq_add_cos_sq (env "d" + env "e" * t)
    simp only [zpow_sub₀ hB, zpow_add₀ hB, zpow_neg, zpow_one, zpow_ofNat]
    have hP0 : Real.sin (env "d" + env "e" * t) ^ kn ≠ 0 := zpow_ne_zero _ hB
    generalize Real.sin (env "d" + env "e" * t) ^ kn = P at *
    push_cast
    generalize Real.sin (env "d" + env "e" * t) = S at *
    generalize Real.cos (env "d" + env "e" * t) = C at *
    generalize env "F" ^ k0 = K
    field_simp
    linear_combination (K*((kn:ℝ) - 1)) * hr

end OSR.IntegrationRec155
