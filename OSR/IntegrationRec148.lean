import OSR.IntegrationRec91

/-!
# Integration (RUBI): `tan² = sec² - 1` reductions

4.7.6 #10 to #13 and 6.7.6 #5, #10 to #13 lower the power of tan, cot, tanh or
coth by two with `tan² = sec² - 1`, `cot² = csc² - 1`, `tanh² = 1 - sech²` and
`coth² = 1 + csch²`.  Proved over ℝ (sec, csc, sech, csch and coth have no
complex interpretation in the fragment).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec148

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 4.7.6 #10 -/
def rubi476r10 : CRule where
  id := "integration.rubi_4_7_6_r10"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .sec (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.int (-1)) (.var "I1")) (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .sec (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.int 3))) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "m", "p"]
  conditions := [.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))),
    .gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)]
  priority := 11822
  description := "RUBI 4.7.6 #10"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:10" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#10"

/-- RUBI 4.7.6 #11 -/
def rubi476r11 : CRule where
  id := "integration.rubi_4_7_6_r11"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.int (-1)) (.var "I1")) (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 2)))) (.pow (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))),
    .gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)]
  priority := 11823
  description := "RUBI 4.7.6 #11"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:11" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#11"

/-- RUBI 4.7.6 #12 -/
def rubi476r12 : CRule where
  id := "integration.rubi_4_7_6_r12"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .csc (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .cot (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.int (-1)) (.var "I1")) (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .csc (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .cot (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .csc (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.int 3))) (.pow (.app1 .cot (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "m", "p"]
  conditions := [.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))),
    .gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)]
  priority := 11824
  description := "RUBI 4.7.6 #12"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:12" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#12"

/-- RUBI 4.7.6 #13 -/
def rubi476r13 : CRule where
  id := "integration.rubi_4_7_6_r13"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .csc (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .cot (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.int (-1)) (.var "I1")) (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .csc (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .cot (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .csc (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 2)))) (.pow (.app1 .cot (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))),
    .gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)]
  priority := 11825
  description := "RUBI 4.7.6 #13"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:13" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#13"

/-- RUBI 6.7.6 #5 -/
def rubi676r5 : CRule where
  id := "integration.rubi_6_7_6_r5"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.var "I1") (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 11826
  description := "RUBI 6.7.6 #5"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:5" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#5"

/-- RUBI 6.7.6 #10 -/
def rubi676r10 : CRule where
  id := "integration.rubi_6_7_6_r10"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .sech (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.var "I1") (.app2 .mul (.int (-1)) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .sech (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.int 3))) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "m", "p"]
  conditions := [.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))),
    .gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)]
  priority := 11827
  description := "RUBI 6.7.6 #10"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:10" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#10"

/-- RUBI 6.7.6 #11 -/
def rubi676r11 : CRule where
  id := "integration.rubi_6_7_6_r11"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.var "I1") (.app2 .mul (.int (-1)) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 2)))) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))),
    .gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)]
  priority := 11828
  description := "RUBI 6.7.6 #11"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:11" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#11"

/-- RUBI 6.7.6 #12 -/
def rubi676r12 : CRule where
  id := "integration.rubi_6_7_6_r12"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .csch (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.var "I1") (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .csch (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.int 3))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "m", "p"]
  conditions := [.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))),
    .gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)]
  priority := 11829
  description := "RUBI 6.7.6 #12"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:12" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#12"

/-- RUBI 6.7.6 #13 -/
def rubi676r13 : CRule where
  id := "integration.rubi_6_7_6_r13"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.var "I1") (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 2)))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))),
    .gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)]
  priority := 11830
  description := "RUBI 6.7.6 #13"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:13" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#13"

/-! ## Proofs -/

theorem rubi476r10_real : rubi476r10.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi476r10.conditions rubi476r10.body rubi476r10.result rubi476r10.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have hch : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi476r10, Defined, eval, Interp.real, hk_m] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi476r10, Defined, eval, Interp.real, hk_m, hk_p] at h
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p3 : intValue? (env "p" + -2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p4 : intValue? (env "p" - 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p5 : intValue? (env "p" + -1 * 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp2 : 2 ≤ kp := by
    have hj := hc (.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1))))) (by simp [rubi476r10])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at hj
    obtain ⟨j, hj⟩ := hj
    have h2 := hc (.gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)) (by simp [rubi476r10])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at h2
    have := (intValue?_eq _ _).1 hj; rw [hkp] at this h2
    have hkj : (kp : ℝ) = 2 * j := by linarith
    have hkj' : kp = 2 * j := by exact_mod_cast hkj
    have : (0 : ℝ) < kp := by
      first | linarith | nlinarith | (have := h2; positivity) | (trace_state; sorry)
    have : 0 < kp := by exact_mod_cast this
    omega
  have hq1 : ¬ kp - 2 < 0 := by omega
  have hq2 : ¬ kp < 2 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi476r10, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi476r10, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_p, p3, p4, p5, Fn.sec, Fn.csc, hq1, hq2] at hw ⊢ <;>
    first | tauto | (refine ⟨by tauto, by tauto, fun _ => ?_⟩; simp [Fn.coth, Real.tanh_eq_sinh_div_cosh, hch]; tauto) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi476r10, Defined, eval, recEnv]
  · simp only [rubi476r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi476r10, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_p, p3, p4, p5, Fn.sec, Fn.csc, hq1, hq2] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.neg).add hΦ2
        | exact hΦ1.add (hΦ2.neg)
        | exact hΦ1.add hΦ2
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)) ?_
    have hrel := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
    have hB : Real.cos (env "a" + env "b" * t) ≠ 0 := by first | assumption | tauto | (trace_state; sorry)
    rw [show Real.tan (env "a" + env "b" * t) ^ kp = Real.tan (env "a" + env "b" * t) ^ (kp - 2) * Real.tan (env "a" + env "b" * t) ^ (2 : ℤ) by
      rw [← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; ring]
    generalize Real.tan (env "a" + env "b" * t) ^ (kp - 2) = Q
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ⊢
    simp only [Real.tan_eq_sin_div_cos] at ⊢
    try generalize Real.cos (env "a" + env "b" * t) ^ kn = P
    generalize (env "c" + env "d" * t) ^ km = M
    generalize Real.sin (env "a" + env "b" * t) = S at *
    generalize Real.cos (env "a" + env "b" * t) = C at *
    field_simp
    linear_combination (-M*Q) * hrel

theorem rubi476r11_real : rubi476r11.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi476r11.conditions rubi476r11.body rubi476r11.result rubi476r11.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have hch : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi476r11, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi476r11, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi476r11, Defined, eval, Interp.real, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p] at h
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p3 : intValue? (env "p" + -2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p4 : intValue? (env "p" - 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p5 : intValue? (env "p" + -1 * 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp2 : 2 ≤ kp := by
    have hj := hc (.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1))))) (by simp [rubi476r11])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at hj
    obtain ⟨j, hj⟩ := hj
    have h2 := hc (.gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)) (by simp [rubi476r11])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at h2
    have := (intValue?_eq _ _).1 hj; rw [hkp] at this h2
    have hkj : (kp : ℝ) = 2 * j := by linarith
    have hkj' : kp = 2 * j := by exact_mod_cast hkj
    have : (0 : ℝ) < kp := by
      first | linarith | nlinarith | (have := h2; positivity) | (trace_state; sorry)
    have : 0 < kp := by exact_mod_cast this
    omega
  have hq1 : ¬ kp - 2 < 0 := by omega
  have hq2 : ¬ kp < 2 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi476r11, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi476r11, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p, p3, p4, p5, Fn.sec, Fn.csc, hq1, hq2] at hw ⊢ <;>
    first | tauto | (refine ⟨by tauto, by tauto, fun _ => ?_⟩; simp [Fn.coth, Real.tanh_eq_sinh_div_cosh, hch]; tauto) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi476r11, Defined, eval, recEnv]
  · simp only [rubi476r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi476r11, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p, p3, p4, p5, Fn.sec, Fn.csc, hq1, hq2] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.neg).add hΦ2
        | exact hΦ1.add (hΦ2.neg)
        | exact hΦ1.add hΦ2
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)) ?_
    have hrel := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
    have hB : Real.cos (env "a" + env "b" * t) ≠ 0 := by first | assumption | tauto | (trace_state; sorry)
    rw [show Real.tan (env "a" + env "b" * t) ^ kp = Real.tan (env "a" + env "b" * t) ^ (kp - 2) * Real.tan (env "a" + env "b" * t) ^ (2 : ℤ) by
      rw [← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; ring]
    generalize Real.tan (env "a" + env "b" * t) ^ (kp - 2) = Q
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ⊢
    simp only [Real.tan_eq_sin_div_cos] at ⊢
    try generalize Real.cos (env "a" + env "b" * t) ^ kn = P
    generalize (env "c" + env "d" * t) ^ km = M
    generalize Real.sin (env "a" + env "b" * t) = S at *
    generalize Real.cos (env "a" + env "b" * t) = C at *
    field_simp
    linear_combination (-M*Q/P) * hrel

theorem rubi476r12_real : rubi476r12.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi476r12.conditions rubi476r12.body rubi476r12.result rubi476r12.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have hch : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi476r12, Defined, eval, Interp.real, hk_m] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi476r12, Defined, eval, Interp.real, hk_m, hk_p] at h
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p3 : intValue? (env "p" + -2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p4 : intValue? (env "p" - 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p5 : intValue? (env "p" + -1 * 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp2 : 2 ≤ kp := by
    have hj := hc (.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1))))) (by simp [rubi476r12])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at hj
    obtain ⟨j, hj⟩ := hj
    have h2 := hc (.gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)) (by simp [rubi476r12])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at h2
    have := (intValue?_eq _ _).1 hj; rw [hkp] at this h2
    have hkj : (kp : ℝ) = 2 * j := by linarith
    have hkj' : kp = 2 * j := by exact_mod_cast hkj
    have : (0 : ℝ) < kp := by
      first | linarith | nlinarith | (have := h2; positivity) | (trace_state; sorry)
    have : 0 < kp := by exact_mod_cast this
    omega
  have hq1 : ¬ kp - 2 < 0 := by omega
  have hq2 : ¬ kp < 2 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi476r12, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi476r12, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_p, p3, p4, p5, Fn.sec, Fn.csc, hq1, hq2] at hw ⊢ <;>
    first | tauto | (refine ⟨by tauto, by tauto, fun _ => ?_⟩; simp [Fn.coth, Real.tanh_eq_sinh_div_cosh, hch]; tauto) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi476r12, Defined, eval, recEnv]
  · simp only [rubi476r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi476r12, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_p, p3, p4, p5, Fn.sec, Fn.csc, hq1, hq2] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.neg).add hΦ2
        | exact hΦ1.add (hΦ2.neg)
        | exact hΦ1.add hΦ2
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)) ?_
    have hrel := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
    have hB : Real.sin (env "a" + env "b" * t) ≠ 0 := by first | assumption | tauto | (trace_state; sorry)
    rw [show Real.cot (env "a" + env "b" * t) ^ kp = Real.cot (env "a" + env "b" * t) ^ (kp - 2) * Real.cot (env "a" + env "b" * t) ^ (2 : ℤ) by
      rw [← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; ring]
    generalize Real.cot (env "a" + env "b" * t) ^ (kp - 2) = Q
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ⊢
    simp only [Real.cot_eq_cos_div_sin] at ⊢
    try generalize Real.sin (env "a" + env "b" * t) ^ kn = P
    generalize (env "c" + env "d" * t) ^ km = M
    generalize Real.sin (env "a" + env "b" * t) = S at *
    generalize Real.cos (env "a" + env "b" * t) = C at *
    field_simp
    linear_combination (-M*Q) * hrel

theorem rubi476r13_real : rubi476r13.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi476r13.conditions rubi476r13.body rubi476r13.result rubi476r13.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have hch : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi476r13, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi476r13, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi476r13, Defined, eval, Interp.real, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p] at h
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p3 : intValue? (env "p" + -2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p4 : intValue? (env "p" - 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p5 : intValue? (env "p" + -1 * 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp2 : 2 ≤ kp := by
    have hj := hc (.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1))))) (by simp [rubi476r13])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at hj
    obtain ⟨j, hj⟩ := hj
    have h2 := hc (.gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)) (by simp [rubi476r13])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at h2
    have := (intValue?_eq _ _).1 hj; rw [hkp] at this h2
    have hkj : (kp : ℝ) = 2 * j := by linarith
    have hkj' : kp = 2 * j := by exact_mod_cast hkj
    have : (0 : ℝ) < kp := by
      first | linarith | nlinarith | (have := h2; positivity) | (trace_state; sorry)
    have : 0 < kp := by exact_mod_cast this
    omega
  have hq1 : ¬ kp - 2 < 0 := by omega
  have hq2 : ¬ kp < 2 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi476r13, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi476r13, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p, p3, p4, p5, Fn.sec, Fn.csc, hq1, hq2] at hw ⊢ <;>
    first | tauto | (refine ⟨by tauto, by tauto, fun _ => ?_⟩; simp [Fn.coth, Real.tanh_eq_sinh_div_cosh, hch]; tauto) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi476r13, Defined, eval, recEnv]
  · simp only [rubi476r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi476r13, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p, p3, p4, p5, Fn.sec, Fn.csc, hq1, hq2] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.neg).add hΦ2
        | exact hΦ1.add (hΦ2.neg)
        | exact hΦ1.add hΦ2
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)) ?_
    have hrel := Real.sin_sq_add_cos_sq (env "a" + env "b" * t)
    have hB : Real.sin (env "a" + env "b" * t) ≠ 0 := by first | assumption | tauto | (trace_state; sorry)
    rw [show Real.cot (env "a" + env "b" * t) ^ kp = Real.cot (env "a" + env "b" * t) ^ (kp - 2) * Real.cot (env "a" + env "b" * t) ^ (2 : ℤ) by
      rw [← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; ring]
    generalize Real.cot (env "a" + env "b" * t) ^ (kp - 2) = Q
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ⊢
    simp only [Real.cot_eq_cos_div_sin] at ⊢
    try generalize Real.sin (env "a" + env "b" * t) ^ kn = P
    generalize (env "c" + env "d" * t) ^ km = M
    generalize Real.sin (env "a" + env "b" * t) = S at *
    generalize Real.cos (env "a" + env "b" * t) = C at *
    field_simp
    linear_combination (-M*Q/P) * hrel

theorem rubi676r5_real : rubi676r5.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi676r5.conditions rubi676r5.body rubi676r5.result rubi676r5.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have hch : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r5, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r5, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r5, Defined, eval, Interp.real, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p] at h
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p3 : intValue? (env "p" + -2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p4 : intValue? (env "p" - 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p5 : intValue? (env "p" + -1 * 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp1 : 0 < kp := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi676r5])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkp] at h
    simp [Interp.real] at h
    exact_mod_cast h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi676r5, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi676r5, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p, p3, p4, p5, Fn.sech, Fn.csch, hch] at hw ⊢ <;>
    first | tauto | (refine ⟨by tauto, by tauto, fun _ => ?_⟩; simp [Fn.coth, Real.tanh_eq_sinh_div_cosh, hch]; tauto) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi676r5, Defined, eval, recEnv]
  · simp only [rubi676r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi676r5, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p, p3, p4, p5, Fn.sech, Fn.csch, hch] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.neg).add hΦ2
        | exact hΦ1.add (hΦ2.neg)
        | exact hΦ1.add hΦ2
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)) ?_
    have hrel := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
    have hC0 : Real.cosh (env "a" + env "b" * t) ≠ 0 := hch _
    have hS0 : Real.sinh (env "a" + env "b" * t) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; tauto
    have hB : Real.cosh (env "a" + env "b" * t) ≠ 0 := by first | assumption | tauto
    rw [show Fn.coth (env "a" + env "b" * t) ^ kp = Fn.coth (env "a" + env "b" * t) ^ (kp - 2) * Fn.coth (env "a" + env "b" * t) ^ (2 : ℤ) by
      rw [← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; ring]
    generalize Fn.coth (env "a" + env "b" * t) ^ (kp - 2) = Q
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ⊢
    simp only [Fn.coth, Real.tanh_eq_sinh_div_cosh] at ⊢
    try generalize Real.cosh (env "a" + env "b" * t) ^ kn = P
    generalize (env "c" + env "d" * t) ^ km = M
    generalize Real.sinh (env "a" + env "b" * t) = S at *
    generalize Real.cosh (env "a" + env "b" * t) = C at *
    field_simp
    linear_combination (-M*P*Q) * hrel

theorem rubi676r10_real : rubi676r10.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi676r10.conditions rubi676r10.body rubi676r10.result rubi676r10.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have hch : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r10, Defined, eval, Interp.real, hk_m] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r10, Defined, eval, Interp.real, hk_m, hk_p] at h
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p3 : intValue? (env "p" + -2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p4 : intValue? (env "p" - 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p5 : intValue? (env "p" + -1 * 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp2 : 2 ≤ kp := by
    have hj := hc (.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1))))) (by simp [rubi676r10])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at hj
    obtain ⟨j, hj⟩ := hj
    have h2 := hc (.gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)) (by simp [rubi676r10])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at h2
    have := (intValue?_eq _ _).1 hj; rw [hkp] at this h2
    have hkj : (kp : ℝ) = 2 * j := by linarith
    have hkj' : kp = 2 * j := by exact_mod_cast hkj
    have : (0 : ℝ) < kp := by
      first | linarith | nlinarith | (have := h2; positivity) | (trace_state; sorry)
    have : 0 < kp := by exact_mod_cast this
    omega
  have hq1 : ¬ kp - 2 < 0 := by omega
  have hq2 : ¬ kp < 2 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi676r10, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi676r10, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_p, p3, p4, p5, Fn.sech, Fn.csch, hch, hq1, hq2] at hw ⊢ <;>
    first | tauto | (refine ⟨by tauto, by tauto, fun _ => ?_⟩; simp [Fn.coth, Real.tanh_eq_sinh_div_cosh, hch]; tauto) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi676r10, Defined, eval, recEnv]
  · simp only [rubi676r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi676r10, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_p, p3, p4, p5, Fn.sech, Fn.csch, hch, hq1, hq2] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.neg).add hΦ2
        | exact hΦ1.add (hΦ2.neg)
        | exact hΦ1.add hΦ2
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)) ?_
    have hrel := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
    have hC0 : Real.cosh (env "a" + env "b" * t) ≠ 0 := hch _
    have hB : Real.cosh (env "a" + env "b" * t) ≠ 0 := by first | assumption | tauto
    rw [show Real.tanh (env "a" + env "b" * t) ^ kp = Real.tanh (env "a" + env "b" * t) ^ (kp - 2) * Real.tanh (env "a" + env "b" * t) ^ (2 : ℤ) by
      rw [← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; ring]
    generalize Real.tanh (env "a" + env "b" * t) ^ (kp - 2) = Q
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ⊢
    simp only [Real.tanh_eq_sinh_div_cosh] at ⊢
    try generalize Real.cosh (env "a" + env "b" * t) ^ kn = P
    generalize (env "c" + env "d" * t) ^ km = M
    generalize Real.sinh (env "a" + env "b" * t) = S at *
    generalize Real.cosh (env "a" + env "b" * t) = C at *
    field_simp
    linear_combination (M*Q) * hrel

theorem rubi676r11_real : rubi676r11.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi676r11.conditions rubi676r11.body rubi676r11.result rubi676r11.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have hch : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r11, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r11, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r11, Defined, eval, Interp.real, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p] at h
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p3 : intValue? (env "p" + -2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p4 : intValue? (env "p" - 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p5 : intValue? (env "p" + -1 * 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp2 : 2 ≤ kp := by
    have hj := hc (.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1))))) (by simp [rubi676r11])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at hj
    obtain ⟨j, hj⟩ := hj
    have h2 := hc (.gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)) (by simp [rubi676r11])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at h2
    have := (intValue?_eq _ _).1 hj; rw [hkp] at this h2
    have hkj : (kp : ℝ) = 2 * j := by linarith
    have hkj' : kp = 2 * j := by exact_mod_cast hkj
    have : (0 : ℝ) < kp := by
      first | linarith | nlinarith | (have := h2; positivity) | (trace_state; sorry)
    have : 0 < kp := by exact_mod_cast this
    omega
  have hq1 : ¬ kp - 2 < 0 := by omega
  have hq2 : ¬ kp < 2 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi676r11, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi676r11, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p, p3, p4, p5, Fn.sech, Fn.csch, hch, hq1, hq2] at hw ⊢ <;>
    first | tauto | (refine ⟨by tauto, by tauto, fun _ => ?_⟩; simp [Fn.coth, Real.tanh_eq_sinh_div_cosh, hch]; tauto) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi676r11, Defined, eval, recEnv]
  · simp only [rubi676r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi676r11, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p, p3, p4, p5, Fn.sech, Fn.csch, hch, hq1, hq2] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.neg).add hΦ2
        | exact hΦ1.add (hΦ2.neg)
        | exact hΦ1.add hΦ2
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)) ?_
    have hrel := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
    have hC0 : Real.cosh (env "a" + env "b" * t) ≠ 0 := hch _
    have hB : Real.cosh (env "a" + env "b" * t) ≠ 0 := by first | assumption | tauto
    rw [show Real.tanh (env "a" + env "b" * t) ^ kp = Real.tanh (env "a" + env "b" * t) ^ (kp - 2) * Real.tanh (env "a" + env "b" * t) ^ (2 : ℤ) by
      rw [← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; ring]
    generalize Real.tanh (env "a" + env "b" * t) ^ (kp - 2) = Q
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ⊢
    simp only [Real.tanh_eq_sinh_div_cosh] at ⊢
    try generalize Real.cosh (env "a" + env "b" * t) ^ kn = P
    generalize (env "c" + env "d" * t) ^ km = M
    generalize Real.sinh (env "a" + env "b" * t) = S at *
    generalize Real.cosh (env "a" + env "b" * t) = C at *
    field_simp
    linear_combination (M*Q/P) * hrel

theorem rubi676r12_real : rubi676r12.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi676r12.conditions rubi676r12.body rubi676r12.result rubi676r12.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have hch : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r12, Defined, eval, Interp.real, hk_m] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r12, Defined, eval, Interp.real, hk_m, hk_p] at h
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p3 : intValue? (env "p" + -2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p4 : intValue? (env "p" - 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p5 : intValue? (env "p" + -1 * 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp2 : 2 ≤ kp := by
    have hj := hc (.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1))))) (by simp [rubi676r12])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at hj
    obtain ⟨j, hj⟩ := hj
    have h2 := hc (.gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)) (by simp [rubi676r12])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at h2
    have := (intValue?_eq _ _).1 hj; rw [hkp] at this h2
    have hkj : (kp : ℝ) = 2 * j := by linarith
    have hkj' : kp = 2 * j := by exact_mod_cast hkj
    have : (0 : ℝ) < kp := by
      first | linarith | nlinarith | (have := h2; positivity) | (trace_state; sorry)
    have : 0 < kp := by exact_mod_cast this
    omega
  have hq1 : ¬ kp - 2 < 0 := by omega
  have hq2 : ¬ kp < 2 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi676r12, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi676r12, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_p, p3, p4, p5, Fn.sech, Fn.csch, hch, hq1, hq2] at hw ⊢ <;>
    first | tauto | (refine ⟨by tauto, by tauto, fun _ => ?_⟩; simp [Fn.coth, Real.tanh_eq_sinh_div_cosh, hch]; tauto) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi676r12, Defined, eval, recEnv]
  · simp only [rubi676r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi676r12, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_p, p3, p4, p5, Fn.sech, Fn.csch, hch, hq1, hq2] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.neg).add hΦ2
        | exact hΦ1.add (hΦ2.neg)
        | exact hΦ1.add hΦ2
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)) ?_
    have hrel := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
    have hC0 : Real.cosh (env "a" + env "b" * t) ≠ 0 := hch _
    have hS0 : Real.sinh (env "a" + env "b" * t) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; tauto
    have hB : Real.sinh (env "a" + env "b" * t) ≠ 0 := by first | assumption | tauto
    rw [show Fn.coth (env "a" + env "b" * t) ^ kp = Fn.coth (env "a" + env "b" * t) ^ (kp - 2) * Fn.coth (env "a" + env "b" * t) ^ (2 : ℤ) by
      rw [← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; ring]
    generalize Fn.coth (env "a" + env "b" * t) ^ (kp - 2) = Q
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ⊢
    simp only [Fn.coth, Real.tanh_eq_sinh_div_cosh] at ⊢
    try generalize Real.sinh (env "a" + env "b" * t) ^ kn = P
    generalize (env "c" + env "d" * t) ^ km = M
    generalize Real.sinh (env "a" + env "b" * t) = S at *
    generalize Real.cosh (env "a" + env "b" * t) = C at *
    field_simp
    linear_combination (-M*Q) * hrel

theorem rubi676r13_real : rubi676r13.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi676r13.conditions rubi676r13.body rubi676r13.result rubi676r13.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i3 : intValue? (3 : ℝ) = some 3 := (intValue?_eq _ _).2 (by norm_num)
  have hch : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r13, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r13, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi676r13, Defined, eval, Interp.real, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p] at h
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have p3 : intValue? (env "p" + -2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p4 : intValue? (env "p" - 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have p5 : intValue? (env "p" + -1 * 2) = some (kp - 2) := (intValue?_eq _ _).2 (by rw [hkp]; push_cast; ring)
  have hp2 : 2 ≤ kp := by
    have hj := hc (.int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1))))) (by simp [rubi676r13])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at hj
    obtain ⟨j, hj⟩ := hj
    have h2 := hc (.gt (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))) (.int 0)) (by simp [rubi676r13])
    simp [Cond.Holds, Defined, eval, Interp.real, im1] at h2
    have := (intValue?_eq _ _).1 hj; rw [hkp] at this h2
    have hkj : (kp : ℝ) = 2 * j := by linarith
    have hkj' : kp = 2 * j := by exact_mod_cast hkj
    have : (0 : ℝ) < kp := by
      first | linarith | nlinarith | (have := h2; positivity) | (trace_state; sorry)
    have : 0 < kp := by exact_mod_cast this
    omega
  have hq1 : ¬ kp - 2 < 0 := by omega
  have hq2 : ¬ kp < 2 := by omega
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi676r13, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi676r13, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p, p3, p4, p5, Fn.sech, Fn.csch, hch, hq1, hq2] at hw ⊢ <;>
    first | tauto | (refine ⟨by tauto, by tauto, fun _ => ?_⟩; simp [Fn.coth, Real.tanh_eq_sinh_div_cosh, hch]; tauto) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi676r13, Defined, eval, recEnv]
  · simp only [rubi676r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi676r13, Defined, eval, Interp.real, i2, im1, i3, hk_m, hk_n, n1, n2, n3, n4, n5, hk_p, p3, p4, p5, Fn.sech, Fn.csch, hch, hq1, hq2] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.neg).add hΦ2
        | exact hΦ1.add (hΦ2.neg)
        | exact hΦ1.add hΦ2
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)) ?_
    have hrel := Real.cosh_sq_sub_sinh_sq (env "a" + env "b" * t)
    have hC0 : Real.cosh (env "a" + env "b" * t) ≠ 0 := hch _
    have hS0 : Real.sinh (env "a" + env "b" * t) ≠ 0 := by intro h; rw [Real.sinh_eq_zero] at h; tauto
    have hB : Real.sinh (env "a" + env "b" * t) ≠ 0 := by first | assumption | tauto
    rw [show Fn.coth (env "a" + env "b" * t) ^ kp = Fn.coth (env "a" + env "b" * t) ^ (kp - 2) * Fn.coth (env "a" + env "b" * t) ^ (2 : ℤ) by
      rw [← zpow_add' (Or.inr (Or.inl (by omega)))]; congr 1; ring]
    generalize Fn.coth (env "a" + env "b" * t) ^ (kp - 2) = Q
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ⊢
    simp only [Fn.coth, Real.tanh_eq_sinh_div_cosh] at ⊢
    try generalize Real.sinh (env "a" + env "b" * t) ^ kn = P
    generalize (env "c" + env "d" * t) ^ km = M
    generalize Real.sinh (env "a" + env "b" * t) = S at *
    generalize Real.cosh (env "a" + env "b" * t) = C at *
    field_simp
    linear_combination (-M*Q/P) * hrel

end OSR.IntegrationRec148
