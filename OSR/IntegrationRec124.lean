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

namespace OSR.IntegrationRec124

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 6.7.9 #12 -/
def rubi679r12 : CRule where
  id := "integration.rubi_6_7_9_r12"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9901
  description := "RUBI 6.7.9 #12"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:12" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#12"

/-- RUBI 6.7.9 #13 -/
def rubi679r13 : CRule where
  id := "integration.rubi_6_7_9_r13"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9902
  description := "RUBI 6.7.9 #13"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:13" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#13"

/-- RUBI 6.7.9 #14 -/
def rubi679r14 : CRule where
  id := "integration.rubi_6_7_9_r14"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9903
  description := "RUBI 6.7.9 #14"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:14" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#14"

/-- RUBI 6.7.9 #19 -/
def rubi679r19 : CRule where
  id := "integration.rubi_6_7_9_r19"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9904
  description := "RUBI 6.7.9 #19"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:19" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#19"

/-- RUBI 6.7.9 #2 -/
def rubi679r2 : CRule where
  id := "integration.rubi_6_7_9_r2"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9905
  description := "RUBI 6.7.9 #2"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:2" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#2"

/-- RUBI 6.7.9 #20 -/
def rubi679r20 : CRule where
  id := "integration.rubi_6_7_9_r20"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9906
  description := "RUBI 6.7.9 #20"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:20" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#20"

/-- RUBI 6.7.9 #23 -/
def rubi679r23 : CRule where
  id := "integration.rubi_6_7_9_r23"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9907
  description := "RUBI 6.7.9 #23"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:23" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#23"

/-- RUBI 6.7.9 #24 -/
def rubi679r24 : CRule where
  id := "integration.rubi_6_7_9_r24"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9908
  description := "RUBI 6.7.9 #24"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:24" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#24"

/-- RUBI 6.7.9 #25 -/
def rubi679r25 : CRule where
  id := "integration.rubi_6_7_9_r25"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9909
  description := "RUBI 6.7.9 #25"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:25" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#25"

/-- RUBI 6.7.9 #26 -/
def rubi679r26 : CRule where
  id := "integration.rubi_6_7_9_r26"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:26"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9910
  description := "RUBI 6.7.9 #26"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:26" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#26"

/-- RUBI 6.7.9 #27 -/
def rubi679r27 : CRule where
  id := "integration.rubi_6_7_9_r27"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9911
  description := "RUBI 6.7.9 #27"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:27" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#27"

/-- RUBI 6.7.9 #28 -/
def rubi679r28 : CRule where
  id := "integration.rubi_6_7_9_r28"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:28"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9912
  description := "RUBI 6.7.9 #28"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:28" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#28"

/-- RUBI 6.7.9 #29 -/
def rubi679r29 : CRule where
  id := "integration.rubi_6_7_9_r29"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9913
  description := "RUBI 6.7.9 #29"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:29" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#29"

/-- RUBI 6.7.9 #30 -/
def rubi679r30 : CRule where
  id := "integration.rubi_6_7_9_r30"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9914
  description := "RUBI 6.7.9 #30"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:30" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#30"

/-- RUBI 6.7.9 #31 -/
def rubi679r31 : CRule where
  id := "integration.rubi_6_7_9_r31"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9915
  description := "RUBI 6.7.9 #31"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:31" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#31"

/-- RUBI 6.7.9 #32 -/
def rubi679r32 : CRule where
  id := "integration.rubi_6_7_9_r32"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:32"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9916
  description := "RUBI 6.7.9 #32"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:32" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#32"

/-- RUBI 6.7.9 #33 -/
def rubi679r33 : CRule where
  id := "integration.rubi_6_7_9_r33"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9917
  description := "RUBI 6.7.9 #33"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:33" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#33"

/-- RUBI 6.7.9 #34 -/
def rubi679r34 : CRule where
  id := "integration.rubi_6_7_9_r34"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:34"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 9918
  description := "RUBI 6.7.9 #34"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:34" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#34"

/-- RUBI 6.7.9 #78 -/
def rubi679r78 : CRule where
  id := "integration.rubi_6_7_9_r78"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:78"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))) (.pow (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "B") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "f")) (.pow (.app2 .mul (.var "a") (.var "d")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.var "b") (.var "B"))) (.int 0)]
  priority := 9919
  description := "RUBI 6.7.9 #78"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:78" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#78"

/-- RUBI 6.7.9 #79 -/
def rubi679r79 : CRule where
  id := "integration.rubi_6_7_9_r79"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:79"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))) (.pow (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "B") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "f")) (.pow (.app2 .mul (.var "a") (.var "d")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.int 0)]
  priority := 9920
  description := "RUBI 6.7.9 #79"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:79" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#79"

/-- RUBI 6.7.9 #9 -/
def rubi679r9 : CRule where
  id := "integration.rubi_6_7_9_r9"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I2"))) (.app2 .mul (.app2 .mul (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I3")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))),
    ("I3", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 1),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 9921
  description := "RUBI 6.7.9 #9"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:9" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#9"

/-- RUBI 7.1.1 #2 -/
def rubi711r2 : CRule where
  id := "integration.rubi_7_1_1_r2"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.1 (a+b arcsinh(c x))^n:2"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "n"]
  conditions := [.gt (.int (-1)) (.var "n")]
  priority := 9922
  description := "RUBI 7.1.1 #2"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.1 (a+b arcsinh(c x))^n:2" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.1 (a+b arcsinh(c x))^n.m#2"

/-- RUBI 7.1.2 #2 -/
def rubi712r2 : CRule where
  id := "integration.rubi_7_1_2_r2"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b arcsinh(c x))^n:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 9923
  description := "RUBI 7.1.2 #2"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b arcsinh(c x))^n:2" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b arcsinh(c x))^n.m#2"

/-- RUBI 7.1.2 #5 -/
def rubi712r5 : CRule where
  id := "integration.rubi_7_1_2_r5"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b arcsinh(c x))^n:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .gt (.int (-2)) (.var "n")]
  priority := 9924
  description := "RUBI 7.1.2 #5"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b arcsinh(c x))^n:5" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b arcsinh(c x))^n.m#5"

/-- RUBI 7.1.4 #23 -/
def rubi714r23 : CRule where
  id := "integration.rubi_7_1_4_r23"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.ne (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .ne (.var "p") (.int (-1))]
  priority := 9925
  description := "RUBI 7.1.4 #23"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:23" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n.m#23"

/-- RUBI 7.1.5 #11 -/
def rubi715r11 : CRule where
  id := "integration.rubi_7_1_5_r11"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.5 u (a+b arcsinh(c x))^n:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .int (.var "m"),
    .gt (.var "m") (.int 0),
    .gt (.var "d") (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 9926
  description := "RUBI 7.1.5 #11"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.5 u (a+b arcsinh(c x))^n:11" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.5 u (a+b arcsinh(c x))^n.m#11"

/-- RUBI 7.1.5 #15 -/
def rubi715r15 : CRule where
  id := "integration.rubi_7_1_5_r15"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.5 u (a+b arcsinh(c x))^n:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "n"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "d") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9927
  description := "RUBI 7.1.5 #15"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.5 u (a+b arcsinh(c x))^n:15" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.5 u (a+b arcsinh(c x))^n.m#15"

/-- RUBI 7.1.5 #2 -/
def rubi715r2 : CRule where
  id := "integration.rubi_7_1_5_r2"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.5 u (a+b arcsinh(c x))^n:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 9928
  description := "RUBI 7.1.5 #2"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.5 u (a+b arcsinh(c x))^n:2" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.5 u (a+b arcsinh(c x))^n.m#2"

/-- RUBI 7.1.5 #8 -/
def rubi715r8 : CRule where
  id := "integration.rubi_7_1_5_r8"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.5 u (a+b arcsinh(c x))^n:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "g")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "f")) (.var "x"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "g")) (.app2 .add (.var "m") (.int 2))) (.pow (.var "x") (.int 2)))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .int (.var "m"),
    .gt (.int 0) (.var "m"),
    .gt (.var "d") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9929
  description := "RUBI 7.1.5 #8"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.5 u (a+b arcsinh(c x))^n:8" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.5 u (a+b arcsinh(c x))^n.m#8"

/-- RUBI 7.2.6 #16 -/
def rubi726r16 : CRule where
  id := "integration.rubi_7_2_6_r16"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.6 Miscellaneous inverse hyperbolic cosine:16"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.var "n"))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.pow (.var "b") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.var "x") (.int 2))) (.app2 .mul (.var "d") (.pow (.var "x") (.int 4)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.app2 .add (.var "n") (.int 1))) (.var "x")) (.app2 .root (.app2 .add (.app2 .add (.int (-1)) (.var "c")) (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .root (.app2 .add (.app2 .add (.int 1) (.var "c")) (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.pow (.var "b") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.int 2))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.eq (.pow (.var "c") (.int 2)) (.int 1),
    .gt (.int (-1)) (.var "n"),
    .ne (.var "n") (.int (-2))]
  priority := 9930
  description := "RUBI 7.2.6 #16"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.6 Miscellaneous inverse hyperbolic cosine:16" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.6 Miscellaneous inverse hyperbolic cosine.m#16"

/-- RUBI 7.2.6 #7 -/
def rubi726r7 : CRule where
  id := "integration.rubi_7_2_6_r7"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.6 Miscellaneous inverse hyperbolic cosine:7"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.var "n"))
  result := (.app2 .add (.app2 .add (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.var "n"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "b")) (.var "n")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.pow (.var "x") (.int 2))) (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "x") (.int 4))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app2 .root (.app2 .add (.app2 .add (.int (-1)) (.var "c")) (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .root (.app2 .add (.app2 .add (.int 1) (.var "c")) (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.pow (.var "b") (.int 2))) (.var "n")) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.eq (.pow (.var "c") (.int 2)) (.int 1),
    .gt (.var "n") (.int 1)]
  priority := 9931
  description := "RUBI 7.2.6 #7"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.6 Miscellaneous inverse hyperbolic cosine:7" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.6 Miscellaneous inverse hyperbolic cosine.m#7"

/-- RUBI 7.3.1 #101 -/
def rubi731r101 : CRule where
  id := "integration.rubi_7_3_1_r101"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:101"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "p")) (.pow (.app2 .mul (.var "c") (.var "m")) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.pow (.var "c") (.int 2)) (.var "m")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "p") (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 9932
  description := "RUBI 7.3.1 #101"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:101" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#101"

/-- RUBI 7.3.1 #11 -/
def rubi731r11 : CRule where
  id := "integration.rubi_7_3_1_r11"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.app1 .ln (.app2 .mul (.int 2) (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.int (-1)))))) (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.pow (.var "e") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app1 .ln (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.var "e")) (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x")))) (.int (-1)))))) (.pow (.var "e") (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.pow (.var "e") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .mul (.int 2) (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.int (-1))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .ln (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.var "e")) (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x")))) (.int (-1))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2)))) (.int 0)]
  priority := 9933
  description := "RUBI 7.3.1 #11"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:11" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#11"

/-- RUBI 7.3.1 #113 -/
def rubi731r113 : CRule where
  id := "integration.rubi_7_3_1_r113"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:113"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "e") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "e") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "p", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .int (.var "p"),
    .int (.app2 .mul (.int 2) (.var "q")),
    .gt (.int (-1)) (.var "q"),
    .int (.var "m"),
    .gt (.var "m") (.int 1),
    .ne (.var "p") (.int (-1))]
  priority := 9934
  description := "RUBI 7.3.1 #113"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:113" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#113"

/-- RUBI 7.3.1 #117 -/
def rubi731r117 : CRule where
  id := "integration.rubi_7_3_1_r117"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:117"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 2))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "p", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .int (.var "m"),
    .gt (.int (-1)) (.var "q"),
    .gt (.int (-1)) (.var "p"),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 2)) (.int 0)]
  priority := 9935
  description := "RUBI 7.3.1 #117"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:117" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#117"

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


theorem rubi679r12_counterexample_real : ¬ rubi679r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r12.conditions rubi679r12.body rubi679r12.result rubi679r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi679r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r13_counterexample_real : ¬ rubi679r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r13.conditions rubi679r13.body rubi679r13.result rubi679r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi679r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r14_counterexample_real : ¬ rubi679r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r14.conditions rubi679r14.body rubi679r14.result rubi679r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi679r14, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r14_counterexample_complex : ¬ rubi679r14.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi679r14.conditions rubi679r14.body rubi679r14.result rubi679r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi679r14, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r14.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi679r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r19_counterexample_real : ¬ rubi679r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r19.conditions rubi679r19.body rubi679r19.result rubi679r19.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi679r19, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r2_counterexample_real : ¬ rubi679r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r2.conditions rubi679r2.body rubi679r2.result rubi679r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi679r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r2_counterexample_complex : ¬ rubi679r2.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi679r2.conditions rubi679r2.body rubi679r2.result rubi679r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi679r2, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r2.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi679r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r20_counterexample_real : ¬ rubi679r20.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r20.conditions rubi679r20.body rubi679r20.result rubi679r20.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi679r20, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r20.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r23_counterexample_real : ¬ rubi679r23.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r23.conditions rubi679r23.body rubi679r23.result rubi679r23.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi679r23, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r23, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r23.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r23, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r23_counterexample_complex : ¬ rubi679r23.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi679r23.conditions rubi679r23.body rubi679r23.result rubi679r23.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi679r23, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r23, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r23.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi679r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r23, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r24_counterexample_real : ¬ rubi679r24.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r24.conditions rubi679r24.body rubi679r24.result rubi679r24.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi679r24, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r24, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r24.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r24, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r24_counterexample_complex : ¬ rubi679r24.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi679r24.conditions rubi679r24.body rubi679r24.result rubi679r24.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi679r24, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r24, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r24.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi679r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r24, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r25_counterexample_real : ¬ rubi679r25.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r25.conditions rubi679r25.body rubi679r25.result rubi679r25.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi679r25, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r25, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r25.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r25, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r25_counterexample_complex : ¬ rubi679r25.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi679r25.conditions rubi679r25.body rubi679r25.result rubi679r25.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi679r25, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r25, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r25.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi679r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r25, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r26_counterexample_real : ¬ rubi679r26.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r26.conditions rubi679r26.body rubi679r26.result rubi679r26.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi679r26, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r26, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r26.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r26, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r27_counterexample_real : ¬ rubi679r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r27.conditions rubi679r27.body rubi679r27.result rubi679r27.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi679r27, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r28_counterexample_real : ¬ rubi679r28.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r28.conditions rubi679r28.body rubi679r28.result rubi679r28.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi679r28, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r28, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r28.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r28, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r29_counterexample_real : ¬ rubi679r29.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r29.conditions rubi679r29.body rubi679r29.result rubi679r29.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi679r29, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r29, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r29.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r29, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r30_counterexample_real : ¬ rubi679r30.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r30.conditions rubi679r30.body rubi679r30.result rubi679r30.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi679r30, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r30, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r30.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r30, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r30_counterexample_complex : ¬ rubi679r30.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi679r30.conditions rubi679r30.body rubi679r30.result rubi679r30.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi679r30, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r30, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r30.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi679r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r30, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r31_counterexample_real : ¬ rubi679r31.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r31.conditions rubi679r31.body rubi679r31.result rubi679r31.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi679r31, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r31.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r31, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r32_counterexample_real : ¬ rubi679r32.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r32.conditions rubi679r32.body rubi679r32.result rubi679r32.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi679r32, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r32, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r32.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r32, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r32, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r33_counterexample_real : ¬ rubi679r33.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r33.conditions rubi679r33.body rubi679r33.result rubi679r33.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi679r33, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r33.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r34_counterexample_real : ¬ rubi679r34.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r34.conditions rubi679r34.body rubi679r34.result rubi679r34.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi679r34, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r34, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r34.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r34, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r34, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r78_counterexample_real : ¬ rubi679r78.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r78.conditions rubi679r78.body rubi679r78.result rubi679r78.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) (1 : ℝ) (by simp [rubi679r78, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r78, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r78.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r78, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r78, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r79_counterexample_real : ¬ rubi679r79.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r79.conditions rubi679r79.body rubi679r79.result rubi679r79.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) (1 : ℝ) (by simp [rubi679r79, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r79, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r79.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r79, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r79, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r9_counterexample_real : ¬ rubi679r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r9.conditions rubi679r9.body rubi679r9.result rubi679r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" then 1 else if s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi679r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" then 1 else if s = "n" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r9_counterexample_complex : ¬ rubi679r9.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi679r9.conditions rubi679r9.body rubi679r9.result rubi679r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" then 1 else if s = "n" then 2 else 0) (1 : ℂ) (by simp [rubi679r9, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r9.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" then 1 else if s = "n" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi679r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi711r2_counterexample_real : ¬ rubi711r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi711r2.conditions rubi711r2.body rubi711r2.result rubi711r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then -3 else if s = "a" then 1 else 0) (1 : ℝ) (by simp [rubi711r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi711r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi711r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then -3 else if s = "a" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi711r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi711r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi712r2_counterexample_real : ¬ rubi712r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi712r2.conditions rubi712r2.body rubi712r2.result rubi712r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi712r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi712r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi712r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi712r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi712r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi712r5_counterexample_real : ¬ rubi712r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi712r5.conditions rubi712r5.body rubi712r5.result rubi712r5.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then -3 else if s = "a" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi712r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi712r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi712r5.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then -3 else if s = "a" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi712r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi712r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi714r23_counterexample_real : ¬ rubi714r23.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi714r23.conditions rubi714r23.body rubi714r23.result rubi714r23.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi714r23, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi714r23, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi714r23.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi714r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi714r23, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi715r11_counterexample_real : ¬ rubi715r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi715r11.conditions rubi715r11.body rubi715r11.result rubi715r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then -3 else if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi715r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi715r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi715r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then -3 else if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi715r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi715r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi715r15_counterexample_real : ¬ rubi715r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi715r15.conditions rubi715r15.body rubi715r15.result rubi715r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "h" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi715r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi715r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi715r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "h" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi715r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi715r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi715r2_counterexample_real : ¬ rubi715r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi715r2.conditions rubi715r2.body rubi715r2.result rubi715r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi715r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi715r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi715r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi715r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi715r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi715r8_counterexample_real : ¬ rubi715r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi715r8.conditions rubi715r8.body rubi715r8.result rubi715r8.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi715r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi715r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi715r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi715r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi715r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi726r16_counterexample_real : ¬ rubi726r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi726r16.conditions rubi726r16.body rubi726r16.result rubi726r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then -3 else if s = "a" ∨ s = "c" then 1 else 0) (1 : ℝ) (by simp [rubi726r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi726r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi726r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then -3 else if s = "a" ∨ s = "c" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi726r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi726r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi726r7_counterexample_real : ¬ rubi726r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi726r7.conditions rubi726r7.body rubi726r7.result rubi726r7.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" then 1 else if s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi726r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi726r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi726r7.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then 1 else if s = "n" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi726r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi726r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi731r101_counterexample_real : ¬ rubi731r101.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi731r101.conditions rubi731r101.body rubi731r101.result rubi731r101.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi731r101, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi731r101, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi731r101.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi731r101, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi731r101, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi731r11_counterexample_real : ¬ rubi731r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi731r11.conditions rubi731r11.body rubi731r11.result rubi731r11.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi731r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi731r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi731r11.integrals[1]!, by simp [rubi731r11], ?_⟩
  intro h
  simp [rubi731r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi731r113_counterexample_real : ¬ rubi731r113.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi731r113.conditions rubi731r113.body rubi731r113.result rubi731r113.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi731r113, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi731r113, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi731r113.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi731r113, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi731r113, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi731r117_counterexample_real : ¬ rubi731r117.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi731r117.conditions rubi731r117.body rubi731r117.result rubi731r117.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "p" ∨ s = "q" then -2 else if s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi731r117, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi731r117, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi731r117.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "p" ∨ s = "q" then -2 else if s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi731r117, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi731r117, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec124
