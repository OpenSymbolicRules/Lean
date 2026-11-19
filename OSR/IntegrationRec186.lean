import OSR.IntegrationRec91

/-!
# Integration (RUBI): linear combinations of residual integrals

Rules whose result is a sum of terms `c ∫ H`, `c x` and `c`, with `c` free of `x`;
the derivative is assembled from the result and matched by `convert`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec186

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/










/-- RUBI 4.5.2.1 #11 -/
def rubi4521r11 : CRule where
  id := "integration.rubi_4_5_2_1_r11"; legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "x")) (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "I1")))
  integrals := [("I1", (.pow (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0)]
  priority := 16409
  description := "RUBI 4.5.2.1 #11"
  provenance := migrated "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:11" "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#11"












/-- RUBI 4.1.3.1 #36 -/
def rubi4131r36 : CRule where
  id := "integration.rubi_4_1_3_1_r36"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):36"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d"))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)]
  priority := 16421
  description := "RUBI 4.1.3.1 #36"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):36" "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#36"

/-- RUBI 4.1.5 #27 -/
def rubi415r27 : CRule where
  id := "integration.rubi_4_1_5_r27"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "x")) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 16422
  description := "RUBI 4.1.5 #27"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:27" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#27"

/-- RUBI 4.1.5 #28 -/
def rubi415r28 : CRule where
  id := "integration.rubi_4_1_5_r28"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:28"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "x")) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 16423
  description := "RUBI 4.1.5 #28"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:28" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#28"






/-- RUBI 4.3.3.1 #24 -/
def rubi4331r24 : CRule where
  id := "integration.rubi_4_3_3_1_r24"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "B") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d")))) (.app2 .mul (.var "A") (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d"))))) (.var "x")) (.pow (.app2 .mul (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B")))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d")))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)]
  priority := 16429
  description := "RUBI 4.3.3.1 #24"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):24" "4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan).m#24"


/-- RUBI 4.3.4.1 #7 -/
def rubi4341r7 : CRule where
  id := "integration.rubi_4_3_4_1_r7"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.var "b") (.var "B"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C"))) (.var "x")) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.int 1) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "A", "B", "C"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.int 0)]
  priority := 16431
  description := "RUBI 4.3.4.1 #7"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):7" "4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2).m#7"

/-- RUBI 4.3.4.1 #10 -/
def rubi4341r10 : CRule where
  id := "integration.rubi_4_3_4_1_r10"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.var "b") (.var "B"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C"))) (.var "x")) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C")))) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))),
    ("I2", (.app2 .mul (.app2 .add (.int 1) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "A", "B", "C"]
  conditions := [.ne (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.int 0)]
  priority := 16432
  description := "RUBI 4.3.4.1 #10"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):10" "4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2).m#10"

/-- RUBI 4.3.4.1 #11 -/
def rubi4341r11 : CRule where
  id := "integration.rubi_4_3_4_1_r11"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.app2 .add (.var "A") (.app2 .mul (.int (-1)) (.var "C")))) (.var "x")) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.var "A") (.app2 .mul (.int (-1)) (.var "C")))) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C")) (.app2 .mul (.var "A") (.pow (.var "b") (.int 2)))) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))),
    ("I2", (.app2 .mul (.app2 .add (.int 1) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "A", "C"]
  conditions := [.ne (.app2 .add (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C")) (.app2 .mul (.var "A") (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.var "A") (.var "C")]
  priority := 16433
  description := "RUBI 4.3.4.1 #11"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):11" "4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2).m#11"

/-- RUBI 4.3.2.1 #10 -/
def rubi4321r10 : CRule where
  id := "integration.rubi_4_3_2_1_r10"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.var "b") (.var "d"))) (.var "x")) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.var "b") (.var "d"))) (.int 0)]
  priority := 16434
  description := "RUBI 4.3.2.1 #10"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:10" "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#10"


/-- RUBI 4.3.2.1 #49 -/
def rubi4321r49 : CRule where
  id := "integration.rubi_4_3_2_1_r49"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:49"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d"))) (.var "x")) (.pow (.app2 .mul (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)]
  priority := 16436
  description := "RUBI 4.3.2.1 #49"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:49" "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#49"

/-- RUBI 4.3.4.2 #20 -/
def rubi4342r20 : CRule where
  id := "integration.rubi_4_3_4_2_r20"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2):20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "C"))) (.app2 .mul (.var "B") (.var "d")))) (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d"))) (.app2 .mul (.var "C") (.var "d"))))) (.var "x")) (.pow (.app2 .mul (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "C")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "c")) (.var "d"))) (.app2 .mul (.var "A") (.pow (.var "d") (.int 2))))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "C"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)]
  priority := 16437
  description := "RUBI 4.3.4.2 #20"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2):20" "4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2).m#20"

/-- RUBI 4.3.4.2 #21 -/
def rubi4342r21 : CRule where
  id := "integration.rubi_4_3_4_2_r21"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2):21"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.var "A") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "C")))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.var "A") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.var "d"))))) (.var "x")) (.pow (.app2 .mul (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "C")) (.app2 .mul (.var "A") (.pow (.var "d") (.int 2))))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "C"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)]
  priority := 16438
  description := "RUBI 4.3.4.2 #21"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2):21" "4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2).m#21"

/-- RUBI 6.7.9 #45 -/
def rubi679r45 : CRule where
  id := "integration.rubi_6_7_9_r45"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:45"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .exp (.app2 .mul (.int (-1)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app1 .exp (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.pow (.int 2) (.int (-1))))) (.app2 .mul (.app1 .exp (.app2 .mul (.int (-1)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app2 .add (.int 1) (.app1 .exp (.app2 .mul (.int 2) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))) (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .exp (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app2 .add (.int 1) (.app1 .exp (.app2 .mul (.int 2) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)]
  priority := 16439
  description := "RUBI 6.7.9 #45"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:45" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#45"



/-- RUBI 6.7.9 #48 -/
def rubi679r48 : CRule where
  id := "integration.rubi_6_7_9_r48"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:48"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app1 .exp (.app2 .mul (.int (-1)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app1 .exp (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.pow (.int 2) (.int (-1))))) (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .exp (.app2 .mul (.int (-1)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app2 .add (.int 1) (.app1 .exp (.app2 .mul (.int 2) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))) (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .exp (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app2 .add (.int 1) (.app1 .exp (.app2 .mul (.int 2) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)]
  priority := 16442
  description := "RUBI 6.7.9 #48"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:48" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#48"



theorem rubi4521r11_real : rubi4521r11.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4521r11.conditions rubi4521r11.body rubi4521r11.result rubi4521r11.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4521r11, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4521r11, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4521r11, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4521r11, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4521r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi4521r11, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (((hasDerivAt_id t).const_mul (env "a" * env "c")).add (hΦ1.const_mul (env "b" * env "d")))
    convert hD using 1
    · funext v
      simp [rubi4521r11, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4521r11, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4131r36_real : rubi4131r36.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4131r36.conditions rubi4131r36.body rubi4131r36.result rubi4131r36.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4131r36, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4131r36, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4131r36, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4131r36, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4131r36, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4131r36, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((hΦ1.const_mul (((env "A" * env "b") + ((-1 : ℝ) * env "a" * env "B")) * (((env "b" * env "c") + ((-1 : ℝ) * env "a" * env "d")))⁻¹)).add (hΦ2.const_mul (((env "B" * env "c") + ((-1 : ℝ) * env "A" * env "d")) * (((env "b" * env "c") + ((-1 : ℝ) * env "a" * env "d")))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4131r36, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4131r36, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4131r36_complex : rubi4131r36.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4131r36.conditions rubi4131r36.body rubi4131r36.result rubi4131r36.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4131r36, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4131r36, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4131r36, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4131r36, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4131r36, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4131r36, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((hΦ1.const_mul (((env "A" * env "b") + ((-1 : ℂ) * env "a" * env "B")) * (((env "b" * env "c") + ((-1 : ℂ) * env "a" * env "d")))⁻¹)).add (hΦ2.const_mul (((env "B" * env "c") + ((-1 : ℂ) * env "A" * env "d")) * (((env "b" * env "c") + ((-1 : ℂ) * env "a" * env "d")))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4131r36, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4131r36, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.sinh_eq, Complex.cosh_eq, Complex.tanh_eq_sinh_div_cosh, Complex.exp_neg, mul_add, two_mul,
          Complex.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi415r27_real : rubi415r27.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi415r27.conditions rubi415r27.body rubi415r27.result rubi415r27.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi415r27, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r27, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi415r27, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi415r27, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi415r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi415r27, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (((hasDerivAt_id t).const_mul (env "b" * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul ((-1 : ℝ) * env "a" * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi415r27, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi415r27, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi415r27_complex : rubi415r27.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi415r27.conditions rubi415r27.body rubi415r27.result rubi415r27.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi415r27, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r27, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi415r27, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi415r27, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi415r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi415r27, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (((hasDerivAt_id t).const_mul (env "b" * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul ((-1 : ℂ) * env "a" * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi415r27, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi415r27, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.sinh_eq, Complex.cosh_eq, Complex.tanh_eq_sinh_div_cosh, Complex.exp_neg, mul_add, two_mul,
          Complex.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi415r28_real : rubi415r28.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi415r28.conditions rubi415r28.body rubi415r28.result rubi415r28.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi415r28, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r28, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi415r28, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi415r28, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi415r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi415r28, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (((hasDerivAt_id t).const_mul (env "a" * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul (env "b" * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi415r28, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi415r28, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi415r28_complex : rubi415r28.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi415r28.conditions rubi415r28.body rubi415r28.result rubi415r28.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi415r28, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi415r28, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi415r28, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi415r28, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi415r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi415r28, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (((hasDerivAt_id t).const_mul (env "a" * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul (env "b" * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi415r28, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi415r28, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.sinh_eq, Complex.cosh_eq, Complex.tanh_eq_sinh_div_cosh, Complex.exp_neg, mul_add, two_mul,
          Complex.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4331r24_real : rubi4331r24.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4331r24.conditions rubi4331r24.body rubi4331r24.result rubi4331r24.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4331r24, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4331r24, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4331r24, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4331r24, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4331r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4331r24, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (((env "B" * ((env "b" * env "c") + (env "a" * env "d"))) + (env "A" * ((env "a" * env "c") + ((-1 : ℝ) * env "b" * env "d")))) * ((((env "a" ^ 2) + (env "b" ^ 2)) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)).add (hΦ1.const_mul (env "b" * ((env "A" * env "b") + ((-1 : ℝ) * env "a" * env "B")) * ((((env "b" * env "c") + ((-1 : ℝ) * env "a" * env "d")) * ((env "a" ^ 2) + (env "b" ^ 2))))⁻¹))).add (hΦ2.const_mul (env "d" * ((env "B" * env "c") + ((-1 : ℝ) * env "A" * env "d")) * ((((env "b" * env "c") + ((-1 : ℝ) * env "a" * env "d")) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4331r24, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4331r24, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4331r24_complex : rubi4331r24.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4331r24.conditions rubi4331r24.body rubi4331r24.result rubi4331r24.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4331r24, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4331r24, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4331r24, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4331r24, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4331r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4331r24, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (((env "B" * ((env "b" * env "c") + (env "a" * env "d"))) + (env "A" * ((env "a" * env "c") + ((-1 : ℂ) * env "b" * env "d")))) * ((((env "a" ^ 2) + (env "b" ^ 2)) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)).add (hΦ1.const_mul (env "b" * ((env "A" * env "b") + ((-1 : ℂ) * env "a" * env "B")) * ((((env "b" * env "c") + ((-1 : ℂ) * env "a" * env "d")) * ((env "a" ^ 2) + (env "b" ^ 2))))⁻¹))).add (hΦ2.const_mul (env "d" * ((env "B" * env "c") + ((-1 : ℂ) * env "A" * env "d")) * ((((env "b" * env "c") + ((-1 : ℂ) * env "a" * env "d")) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4331r24, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4331r24, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.sinh_eq, Complex.cosh_eq, Complex.tanh_eq_sinh_div_cosh, Complex.exp_neg, mul_add, two_mul,
          Complex.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4341r7_real : rubi4341r7.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4341r7.conditions rubi4341r7.body rubi4341r7.result rubi4341r7.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4341r7, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r7, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4341r7, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4341r7, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4341r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi4341r7, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (((hasDerivAt_id t).const_mul (((env "a" * env "A") + (env "b" * env "B") + ((-1 : ℝ) * env "a" * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul (((env "A" * (env "b" ^ 2)) + ((-1 : ℝ) * env "a" * env "b" * env "B") + ((env "a" ^ 2) * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4341r7, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4341r7, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4341r7_complex : rubi4341r7.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4341r7.conditions rubi4341r7.body rubi4341r7.result rubi4341r7.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4341r7, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r7, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4341r7, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4341r7, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4341r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi4341r7, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (((hasDerivAt_id t).const_mul (((env "a" * env "A") + (env "b" * env "B") + ((-1 : ℂ) * env "a" * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul (((env "A" * (env "b" ^ 2)) + ((-1 : ℂ) * env "a" * env "b" * env "B") + ((env "a" ^ 2) * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4341r7, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4341r7, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.sinh_eq, Complex.cosh_eq, Complex.tanh_eq_sinh_div_cosh, Complex.exp_neg, mul_add, two_mul,
          Complex.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4341r10_real : rubi4341r10.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4341r10.conditions rubi4341r10.body rubi4341r10.result rubi4341r10.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4341r10, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r10, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4341r10, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4341r10, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4341r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4341r10, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (((env "a" * env "A") + (env "b" * env "B") + ((-1 : ℝ) * env "a" * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul ((-1 : ℝ) * ((env "A" * env "b") + ((-1 : ℝ) * env "a" * env "B") + ((-1 : ℝ) * env "b" * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹))).add (hΦ2.const_mul (((env "A" * (env "b" ^ 2)) + ((-1 : ℝ) * env "a" * env "b" * env "B") + ((env "a" ^ 2) * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4341r10, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4341r10, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4341r10_complex : rubi4341r10.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4341r10.conditions rubi4341r10.body rubi4341r10.result rubi4341r10.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4341r10, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r10, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4341r10, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4341r10, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4341r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4341r10, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (((env "a" * env "A") + (env "b" * env "B") + ((-1 : ℂ) * env "a" * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul ((-1 : ℂ) * ((env "A" * env "b") + ((-1 : ℂ) * env "a" * env "B") + ((-1 : ℂ) * env "b" * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹))).add (hΦ2.const_mul (((env "A" * (env "b" ^ 2)) + ((-1 : ℂ) * env "a" * env "b" * env "B") + ((env "a" ^ 2) * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4341r10, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4341r10, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.sinh_eq, Complex.cosh_eq, Complex.tanh_eq_sinh_div_cosh, Complex.exp_neg, mul_add, two_mul,
          Complex.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4341r11_real : rubi4341r11.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4341r11.conditions rubi4341r11.body rubi4341r11.result rubi4341r11.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4341r11, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r11, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4341r11, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4341r11, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4341r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4341r11, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (env "a" * (env "A" + ((-1 : ℝ) * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul ((-1 : ℝ) * env "b" * (env "A" + ((-1 : ℝ) * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹))).add (hΦ2.const_mul ((((env "a" ^ 2) * env "C") + (env "A" * (env "b" ^ 2))) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4341r11, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4341r11, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4341r11_complex : rubi4341r11.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4341r11.conditions rubi4341r11.body rubi4341r11.result rubi4341r11.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4341r11, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r11, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4341r11, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4341r11, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4341r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4341r11, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (env "a" * (env "A" + ((-1 : ℂ) * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul ((-1 : ℂ) * env "b" * (env "A" + ((-1 : ℂ) * env "C")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹))).add (hΦ2.const_mul ((((env "a" ^ 2) * env "C") + (env "A" * (env "b" ^ 2))) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4341r11, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4341r11, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.sinh_eq, Complex.cosh_eq, Complex.tanh_eq_sinh_div_cosh, Complex.exp_neg, mul_add, two_mul,
          Complex.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4321r10_real : rubi4321r10.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4321r10.conditions rubi4321r10.body rubi4321r10.result rubi4321r10.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4321r10, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r10, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4321r10, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4321r10, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4321r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi4321r10, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (((hasDerivAt_id t).const_mul (((env "a" * env "c") + (env "b" * env "d")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul (((env "b" * env "c") + ((-1 : ℝ) * env "a" * env "d")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4321r10, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4321r10, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4321r10_complex : rubi4321r10.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4321r10.conditions rubi4321r10.body rubi4321r10.result rubi4321r10.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4321r10, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r10, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4321r10, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4321r10, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4321r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi4321r10, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (((hasDerivAt_id t).const_mul (((env "a" * env "c") + (env "b" * env "d")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul (((env "b" * env "c") + ((-1 : ℂ) * env "a" * env "d")) * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4321r10, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4321r10, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.sinh_eq, Complex.cosh_eq, Complex.tanh_eq_sinh_div_cosh, Complex.exp_neg, mul_add, two_mul,
          Complex.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4321r49_real : rubi4321r49.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4321r49.conditions rubi4321r49.body rubi4321r49.result rubi4321r49.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4321r49, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r49, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4321r49, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4321r49, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4321r49, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4321r49, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (((env "a" * env "c") + ((-1 : ℝ) * env "b" * env "d")) * ((((env "a" ^ 2) + (env "b" ^ 2)) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)).add (hΦ1.const_mul ((env "b" ^ 2) * ((((env "b" * env "c") + ((-1 : ℝ) * env "a" * env "d")) * ((env "a" ^ 2) + (env "b" ^ 2))))⁻¹))).add (hΦ2.const_mul ((-1 : ℝ) * (env "d" ^ 2) * ((((env "b" * env "c") + ((-1 : ℝ) * env "a" * env "d")) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4321r49, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4321r49, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4321r49_complex : rubi4321r49.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4321r49.conditions rubi4321r49.body rubi4321r49.result rubi4321r49.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4321r49, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r49, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4321r49, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4321r49, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4321r49, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4321r49, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (((env "a" * env "c") + ((-1 : ℂ) * env "b" * env "d")) * ((((env "a" ^ 2) + (env "b" ^ 2)) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)).add (hΦ1.const_mul ((env "b" ^ 2) * ((((env "b" * env "c") + ((-1 : ℂ) * env "a" * env "d")) * ((env "a" ^ 2) + (env "b" ^ 2))))⁻¹))).add (hΦ2.const_mul ((-1 : ℂ) * (env "d" ^ 2) * ((((env "b" * env "c") + ((-1 : ℂ) * env "a" * env "d")) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4321r49, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4321r49, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.sinh_eq, Complex.cosh_eq, Complex.tanh_eq_sinh_div_cosh, Complex.exp_neg, mul_add, two_mul,
          Complex.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4342r20_real : rubi4342r20.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4342r20.conditions rubi4342r20.body rubi4342r20.result rubi4342r20.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4342r20, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r20, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4342r20, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4342r20, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4342r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4342r20, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (((env "a" * ((env "A" * env "c") + ((-1 : ℝ) * env "c" * env "C") + (env "B" * env "d"))) + (env "b" * ((env "B" * env "c") + ((-1 : ℝ) * env "A" * env "d") + (env "C" * env "d")))) * ((((env "a" ^ 2) + (env "b" ^ 2)) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)).add (hΦ1.const_mul (((env "A" * (env "b" ^ 2)) + ((-1 : ℝ) * env "a" * env "b" * env "B") + ((env "a" ^ 2) * env "C")) * ((((env "b" * env "c") + ((-1 : ℝ) * env "a" * env "d")) * ((env "a" ^ 2) + (env "b" ^ 2))))⁻¹))).add (hΦ2.const_mul ((-1 : ℝ) * (((env "c" ^ 2) * env "C") + ((-1 : ℝ) * env "B" * env "c" * env "d") + (env "A" * (env "d" ^ 2))) * ((((env "b" * env "c") + ((-1 : ℝ) * env "a" * env "d")) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4342r20, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4342r20, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4342r20_complex : rubi4342r20.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4342r20.conditions rubi4342r20.body rubi4342r20.result rubi4342r20.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4342r20, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r20, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4342r20, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4342r20, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4342r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4342r20, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (((env "a" * ((env "A" * env "c") + ((-1 : ℂ) * env "c" * env "C") + (env "B" * env "d"))) + (env "b" * ((env "B" * env "c") + ((-1 : ℂ) * env "A" * env "d") + (env "C" * env "d")))) * ((((env "a" ^ 2) + (env "b" ^ 2)) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)).add (hΦ1.const_mul (((env "A" * (env "b" ^ 2)) + ((-1 : ℂ) * env "a" * env "b" * env "B") + ((env "a" ^ 2) * env "C")) * ((((env "b" * env "c") + ((-1 : ℂ) * env "a" * env "d")) * ((env "a" ^ 2) + (env "b" ^ 2))))⁻¹))).add (hΦ2.const_mul ((-1 : ℂ) * (((env "c" ^ 2) * env "C") + ((-1 : ℂ) * env "B" * env "c" * env "d") + (env "A" * (env "d" ^ 2))) * ((((env "b" * env "c") + ((-1 : ℂ) * env "a" * env "d")) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4342r20, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4342r20, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.sinh_eq, Complex.cosh_eq, Complex.tanh_eq_sinh_div_cosh, Complex.exp_neg, mul_add, two_mul,
          Complex.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4342r21_real : rubi4342r21.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4342r21.conditions rubi4342r21.body rubi4342r21.result rubi4342r21.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4342r21, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r21, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4342r21, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4342r21, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4342r21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4342r21, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (((env "a" * ((env "A" * env "c") + ((-1 : ℝ) * env "c" * env "C"))) + ((-1 : ℝ) * env "b" * ((env "A" * env "d") + ((-1 : ℝ) * env "C" * env "d")))) * ((((env "a" ^ 2) + (env "b" ^ 2)) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)).add (hΦ1.const_mul (((env "A" * (env "b" ^ 2)) + ((env "a" ^ 2) * env "C")) * ((((env "b" * env "c") + ((-1 : ℝ) * env "a" * env "d")) * ((env "a" ^ 2) + (env "b" ^ 2))))⁻¹))).add (hΦ2.const_mul ((-1 : ℝ) * (((env "c" ^ 2) * env "C") + (env "A" * (env "d" ^ 2))) * ((((env "b" * env "c") + ((-1 : ℝ) * env "a" * env "d")) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4342r21, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4342r21, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4342r21_complex : rubi4342r21.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4342r21.conditions rubi4342r21.body rubi4342r21.result rubi4342r21.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4342r21, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4342r21, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4342r21, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4342r21, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi4342r21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4342r21, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (((env "a" * ((env "A" * env "c") + ((-1 : ℂ) * env "c" * env "C"))) + ((-1 : ℂ) * env "b" * ((env "A" * env "d") + ((-1 : ℂ) * env "C" * env "d")))) * ((((env "a" ^ 2) + (env "b" ^ 2)) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)).add (hΦ1.const_mul (((env "A" * (env "b" ^ 2)) + ((env "a" ^ 2) * env "C")) * ((((env "b" * env "c") + ((-1 : ℂ) * env "a" * env "d")) * ((env "a" ^ 2) + (env "b" ^ 2))))⁻¹))).add (hΦ2.const_mul ((-1 : ℂ) * (((env "c" ^ 2) * env "C") + (env "A" * (env "d" ^ 2))) * ((((env "b" * env "c") + ((-1 : ℂ) * env "a" * env "d")) * ((env "c" ^ 2) + (env "d" ^ 2))))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4342r21, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4342r21, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.sinh_eq, Complex.cosh_eq, Complex.tanh_eq_sinh_div_cosh, Complex.exp_neg, mul_add, two_mul,
          Complex.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi679r45_real : rubi679r45.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r45.conditions rubi679r45.body rubi679r45.result rubi679r45.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi679r45, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r45, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r45, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi679r45, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi679r45, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi679r45, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (hΦ1.const_mul (1))
    convert hD using 1
    · funext v
      simp [rubi679r45, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi679r45, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi679r48_real : rubi679r48.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r48.conditions rubi679r48.body rubi679r48.result rubi679r48.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi679r48, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r48, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r48, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi679r48, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (apply ne_of_gt; positivity) | (trace_state; sorry)
  · simp only [rubi679r48, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi679r48, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (hΦ1.const_mul (1))
    convert hD using 1
    · funext v
      simp [rubi679r48, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi679r48, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.sinh_eq, Real.cosh_eq, Real.tanh_eq_sinh_div_cosh, Real.exp_neg, mul_add, two_mul,
          Real.exp_add, neg_add]; field_simp; ring1)
      | ((try casesm* _ ∧ _); field_simp; grind)
      | ((try casesm* _ ∧ _); grind)
      | ((try casesm* _ ∧ _); field_simp; simp only [Real.sq_sqrt, Real.sqrt_mul_self, pow_two, *] <;> ring1)
      | ((try casesm* _ ∧ _); rw [div_eq_iff (by positivity)] <;> field_simp <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption)] <;> ring1)
      | ((try casesm* _ ∧ _); field_simp; rw [Real.sq_sqrt (by assumption), Real.sq_sqrt (by assumption)] <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

end OSR.IntegrationRec186
