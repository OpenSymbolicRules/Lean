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

namespace OSR.IntegrationRec173

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/



/-- RUBI 4.5.9 #11 -/
def rubi459r11 : CRule where
  id := "integration.rubi_4_5_9_r11"; legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.9 trig^m (a+b sec^n+c sec^(2 n))^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.int 2) (.var "n")))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "n"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n")]
  priority := 12602
  description := "RUBI 4.5.9 #11"
  provenance := migrated "rubi:4 Trig functions/4.5 Secant/4.5.9 trig^m (a+b sec^n+c sec^(2 n))^p:11" "4 Trig functions/4.5 Secant/4.5.9 trig^m (a+b sec^n+c sec^(2 n))^p.m#11"





























/-- RUBI 4.1.9 #5 -/
def rubi419r5 : CRule where
  id := "integration.rubi_4_1_9_r5"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))) (.app2 .mul (.var "c") (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n2")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "m")) (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))) (.app2 .mul (.int 2) (.var "p")))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "p")]
  priority := 12631
  description := "RUBI 4.1.9 #5"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p:5" "4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p.m#5"





/-- RUBI 4.1.1.2 #18 -/
def rubi4112r18 : CRule where
  id := "integration.rubi_4_1_1_2_r18"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.app2 .root (.app2 .add (.int 1) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.app2 .root (.app2 .add (.int 1) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.pow (.app2 .add (.app2 .add (.var "b") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "a") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.pow (.app2 .root (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.pow (.app2 .mul (.app2 .root (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.app2 .root (.app2 .add (.int 1) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "g"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 12636
  description := "RUBI 4.1.1.2 #18"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m:18" "4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m.m#18"



/-- RUBI 4.1.4.2 #4 -/
def rubi4142r4 : CRule where
  id := "integration.rubi_4_1_4_2_r4"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C")))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "C")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .mul (.app2 .mul (.var "A") (.var "b")) (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .add (.var "m") (.int 2))) (.app2 .mul (.var "C") (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.var "m") (.int 1))))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "C")) (.var "d")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "C", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 12639
  description := "RUBI 4.1.4.2 #4"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):4" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#4"

/-- RUBI 4.1.4.2 #29 -/
def rubi4142r29 : CRule where
  id := "integration.rubi_4_1_4_2_r29"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "C") (.var "x")) (.pow (.app2 .mul (.var "b") (.var "d")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.pow (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "C")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "c")) (.var "d"))) (.app2 .mul (.var "A") (.pow (.var "d") (.int 2))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "C"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)]
  priority := 12640
  description := "RUBI 4.1.4.2 #29"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):29" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#29"


/-- RUBI 4.1.2.1 #4 -/
def rubi4121r4 : CRule where
  id := "integration.rubi_4_1_2_1_r4"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 12642
  description := "RUBI 4.1.2.1 #4"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:4" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#4"




/-- RUBI 4.1.10 #1 -/
def rubi4110r1 : CRule where
  id := "integration.rubi_4_1_10_r1"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m"))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.var "f") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "m")) (.pow (.var "f") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))]
  independent := ["c", "d", "e", "f", "m"]
  conditions := [.gt (.var "m") (.int 0)]
  priority := 12646
  description := "RUBI 4.1.10 #1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:1" "4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n.m#1"

/-- RUBI 4.1.10 #16 -/
def rubi4110r16 : CRule where
  id := "integration.rubi_4_1_10_r16"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.var "n") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m"))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "f") (.var "n")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.var "n") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))) (.var "m")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.var "n") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))))]
  independent := ["b", "c", "d", "e", "f", "m", "n"]
  conditions := [.gt (.var "n") (.int 1),
    .gt (.var "m") (.int 1)]
  priority := 12647
  description := "RUBI 4.1.10 #16"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:16" "4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n.m#16"


/-- RUBI 4.1.3.1 #9 -/
def rubi4131r9 : CRule where
  id := "integration.rubi_4_1_3_1_r9"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):9"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d"))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2)) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1)))))) (.int 0)]
  priority := 12649
  description := "RUBI 4.1.3.1 #9"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):9" "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#9"

/-- RUBI 4.1.3.1 #21 -/
def rubi4131r21 : CRule where
  id := "integration.rubi_4_1_3_1_r21"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):21"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "B") (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d")))) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .ne (.app2 .add (.var "m") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))) (.int 0)]
  priority := 12650
  description := "RUBI 4.1.3.1 #21"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):21" "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#21"

/-- RUBI 4.1.5 #1 -/
def rubi415r1 : CRule where
  id := "integration.rubi_4_1_5_r1"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:1"
  shape := .antideriv; x := "x"
  body := (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n"))
  result := (.app2 .mul (.app2 .mul (.var "a") (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.int (-1))))
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 12651
  description := "RUBI 4.1.5 #1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:1" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#1"

/-- RUBI 4.1.5 #32 -/
def rubi415r32 : CRule where
  id := "integration.rubi_4_1_5_r32"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:32"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))),
    ("I2", (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 12652
  description := "RUBI 4.1.5 #32"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:32" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#32"


/-- RUBI 4.1.7 #1 -/
def rubi417r1 : CRule where
  id := "integration.rubi_4_1_7_r1"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 4) (.var "A")) (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.var "b"))) (.app2 .mul (.var "B") (.app2 .add (.app2 .mul (.int 4) (.var "a")) (.app2 .mul (.int 3) (.var "b"))))) (.var "x")) (.pow (.int 8) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.int 4) (.var "A")) (.var "b")) (.app2 .mul (.var "B") (.app2 .add (.app2 .mul (.int 4) (.var "a")) (.app2 .mul (.int 3) (.var "b")))))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.int 8) (.var "f")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B")) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 3))) (.pow (.app2 .mul (.int 4) (.var "f")) (.int (-1)))))
  independent := ["a", "b", "e", "f", "A", "B"]
  priority := 12654
  description := "RUBI 4.1.7 #1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:1" "4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p.m#1"

/-- RUBI 4.1.7 #10 -/
def rubi417r10 : CRule where
  id := "integration.rubi_4_1_7_r10"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:10"
  shape := .antideriv; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.int 2))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.int 8) (.pow (.var "a") (.int 2))) (.app2 .mul (.app2 .mul (.int 8) (.var "a")) (.var "b"))) (.app2 .mul (.int 3) (.pow (.var "b") (.int 2)))) (.var "x")) (.pow (.int 8) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.int 8) (.var "a")) (.app2 .mul (.int 3) (.var "b")))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.int 8) (.var "f")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 3))) (.pow (.app2 .mul (.int 4) (.var "f")) (.int (-1)))))
  independent := ["a", "b", "e", "f"]
  priority := 12655
  description := "RUBI 4.1.7 #10"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:10" "4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p.m#10"

/-- RUBI 4.1.2.2 #7 -/
def rubi4122r7 : CRule where
  id := "integration.rubi_4_1_2_2_r7"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "g") (.int 2)) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "g") (.int 2))) (.pow (.app2 .mul (.var "b") (.var "d")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "d", "e", "f", "g", "n", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 12656
  description := "RUBI 4.1.2.2 #7"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:7" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#7"




/-- RUBI 4.1.2.2 #47 -/
def rubi4122r47 : CRule where
  id := "integration.rubi_4_1_2_2_r47"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:47"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)) (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "d", "e", "f", "m", "n"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.app2 .mul (.int 2) (.var "m")),
    .int (.app2 .mul (.int 2) (.var "n"))]
  priority := 12660
  description := "RUBI 4.1.2.2 #47"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:47" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#47"



/-- RUBI 4.1.2.2 #83 -/
def rubi4122r83 : CRule where
  id := "integration.rubi_4_1_2_2_r83"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:83"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.app2 .mul (.int 2) (.var "m")),
    .int (.app2 .mul (.int 2) (.var "n"))]
  priority := 12663
  description := "RUBI 4.1.2.2 #83"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:83" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#83"



/-- RUBI 4.1.1.3 #3 -/
def rubi4113r3 : CRule where
  id := "integration.rubi_4_1_1_3_r3"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")))
  result := (.app2 .mul (.pow (.var "a") (.var "p")) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.var "p")) (.pow (.pow (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "m", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.var "m"),
    .int (.var "p"),
    .eq (.var "p") (.app2 .mul (.int 2) (.var "m"))]
  priority := 12666
  description := "RUBI 4.1.1.3 #3"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m:3" "4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m.m#3"



/-- RUBI 4.1.4.1 #7 -/
def rubi4141r7 : CRule where
  id := "integration.rubi_4_1_4_1_r7"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .mul (.app2 .mul (.var "C") (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .mul (.int (-1)) (.var "a")) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "e", "f", "A", "C", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)]
  priority := 12669
  description := "RUBI 4.1.4.1 #7"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):7" "4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2).m#7"

/-- RUBI 4.1.2.3 #2 -/
def rubi4123r2 : CRule where
  id := "integration.rubi_4_1_2_3_r2"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .root (.app2 .mul (.var "g") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .root (.app2 .mul (.var "g") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .root (.app2 .mul (.var "g") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)]
  priority := 12670
  description := "RUBI 4.1.2.3 #2"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:2" "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#2"




/-- RUBI 4.1.6 #3 -/
def rubi416r3 : CRule where
  id := "integration.rubi_4_1_6_r3"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:3"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "c") (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.app2 .mul (.var "c") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)]
  priority := 12674
  description := "RUBI 4.1.6 #3"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:3" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#3"


/-- RUBI 4.1.6 #21 -/
def rubi416r21 : CRule where
  id := "integration.rubi_4_1_6_r21"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:21"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))) (.var "x")) (.pow (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.app1 .ln (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))))) (.pow (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "C"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))))) (.int 0)]
  priority := 12676
  description := "RUBI 4.1.6 #21"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:21" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#21"

/-- RUBI 4.1.6 #26 -/
def rubi416r26 : CRule where
  id := "integration.rubi_4_1_6_r26"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:26"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.var "a") (.var "B")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "A", "B", "n"]
  conditions := [.ne (.var "n") (.int (-1)),
    .eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.int 0)]
  priority := 12677
  description := "RUBI 4.1.6 #26"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:26" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#26"

/-- RUBI 4.1.6 #31 -/
def rubi416r31 : CRule where
  id := "integration.rubi_4_1_6_r31"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .mul (.var "a") (.var "B")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "a") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C")))) (.var "n")) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "a") (.int 2)) (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.pow (.var "c") (.int 2)))) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "C")))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.var "c")) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.var "C")))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "C", "n"]
  conditions := [.gt (.var "n") (.int 0),
    .ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)]
  priority := 12678
  description := "RUBI 4.1.6 #31"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:31" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#31"

/-- RUBI 4.1.6 #36 -/
def rubi416r36 : CRule where
  id := "integration.rubi_4_1_6_r36"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:36"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "C")) (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "C")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "A"))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .mul (.var "b") (.var "A")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "A", "C"]
  conditions := [.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "C"))) (.int 0)]
  priority := 12679
  description := "RUBI 4.1.6 #36"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:36" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#36"


/-- RUBI 4.7.4 #7 -/
def rubi474r7 : CRule where
  id := "integration.rubi_4_7_4_r7"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "f") (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.var "n")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.int 2) (.var "p")) (.pow (.pow (.var "f") (.var "p")) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")) (.pow (.app2 .mul (.var "f") (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app2 .add (.var "n") (.var "p")))))]
  independent := ["a", "b", "c", "d", "f", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.int 2),
    .int (.var "p")]
  priority := 12681
  description := "RUBI 4.7.4 #7"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:7" "4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n.m#7"

/-- RUBI 4.3.3.1 #2 -/
def rubi4331r2 : CRule where
  id := "integration.rubi_4_3_3_1_r2"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "B") (.var "d")) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))),
    ("I2", (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.var "b")) (.var "c")) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.var "b")) (.var "d")) (.app2 .mul (.var "B") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 12682
  description := "RUBI 4.3.3.1 #2"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):2" "4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan).m#2"

/-- RUBI 4.3.3.1 #19 -/
def rubi4331r19 : CRule where
  id := "integration.rubi_4_3_3_1_r19"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "B")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.var "d") (.var "f")) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "A")) (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.var "B")) (.var "c"))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "A")) (.var "b")) (.app2 .mul (.var "B") (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))))) (.var "d")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "d"))))) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)]
  priority := 12683
  description := "RUBI 4.3.3.1 #19"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):19" "4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan).m#19"

/-- RUBI 4.3.3.1 #27 -/
def rubi4331r27 : CRule where
  id := "integration.rubi_4_3_3_1_r27"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.pow (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.var "I1") (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.var "a") (.var "B"))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.int 1) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)]
  priority := 12684
  description := "RUBI 4.3.3.1 #27"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):27" "4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan).m#27"

/-- RUBI 4.3.1.2 #23 -/
def rubi4312r23 : CRule where
  id := "integration.rubi_4_3_1_2_r23"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sec (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .mul (.var "d") (.app1 .sec (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sec (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "a") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.app2 .add (.var "m") (.int 2))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 12685
  description := "RUBI 4.3.1.2 #23"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n:23" "4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n.m#23"


/-- RUBI 4.3.10 #17 -/
def rubi4310r17 : CRule where
  id := "integration.rubi_4_3_10_r17"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.pow (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.pow (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1))))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "f") (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.var "f"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "d")) (.var "f")) (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 12687
  description := "RUBI 4.3.10 #17"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n:17" "4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n.m#17"



/-- RUBI 4.3.2.1 #3 -/
def rubi4321r3 : CRule where
  id := "integration.rubi_4_3_2_1_r3"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:3"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d"))) (.var "x")) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.var "f") (.int (-1)))))
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0)]
  priority := 12690
  description := "RUBI 4.3.2.1 #3"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:3" "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#3"




/-- RUBI 4.5.9 #1 -/
def rubi459r1 : CRule where
  id := "integration.rubi_4_5_9_r1"; legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.9 trig^m (a+b sec^n+c sec^(2 n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))) (.app2 .mul (.var "c") (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n2")))) (.var "p"))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.app1 .sec (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))) (.app2 .mul (.int 2) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "p")]
  priority := 12694
  description := "RUBI 4.5.9 #1"
  provenance := migrated "rubi:4 Trig functions/4.5 Secant/4.5.9 trig^m (a+b sec^n+c sec^(2 n))^p:1" "4 Trig functions/4.5 Secant/4.5.9 trig^m (a+b sec^n+c sec^(2 n))^p.m#1"





























/-- RUBI 4.1.9 #6 -/
def rubi419r6 : CRule where
  id := "integration.rubi_4_1_9_r6"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))) (.app2 .mul (.var "c") (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n2")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "m")) (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))) (.app2 .mul (.int 2) (.var "p")))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "p")]
  priority := 12723
  description := "RUBI 4.1.9 #6"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p:6" "4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p.m#6"


/-- RUBI 4.1.0.1 #14 -/
def rubi4101r14 : CRule where
  id := "integration.rubi_4_1_0_1_r14"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.0.1 (a sin)^m (b trg)^n:14"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "a") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.pow (.app2 .mul (.var "b") (.app1 .sec (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .mul (.var "a") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app1 .sec (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "e", "f", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 2)) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 12725
  description := "RUBI 4.1.0.1 #14"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.0.1 (a sin)^m (b trg)^n:14" "4 Trig functions/4.1 Sine/4.1.0.1 (a sin)^m (b trg)^n.m#14"


/-- RUBI 4.1.1.2 #11 -/
def rubi4112r11 : CRule where
  id := "integration.rubi_4_1_1_2_r11"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .root (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.app2 .root (.app2 .add (.int 1) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.app2 .root (.app2 .add (.int 1) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.pow (.app2 .root (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.pow (.app2 .mul (.app2 .root (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.app2 .root (.app2 .add (.int 1) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "g"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 12727
  description := "RUBI 4.1.1.2 #11"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m:11" "4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m.m#11"




/-- RUBI 4.1.4.2 #13 -/
def rubi4142r13 : CRule where
  id := "integration.rubi_4_1_4_2_r13"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.app2 .mul (.var "a") (.var "C"))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.var "n")) (.int 2))))) (.app2 .mul (.var "B") (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "m")) (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "n") (.int 1)))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1)))))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.app2 .mul (.var "C") (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.app2 .mul (.int (-1)) (.int 1))))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "C", "n", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .gt (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1)))) (.var "m")]
  priority := 12731
  description := "RUBI 4.1.4.2 #13"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):13" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#13"


/-- RUBI 4.1.4.2 #35 -/
def rubi4142r35 : CRule where
  id := "integration.rubi_4_1_4_2_r35"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):35"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C"))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.var "C") (.pow (.app2 .mul (.var "b") (.var "d")) (.int (-1)))) (.var "I2"))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I3")))
  integrals := [("I1", (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))),
    ("I2", (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))),
    ("I3", (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "d", "e", "f", "A", "B", "C", "n"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 12733
  description := "RUBI 4.1.4.2 #35"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):35" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#35"

/-- RUBI 4.1.2.1 #5 -/
def rubi4121r5 : CRule where
  id := "integration.rubi_4_1_2_1_r5"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:5"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-2)) (.var "b")) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.int 1))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.var "n") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))]
  priority := 12734
  description := "RUBI 4.1.2.1 #5"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:5" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#5"

/-- RUBI 4.1.2.1 #15 -/
def rubi4121r15 : CRule where
  id := "integration.rubi_4_1_2_1_r15"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.var "c") (.var "I1")) (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m"))),
    ("I2", (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "m") (.int 1))))]
  independent := ["b", "c", "d", "e", "f", "m"]
  priority := 12735
  description := "RUBI 4.1.2.1 #15"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:15" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#15"



/-- RUBI 4.1.2.1 #50 -/
def rubi4121r50 : CRule where
  id := "integration.rubi_4_1_2_1_r50"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:50"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.var "n"))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "m") (.var "n"))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.app2 .add (.app2 .add (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))) (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "c") (.int 2))) (.app2 .add (.var "m") (.var "n")))) (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "n"))) (.app2 .mul (.int (-1)) (.int 1)))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .gt (.var "n") (.int 1),
    .int (.var "n")]
  priority := 12738
  description := "RUBI 4.1.2.1 #50"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:50" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#50"

/-- RUBI 4.1.2.1 #70 -/
def rubi4121r70 : CRule where
  id := "integration.rubi_4_1_2_1_r70"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:70"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)]
  priority := 12739
  description := "RUBI 4.1.2.1 #70"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:70" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#70"

/-- RUBI 4.1.10 #2 -/
def rubi4110r2 : CRule where
  id := "integration.rubi_4_1_10_r2"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))]
  independent := ["c", "d", "e", "f", "m"]
  conditions := [.gt (.int (-1)) (.var "m")]
  priority := 12740
  description := "RUBI 4.1.10 #2"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:2" "4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n.m#2"

/-- RUBI 4.1.10 #19 -/
def rubi4110r19 : CRule where
  id := "integration.rubi_4_1_10_r19"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "n")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.int 2)))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "m") (.int 2))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "m") (.int 2))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "f") (.int 2))) (.var "n")) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "m") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["b", "c", "d", "e", "f", "m", "n"]
  conditions := [.gt (.var "n") (.int 1),
    .gt (.int (-2)) (.var "m")]
  priority := 12741
  description := "RUBI 4.1.10 #19"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:19" "4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n.m#19"

/-- RUBI 4.1.3.1 #14 -/
def rubi4131r14 : CRule where
  id := "integration.rubi_4_1_3_1_r14"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):14"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-2)) (.var "b")) (.var "B")) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.int 3))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "A") (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "d")) (.app2 .add (.var "n") (.int 1)))))) (.int 0)]
  priority := 12742
  description := "RUBI 4.1.3.1 #14"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):14" "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#14"

/-- RUBI 4.1.3.1 #37 -/
def rubi4131r37 : CRule where
  id := "integration.rubi_4_1_3_1_r37"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):37"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "B") (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d")))) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)]
  priority := 12743
  description := "RUBI 4.1.3.1 #37"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):37" "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#37"

/-- RUBI 4.1.5 #5 -/
def rubi415r5 : CRule where
  id := "integration.rubi_4_1_5_r5"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:5"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))) (.int (-1))))
  independent := ["a", "b", "c", "d"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 12744
  description := "RUBI 4.1.5 #5"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:5" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#5"



/-- RUBI 4.1.5 #38 -/
def rubi415r38 : CRule where
  id := "integration.rubi_4_1_5_r38"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:38"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "m")) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I2"))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I3")))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))),
    ("I2", (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1))))),
    ("I3", (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "m")) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 2)))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.int (-1)) (.var "n"),
    .gt (.int (-1)) (.var "m")]
  priority := 12747
  description := "RUBI 4.1.5 #38"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:38" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#38"

/-- RUBI 4.1.7 #2 -/
def rubi417r2 : CRule where
  id := "integration.rubi_4_1_7_r2"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.var "p")) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.int 2) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "B")) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "A")) (.app2 .add (.var "p") (.int 1)))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "A")) (.var "b")) (.app2 .add (.var "p") (.int 1))) (.app2 .mul (.var "B") (.app2 .add (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "p"))) (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "p"))))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "e", "f", "A", "B", "p"]
  conditions := [.gt (.var "p") (.int 0)]
  priority := 12748
  description := "RUBI 4.1.7 #2"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:2" "4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p.m#2"

/-- RUBI 4.1.7 #11 -/
def rubi417r11 : CRule where
  id := "integration.rubi_4_1_7_r11"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:11"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.var "p")) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.int 2) (.var "p")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))) (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "p")))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.var "b"))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "e", "f", "p"]
  conditions := [.ne (.app2 .add (.var "a") (.var "b")) (.int 0),
    .gt (.var "p") (.int 1)]
  priority := 12749
  description := "RUBI 4.1.7 #11"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:11" "4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p.m#11"

/-- RUBI 4.1.2.2 #9 -/
def rubi4122r9 : CRule where
  id := "integration.rubi_4_1_2_2_r9"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.var "a") (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1))))) (.pow (.var "c") (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1)))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.app2 .mul (.var "p") (.pow (.int 2) (.int (-1))))]
  priority := 12750
  description := "RUBI 4.1.2.2 #9"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:9" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#9"

/-! ## Refutations -/

theorem rubi459r11_counterexample_real : ¬ rubi459r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi459r11.conditions rubi459r11.body rubi459r11.result rubi459r11.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "n" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi459r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi459r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi459r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi459r11, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi459r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi459r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi419r5_counterexample_real : ¬ rubi419r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi419r5.conditions rubi419r5.body rubi419r5.result rubi419r5.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "e" then (1 : ℝ) else if s = "p" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi419r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi419r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi419r5.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "e" then (1 : ℝ) else if s = "p" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi419r5, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi419r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi419r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4112r18_counterexample_real : ¬ rubi4112r18.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4112r18.conditions rubi4112r18.body rubi4112r18.result rubi4112r18.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then (1 : ℝ) else if s = "b" then (-1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4112r18, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4112r18, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4112r18, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4112r18, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi4142r4_counterexample_real : ¬ rubi4142r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r4.conditions rubi4142r4.body rubi4142r4.result rubi4142r4.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "d" then ((-1 : ℝ) / 2) else if s = "e" then (1 : ℝ) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "d" then ((-1 : ℝ) / 2) else if s = "e" then (1 : ℝ) else if s = "m" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r4, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4142r29_counterexample_real : ¬ rubi4142r29.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r29.conditions rubi4142r29.body rubi4142r29.result rubi4142r29.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (3 : ℝ) else if s = "c" then (4 : ℝ) else if s = "d" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r29.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (3 : ℝ) else if s = "c" then (4 : ℝ) else if s = "d" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r29, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r4_counterexample_real : ¬ rubi4121r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r4.conditions rubi4121r4.body rubi4121r4.result rubi4121r4.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "c" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r4, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4110r1_counterexample_real : ¬ rubi4110r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4110r1.conditions rubi4110r1.body rubi4110r1.result rubi4110r1.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "m" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4110r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4110r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4110r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4110r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4110r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4110r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4110r16_counterexample_real : ¬ rubi4110r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4110r16.conditions rubi4110r16.body rubi4110r16.result rubi4110r16.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "m" then (2 : ℝ) else if s = "n" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4110r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4110r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4110r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then (2 : ℝ) else if s = "n" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4110r16, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4110r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4110r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4131r9_counterexample_real : ¬ rubi4131r9.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4131r9.conditions rubi4131r9.body rubi4131r9.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "a" then (3 : ℝ) else if s = "b" then (-3 : ℝ) else if s = "d" then ((1 : ℝ) / 2) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4131r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4131r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4131r9, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4131r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4131r21_counterexample_real : ¬ rubi4131r21.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4131r21.conditions rubi4131r21.body rubi4131r21.result rubi4131r21.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "b" then ((1 : ℝ) / 2) else if s = "c" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4131r21, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4131r21, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4131r21.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "b" then ((1 : ℝ) / 2) else if s = "c" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4131r21, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4131r21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4131r21, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi415r1_counterexample_real : ¬ rubi415r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi415r1.conditions rubi415r1.body rubi415r1.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi415r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi415r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi415r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi415r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi415r32_counterexample_real : ¬ rubi415r32.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi415r32.conditions rubi415r32.body rubi415r32.result rubi415r32.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi415r32, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi415r32, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi415r32.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi415r32, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi415r32, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi415r32, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi417r1_counterexample_real : ¬ rubi417r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi417r1.conditions rubi417r1.body rubi417r1.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi417r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi417r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi417r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi417r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi417r10_counterexample_real : ¬ rubi417r10.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi417r10.conditions rubi417r10.body rubi417r10.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi417r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi417r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi417r10, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi417r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4122r7_counterexample_real : ¬ rubi4122r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r7.conditions rubi4122r7.body rubi4122r7.result rubi4122r7.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then (1 : ℝ) else if s = "b" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4122r7, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4122r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi4122r47_counterexample_real : ¬ rubi4122r47.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r47.conditions rubi4122r47.body rubi4122r47.result rubi4122r47.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r47, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r47, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4122r47.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4122r47, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4122r47, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4122r47, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4122r83_counterexample_real : ¬ rubi4122r83.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r83.conditions rubi4122r83.body rubi4122r83.result rubi4122r83.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r83, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r83, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4122r83.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4122r83, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4122r83, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4122r83, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4113r3_counterexample_real : ¬ rubi4113r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r3.conditions rubi4113r3.body rubi4113r3.result rubi4113r3.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "m" then (1 : ℝ) else if s = "p" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4113r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4113r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4113r3, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4113r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi4141r7_counterexample_real : ¬ rubi4141r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4141r7.conditions rubi4141r7.body rubi4141r7.result rubi4141r7.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4141r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4141r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4141r7.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4141r7, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4141r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4141r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4123r2_counterexample_real : ¬ rubi4123r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4123r2.conditions rubi4123r2.body rubi4123r2.result rubi4123r2.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" then (1 : ℝ) else if s = "c" then (-1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4123r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4123r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4123r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4123r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi416r3_counterexample_real : ¬ rubi416r3.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi416r3.conditions rubi416r3.body rubi416r3.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "a" then (-3 : ℝ) else if s = "c" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi416r3, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi416r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi416r21_counterexample_real : ¬ rubi416r21.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r21.conditions rubi416r21.body rubi416r21.result rubi416r21.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "A" then (2 : ℝ) else if s = "b" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r21, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r21, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r21.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then (2 : ℝ) else if s = "b" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r21, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r21, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r26_counterexample_real : ¬ rubi416r26.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi416r26.conditions rubi416r26.body rubi416r26.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r26, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r26, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi416r26, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi416r26, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi416r31_counterexample_real : ¬ rubi416r31.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r31.conditions rubi416r31.body rubi416r31.result rubi416r31.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (1 : ℝ) else if s = "n" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r31.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (1 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r31, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r31, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r36_counterexample_real : ¬ rubi416r36.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi416r36.conditions rubi416r36.body rubi416r36.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "a" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r36, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r36, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi416r36, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi416r36, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi474r7_counterexample_real : ¬ rubi474r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi474r7.conditions rubi474r7.body rubi474r7.result rubi474r7.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else if s = "p" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi474r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi474r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi474r7.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else if s = "p" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi474r7, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi474r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi474r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4331r2_counterexample_real : ¬ rubi4331r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4331r2.conditions rubi4331r2.body rubi4331r2.result rubi4331r2.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "d" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4331r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4331r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4331r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "d" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4331r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4331r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4331r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4331r19_counterexample_real : ¬ rubi4331r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4331r19.conditions rubi4331r19.body rubi4331r19.result rubi4331r19.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (1 : ℝ) else if s = "c" then ((1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4331r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4331r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4331r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (1 : ℝ) else if s = "c" then ((1 : ℝ) / 2) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4331r19, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4331r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4331r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4331r27_counterexample_real : ¬ rubi4331r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4331r27.conditions rubi4331r27.body rubi4331r27.result rubi4331r27.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" then (1 : ℝ) else if s = "c" then ((1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4331r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4331r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4331r27, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4331r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi4312r23_counterexample_real : ¬ rubi4312r23.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4312r23.conditions rubi4312r23.body rubi4312r23.result rubi4312r23.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4312r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4312r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4312r23.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4312r23, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4312r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4312r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4310r17_counterexample_real : ¬ rubi4310r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4310r17.conditions rubi4310r17.body rubi4310r17.result rubi4310r17.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4310r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4310r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4310r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4310r17, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4310r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4310r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4321r3_counterexample_real : ¬ rubi4321r3.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4321r3.conditions rubi4321r3.body rubi4321r3.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "b" then (-1 : ℝ) else if s = "c" then (1 : ℝ) else if s = "d" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4321r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4321r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4321r3, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4321r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi459r1_counterexample_real : ¬ rubi459r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi459r1.conditions rubi459r1.body rubi459r1.result rubi459r1.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "p" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi459r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi459r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi459r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi459r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi459r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi459r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi419r6_counterexample_real : ¬ rubi419r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi419r6.conditions rubi419r6.body rubi419r6.result rubi419r6.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "e" then (1 : ℝ) else if s = "p" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi419r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi419r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi419r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "e" then (1 : ℝ) else if s = "p" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi419r6, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi419r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi419r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4101r14_counterexample_real : ¬ rubi4101r14.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4101r14.conditions rubi4101r14.body rubi4101r14.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "n" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4101r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4101r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4101r14, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4101r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4112r11_counterexample_real : ¬ rubi4112r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4112r11.conditions rubi4112r11.body rubi4112r11.result rubi4112r11.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "g" then ((1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4112r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4112r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4112r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "g" then ((1 : ℝ) / 2) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4112r11, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4112r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4112r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4142r13_counterexample_real : ¬ rubi4142r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r13.conditions rubi4142r13.body rubi4142r13.result rubi4142r13.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "B" then (-1 : ℝ) else if s = "a" then (-1 : ℝ) else if s = "b" then (-1 : ℝ) else if s = "c" then (3 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "B" then (-1 : ℝ) else if s = "a" then (-1 : ℝ) else if s = "b" then (-1 : ℝ) else if s = "c" then (3 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r13, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4142r35_counterexample_real : ¬ rubi4142r35.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r35.conditions rubi4142r35.body rubi4142r35.result rubi4142r35.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "B" then (4 : ℝ) else if s = "a" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r35, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r35, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r35.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "B" then (4 : ℝ) else if s = "a" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r35, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r35, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r35, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r5_counterexample_real : ¬ rubi4121r5.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4121r5.conditions rubi4121r5.body rubi4121r5.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4121r5, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4121r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4121r15_counterexample_real : ¬ rubi4121r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r15.conditions rubi4121r15.body rubi4121r15.result rubi4121r15.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r15, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r50_counterexample_real : ¬ rubi4121r50.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r50.conditions rubi4121r50.body rubi4121r50.result rubi4121r50.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-1 : ℝ) else if s = "b" then (1 : ℝ) else if s = "d" then ((1 : ℝ) / 2) else if s = "n" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r50, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r50, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r50.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-1 : ℝ) else if s = "b" then (1 : ℝ) else if s = "d" then ((1 : ℝ) / 2) else if s = "n" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r50, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r50, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r50, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r70_counterexample_real : ¬ rubi4121r70.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r70.conditions rubi4121r70.body rubi4121r70.result rubi4121r70.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r70, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r70, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4121r70, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4121r70, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi4110r2_counterexample_real : ¬ rubi4110r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4110r2.conditions rubi4110r2.body rubi4110r2.result rubi4110r2.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "c" then ((1 : ℝ) / 2) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4110r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4110r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4110r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then ((1 : ℝ) / 2) else if s = "m" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4110r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4110r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4110r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4110r19_counterexample_real : ¬ rubi4110r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4110r19.conditions rubi4110r19.body rubi4110r19.result rubi4110r19.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "c" then (2 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4110r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4110r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4110r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "c" then (2 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4110r19, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4110r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4110r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4131r14_counterexample_real : ¬ rubi4131r14.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4131r14.conditions rubi4131r14.body rubi4131r14.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "a" then (1 : ℝ) else if s = "b" then (1 : ℝ) else if s = "d" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4131r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4131r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4131r14, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4131r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4131r37_counterexample_real : ¬ rubi4131r37.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4131r37.conditions rubi4131r37.body rubi4131r37.result rubi4131r37.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (4 : ℝ) else if s = "c" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4131r37, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4131r37, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4131r37.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (4 : ℝ) else if s = "c" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4131r37, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4131r37, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4131r37, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi415r5_counterexample_real : ¬ rubi415r5.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi415r5.conditions rubi415r5.body rubi415r5.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "a" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi415r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi415r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi415r5, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi415r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi415r38_counterexample_real : ¬ rubi415r38.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi415r38.conditions rubi415r38.body rubi415r38.result rubi415r38.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (4 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi415r38, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi415r38, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi415r38.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (4 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi415r38, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi415r38, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi415r38, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi417r2_counterexample_real : ¬ rubi417r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi417r2.conditions rubi417r2.body rubi417r2.result rubi417r2.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "p" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi417r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi417r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi417r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi417r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi417r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi417r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi417r11_counterexample_real : ¬ rubi417r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi417r11.conditions rubi417r11.body rubi417r11.result rubi417r11.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-3 : ℝ) else if s = "p" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi417r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi417r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi417r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-3 : ℝ) else if s = "p" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi417r11, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi417r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi417r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4122r9_counterexample_real : ¬ rubi4122r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r9.conditions rubi4122r9.body rubi4122r9.result rubi4122r9.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "p" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4122r9, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4122r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

end OSR.IntegrationRec173
