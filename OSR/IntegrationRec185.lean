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

namespace OSR.IntegrationRec185

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/







/-- RUBI 5.3.4 #42 -/
def rubi534r42 : CRule where
  id := "integration.rubi_5_3_4_r42"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:42"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .arctan (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  priority := 16006
  description := "RUBI 5.3.4 #42"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:42" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#42"

/-- RUBI 5.3.4 #139 -/
def rubi534r139 : CRule where
  id := "integration.rubi_5_3_4_r139"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:139"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app1 .arctan (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "f", "g"]
  priority := 16007
  description := "RUBI 5.3.4 #139"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:139" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#139"

/-- RUBI 5.3.4 #141 -/
def rubi534r141 : CRule where
  id := "integration.rubi_5_3_4_r141"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:141"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "d") (.var "I1")) (.app2 .mul (.var "e") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1))))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  priority := 16008
  description := "RUBI 5.3.4 #141"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:141" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#141"


/-- RUBI 4.5.3.1 #10 -/
def rubi4531r10 : CRule where
  id := "integration.rubi_4_5_3_1_r10"; legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec):10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.int (-1)) (.var "B"))) (.var "I1")) (.app2 .mul (.var "B") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.app2 .add (.int 1) (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "A", "B"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "A") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "B") (.int 2)))) (.int 0)]
  priority := 16010
  description := "RUBI 4.5.3.1 #10"
  provenance := migrated "rubi:4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec):10" "4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec).m#10"



/-- RUBI 4.5.1.2 #51 -/
def rubi4512r51 : CRule where
  id := "integration.rubi_4_5_1_2_r51"; legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:51"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.int (-1)) (.var "I1")) (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.app2 .add (.int 1) (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "e", "f"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 16013
  description := "RUBI 4.5.1.2 #51"
  provenance := migrated "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:51" "4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.m#51"

/-- RUBI 4.5.4.1 #18 -/
def rubi4541r18 : CRule where
  id := "integration.rubi_4_5_4_1_r18"; legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.4.1 (a+b sec)^m (A+B sec+C sec^2):18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.var "I1") (.app2 .mul (.var "C") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.app2 .add (.var "B") (.app2 .mul (.int (-1)) (.var "C"))) (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.app2 .add (.int 1) (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "A", "B", "C"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 16014
  description := "RUBI 4.5.4.1 #18"
  provenance := migrated "rubi:4 Trig functions/4.5 Secant/4.5.4.1 (a+b sec)^m (A+B sec+C sec^2):18" "4 Trig functions/4.5 Secant/4.5.4.1 (a+b sec)^m (A+B sec+C sec^2).m#18"

/-- RUBI 4.5.4.1 #19 -/
def rubi4541r19 : CRule where
  id := "integration.rubi_4_5_4_1_r19"; legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.4.1 (a+b sec)^m (A+B sec+C sec^2):19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.var "I1") (.app2 .mul (.var "C") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.app2 .add (.int 1) (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "A", "C"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 16015
  description := "RUBI 4.5.4.1 #19"
  provenance := migrated "rubi:4 Trig functions/4.5 Secant/4.5.4.1 (a+b sec)^m (A+B sec+C sec^2):19" "4 Trig functions/4.5 Secant/4.5.4.1 (a+b sec)^m (A+B sec+C sec^2).m#19"


/-- RUBI 4.5.2.1 #12 -/
def rubi4521r12 : CRule where
  id := "integration.rubi_4_5_2_1_r12"; legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "x")) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.var "I1"))) (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "I2")))
  integrals := [("I1", (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))),
    ("I2", (.pow (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0)]
  priority := 16017
  description := "RUBI 4.5.2.1 #12"
  provenance := migrated "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:12" "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#12"







/-- RUBI 4.5.1.1 #7 -/
def rubi4511r7 : CRule where
  id := "integration.rubi_4_5_1_1_r7"; legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.1 (a+b sec)^n:7"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int 2))
  result := (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "a") (.int 2)) (.var "x")) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.var "I1"))) (.app2 .mul (.pow (.var "b") (.int 2)) (.var "I2")))
  integrals := [("I1", (.app1 .csc (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))),
    ("I2", (.pow (.app1 .csc (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int 2)))]
  independent := ["a", "b", "c", "d"]
  priority := 16024
  description := "RUBI 4.5.1.1 #7"
  provenance := migrated "rubi:4 Trig functions/4.5 Secant/4.5.1.1 (a+b sec)^n:7" "4 Trig functions/4.5 Secant/4.5.1.1 (a+b sec)^n.m#7"















/-- RUBI 4.3.1.1 #12 -/
def rubi4311r12x : CRule where
  id := "integration.rubi_4_3_1_1_r12"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "x")) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 16039
  description := "RUBI 4.3.1.1 #12"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n:12" "4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n.m#12"



/-- RUBI 4.3.4.1 #8 -/
def rubi4341r8 : CRule where
  id := "integration.rubi_4_3_4_1_r8"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.var "B") (.var "x")) (.app2 .mul (.var "A") (.var "I1"))) (.app2 .mul (.var "C") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int (-1))))),
    ("I2", (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))]
  independent := ["e", "f", "A", "B", "C"]
  conditions := [.ne (.var "A") (.var "C")]
  priority := 16042
  description := "RUBI 4.3.4.1 #8"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):8" "4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2).m#8"














theorem rubi534r42_real : rubi534r42.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r42.conditions rubi534r42.body rubi534r42.result rubi534r42.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi534r42, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r42, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi534r42, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi534r42, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi534r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi534r42, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((hΦ1.const_mul (env "a")).add (hΦ2.const_mul (env "b")))
    convert hD using 1
    · funext v
      simp [rubi534r42, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi534r42, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi534r42_complex : rubi534r42.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi534r42.conditions rubi534r42.body rubi534r42.result rubi534r42.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi534r42, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r42, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi534r42, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi534r42, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi534r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi534r42, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((hΦ1.const_mul (env "a")).add (hΦ2.const_mul (env "b")))
    convert hD using 1
    · funext v
      simp [rubi534r42, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi534r42, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi534r139_real : rubi534r139.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r139.conditions rubi534r139.body rubi534r139.result rubi534r139.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi534r139, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r139, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi534r139, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi534r139, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi534r139, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi534r139, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((hΦ1.const_mul (env "a")).add (hΦ2.const_mul (env "b")))
    convert hD using 1
    · funext v
      simp [rubi534r139, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi534r139, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi534r139_complex : rubi534r139.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi534r139.conditions rubi534r139.body rubi534r139.result rubi534r139.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi534r139, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r139, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi534r139, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi534r139, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi534r139, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi534r139, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((hΦ1.const_mul (env "a")).add (hΦ2.const_mul (env "b")))
    convert hD using 1
    · funext v
      simp [rubi534r139, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi534r139, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi534r141_real : rubi534r141.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r141.conditions rubi534r141.body rubi534r141.result rubi534r141.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi534r141, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r141, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi534r141, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi534r141, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi534r141, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi534r141, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((hΦ1.const_mul (env "d")).add (hΦ2.const_mul (env "e")))
    convert hD using 1
    · funext v
      simp [rubi534r141, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi534r141, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi534r141_complex : rubi534r141.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi534r141.conditions rubi534r141.body rubi534r141.result rubi534r141.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi534r141, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r141, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi534r141, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi534r141, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi534r141, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi534r141, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((hΦ1.const_mul (env "d")).add (hΦ2.const_mul (env "e")))
    convert hD using 1
    · funext v
      simp [rubi534r141, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi534r141, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4531r10_real : rubi4531r10.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4531r10.conditions rubi4531r10.body rubi4531r10.result rubi4531r10.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4531r10, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4531r10, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4531r10, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4531r10, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4531r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4531r10, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((hΦ1.const_mul ((env "A" + ((-1 : ℝ) * env "B")))).add (hΦ2.const_mul (env "B")))
    convert hD using 1
    · funext v
      simp [rubi4531r10, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4531r10, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4512r51_real : rubi4512r51.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4512r51.conditions rubi4512r51.body rubi4512r51.result rubi4512r51.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4512r51, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4512r51, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4512r51, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4512r51, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4512r51, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4512r51, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((hΦ1.const_mul ((-1 : ℝ))).add (hΦ2.const_mul (1)))
    convert hD using 1
    · funext v
      simp [rubi4512r51, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4512r51, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4541r18_real : rubi4541r18.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4541r18.conditions rubi4541r18.body rubi4541r18.result rubi4541r18.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4541r18, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4541r18, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4541r18, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4541r18, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4541r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4541r18, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((hΦ1.const_mul (1)).add (hΦ2.const_mul (env "C")))
    convert hD using 1
    · funext v
      simp [rubi4541r18, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4541r18, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4541r19_real : rubi4541r19.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4541r19.conditions rubi4541r19.body rubi4541r19.result rubi4541r19.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4541r19, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4541r19, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4541r19, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4541r19, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4541r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4541r19, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((hΦ1.const_mul (1)).add (hΦ2.const_mul (env "C")))
    convert hD using 1
    · funext v
      simp [rubi4541r19, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4541r19, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4521r12_real : rubi4521r12.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4521r12.conditions rubi4521r12.body rubi4521r12.result rubi4521r12.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4521r12, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4521r12, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4521r12, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4521r12, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4521r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4521r12, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (env "a" * env "c")).add (hΦ1.const_mul (((env "b" * env "c") + (env "a" * env "d"))))).add (hΦ2.const_mul (env "b" * env "d")))
    convert hD using 1
    · funext v
      simp [rubi4521r12, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4521r12, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4511r7_real : rubi4511r7.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4511r7.conditions rubi4511r7.body rubi4511r7.result rubi4511r7.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4511r7, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4511r7, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4511r7, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4511r7, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4511r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4511r7, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul ((env "a" ^ 2))).add (hΦ1.const_mul ((2 : ℝ) * env "a" * env "b"))).add (hΦ2.const_mul ((env "b" ^ 2))))
    convert hD using 1
    · funext v
      simp [rubi4511r7, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4511r7, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4311r12x_real : rubi4311r12x.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4311r12x.conditions rubi4311r12x.body rubi4311r12x.result rubi4311r12x.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4311r12x, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4311r12x, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4311r12x, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4311r12x, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4311r12x, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi4311r12x, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (((hasDerivAt_id t).const_mul (env "a" * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul (env "b" * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4311r12x, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4311r12x, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4311r12x_complex : rubi4311r12x.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4311r12x.conditions rubi4311r12x.body rubi4311r12x.result rubi4311r12x.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4311r12x, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4311r12x, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4311r12x, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4311r12x, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4311r12x, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    have hΦ1 := hΦ
    simp only [rubi4311r12x, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1
    have hD := (((hasDerivAt_id t).const_mul (env "a" * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)).add (hΦ1.const_mul (env "b" * (((env "a" ^ 2) + (env "b" ^ 2)))⁻¹)))
    convert hD using 1
    · funext v
      simp [rubi4311r12x, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4311r12x, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4341r8_real : rubi4341r8.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4341r8.conditions rubi4341r8.body rubi4341r8.result rubi4341r8.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4341r8, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r8, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4341r8, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4341r8, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4341r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4341r8, eval, recEnv, Interp.real, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (env "B")).add (hΦ1.const_mul (env "A"))).add (hΦ2.const_mul (env "C")))
    convert hD using 1
    · funext v
      simp [rubi4341r8, eval, recEnv, Interp.real, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4341r8, eval, Interp.real, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

theorem rubi4341r8_complex : rubi4341r8.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4341r8.conditions rubi4341r8.body rubi4341r8.result rubi4341r8.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4341r8, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r8, List.mem_cons, List.not_mem_nil, or_false] at hi
    (try rcases hi with hi | hi) <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4341r8, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4341r8, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4341r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp only [rubi4341r8, eval, recEnv, Interp.complex, i2, im1, List.map, List.mem_cons, List.not_mem_nil, or_false,
      Function.update, if_pos, if_neg] at hΦ1 hΦ2
    have hD := ((((hasDerivAt_id t).const_mul (env "B")).add (hΦ1.const_mul (env "A"))).add (hΦ2.const_mul (env "C")))
    convert hD using 1
    · funext v
      simp [rubi4341r8, eval, recEnv, Interp.complex, i2, im1]
      all_goals first | ring1 | (trace_state; sorry)
    · simp [rubi4341r8, eval, Interp.complex, i2, im1] at hΦ1 ⊢
      all_goals first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2))
      | (trace_state; sorry)

end OSR.IntegrationRec185
