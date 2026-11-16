import OSR.IntegrationRec29

/-!
# Integration (RUBI): random-sampling refutations of the wider pass

The 144 candidates of the wider inventory pass without a grid proposal were
searched again by random sampling (development tool, proposes only); 17
proposals came back.  The refutations of those not using `Sqrt` (which waits
for the converter's `arith1#root` convention) are Lean theorems below, per
domain.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec30

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.3.4 #34 -/
def rubi1234r34 : CRule where
  id := "integration.rubi_1_2_3_4_r34"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:34"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.pow (.var "f") (.var "n")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.var "m"))) (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.app2 .mul (.int 2) (.var "n"))) (.var "m")) (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "c", "d", "e", "f", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .int (.var "p")]
  priority := 5540
  description := "RUBI 1.2.3.4 #34"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:34" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#34"

/-- RUBI 1.2.3.4 #40 -/
def rubi1234r40 : CRule where
  id := "integration.rubi_1_2_3_4_r40"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:40"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "f") (.var "n"))) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "c", "d", "e", "f", "p", "m", "n", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "m"),
    .int (.var "p")]
  priority := 5550
  description := "RUBI 1.2.3.4 #40"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:40" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#40"

/-- RUBI 1.2.3.4 #61 -/
def rubi1234r61 : CRule where
  id := "integration.rubi_1_2_3_4_r61"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:61"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "d") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.pow (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.app2 .mul (.int 2) (.var "n")))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.var "p") (.int 0),
    .gt (.app2 .mul (.int (-1)) (.var "n")) (.var "m")]
  priority := 5560
  description := "RUBI 1.2.3.4 #61"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:61" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#61"

/-- RUBI 1.2.3.4 #64 -/
def rubi1234r64 : CRule where
  id := "integration.rubi_1_2_3_4_r64"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:64"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "d") (.var "e")) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.pow (.var "f") (.var "n"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.var "p") (.int 0),
    .gt (.int 0) (.var "m")]
  priority := 5570
  description := "RUBI 1.2.3.4 #64"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:64" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#64"

/-- RUBI 1.2.3.4 #66 -/
def rubi1234r66 : CRule where
  id := "integration.rubi_1_2_3_4_r66"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:66"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "f") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.var "n")]
  priority := 5580
  description := "RUBI 1.2.3.4 #66"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:66" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#66"

/-- RUBI 1.2.3.4 #67 -/
def rubi1234r67 : CRule where
  id := "integration.rubi_1_2_3_4_r67"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:67"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "f") (.var "n")) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")) (.pow (.var "f") (.var "n"))) (.pow (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 0)]
  priority := 5590
  description := "RUBI 1.2.3.4 #67"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:67" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#67"

/-- RUBI 1.2.3.5 #6 -/
def rubi1235r6 : CRule where
  id := "integration.rubi_1_2_3_5_r6"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:6"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "f") (.pow (.var "x") (.var "n2")))) (.app2 .mul (.var "g") (.pow (.var "x") (.var "n3")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.pow (.var "a") (.int 2)) (.app2 .add (.var "n") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "g", "n", "p", "n2", "n3"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.var "n3") (.app2 .mul (.int 3) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "g")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 1))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 2))) (.int 1))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))))) (.int 0)]
  priority := 5610
  description := "RUBI 1.2.3.5 #6"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:6" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p.m#6"

/-- RUBI 1.2.3.5 #7 -/
def rubi1235r7 : CRule where
  id := "integration.rubi_1_2_3_5_r7"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:7"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n2")))) (.app2 .mul (.var "g") (.pow (.var "x") (.var "n3")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.pow (.var "a") (.int 2)) (.app2 .add (.var "n") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "f", "g", "n", "p", "n2", "n3"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.var "n3") (.app2 .mul (.int 3) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "g")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 1))) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 2))) (.int 1))) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0)]
  priority := 5620
  description := "RUBI 1.2.3.5 #7"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:7" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p.m#7"

/-- RUBI 1.2.3.5 #8 -/
def rubi1235r8 : CRule where
  id := "integration.rubi_1_2_3_5_r8"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:8"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "g") (.pow (.var "x") (.var "n3")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.pow (.var "a") (.int 2)) (.app2 .add (.var "n") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "g", "n", "p", "n2", "n3"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.var "n3") (.app2 .mul (.int 3) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "g")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 1))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 1))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 2))) (.int 1))) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))))) (.int 0)]
  priority := 5630
  description := "RUBI 1.2.3.5 #8"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:8" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p.m#8"

/-- RUBI 1.2.3.5 #9 -/
def rubi1235r9 : CRule where
  id := "integration.rubi_1_2_3_5_r9"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:9"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "g") (.pow (.var "x") (.var "n3")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.pow (.var "a") (.int 2)) (.app2 .add (.var "n") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "g", "n", "p", "n2", "n3"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.var "n3") (.app2 .mul (.int 3) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "g")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 1))) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.var "d")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 2))) (.int 1))) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)))) (.int 0)]
  priority := 5640
  description := "RUBI 1.2.3.5 #9"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p:9" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p.m#9"

/-- RUBI 3.2.1 #10 -/
def rubi321r10 : CRule where
  id := "integration.rubi_3_2_1_r10"; legacyId := some "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "mn")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .ln (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.int (-1)))))))) (.pow (.var "g") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "B") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "g") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "A", "B", "n", "mn"]
  conditions := [.eq (.app2 .add (.var "n") (.var "mn")) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "d") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "g"))) (.int 0)]
  priority := 5650
  description := "RUBI 3.2.1 #10"
  provenance := migrated "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:10" "3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.m#10"

/-- RUBI 3.2.1 #8 -/
def rubi321r8 : CRule where
  id := "integration.rubi_3_2_1_r8"; legacyId := some "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "mn")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .ln (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.int (-1)))))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "n"))) (.pow (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.int (-1)))))))) (.pow (.var "g") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "B") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "g") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.int (-1))))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "A", "B", "n", "mn"]
  conditions := [.eq (.app2 .add (.var "n") (.var "mn")) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "g"))) (.int 0)]
  priority := 5660
  description := "RUBI 3.2.1 #8"
  provenance := migrated "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:8" "3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.m#8"

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

theorem rubi1234r34_counterexample_real : ¬ rubi1234r34.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r34.conditions rubi1234r34.body rubi1234r34.result rubi1234r34.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "p" then -3 else if s = "n" then 1 else if s = "m" ∨ s = "n2" then 2 else if s = "a" then 4 else 0) (1 : ℝ) (by simp [rubi1234r34, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1234r34, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r34.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "p" then -3 else if s = "n" then 1 else if s = "m" ∨ s = "n2" then 2 else if s = "a" then 4 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r34, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r34, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1234r34_counterexample_complex : ¬ rubi1234r34.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1234r34.conditions rubi1234r34.body rubi1234r34.result rubi1234r34.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "p" then -3 else if s = "n" then 1 else if s = "m" ∨ s = "n2" then 2 else if s = "a" then 4 else 0) (1 : ℂ) (by simp [rubi1234r34, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1234r34, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r34.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "p" then -3 else if s = "n" then 1 else if s = "m" ∨ s = "n2" then 2 else if s = "a" then 4 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r34, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r34, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1234r40_counterexample_real : ¬ rubi1234r40.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r40.conditions rubi1234r40.body rubi1234r40.result rubi1234r40.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -2 else if s = "f" then -3 else if s = "n" then 1 else if s = "d" ∨ s = "n2" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi1234r40, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1234r40, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r40.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -2 else if s = "f" then -3 else if s = "n" then 1 else if s = "d" ∨ s = "n2" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r40, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r40, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1234r40_counterexample_complex : ¬ rubi1234r40.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1234r40.conditions rubi1234r40.body rubi1234r40.result rubi1234r40.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -2 else if s = "f" then -3 else if s = "n" then 1 else if s = "d" ∨ s = "n2" ∨ s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi1234r40, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1234r40, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r40.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -2 else if s = "f" then -3 else if s = "n" then 1 else if s = "d" ∨ s = "n2" ∨ s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r40, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r40, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1234r61_counterexample_real : ¬ rubi1234r61.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r61.conditions rubi1234r61.body rubi1234r61.result rubi1234r61.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" then -1 else if s = "m" then -2 else if s = "a" ∨ s = "b" then -3 else if s = "f" ∨ s = "n" then 1 else if s = "n2" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi1234r61, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1234r61, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r61.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "e" then -1 else if s = "m" then -2 else if s = "a" ∨ s = "b" then -3 else if s = "f" ∨ s = "n" then 1 else if s = "n2" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r61, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r61, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1234r61_counterexample_complex : ¬ rubi1234r61.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1234r61.conditions rubi1234r61.body rubi1234r61.result rubi1234r61.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" then -1 else if s = "m" then -2 else if s = "a" ∨ s = "b" then -3 else if s = "f" ∨ s = "n" then 1 else if s = "n2" ∨ s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi1234r61, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1234r61, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r61.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "e" then -1 else if s = "m" then -2 else if s = "a" ∨ s = "b" then -3 else if s = "f" ∨ s = "n" then 1 else if s = "n2" ∨ s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r61, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r61, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1234r64_counterexample_real : ¬ rubi1234r64.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r64.conditions rubi1234r64.body rubi1234r64.result rubi1234r64.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -1 else if s = "e" then -2 else if s = "c" then 1 else if s = "n" ∨ s = "p" then 2 else if s = "f" ∨ s = "n2" then 4 else 0) (1 : ℝ) (by simp [rubi1234r64, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1234r64, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r64.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -1 else if s = "e" then -2 else if s = "c" then 1 else if s = "n" ∨ s = "p" then 2 else if s = "f" ∨ s = "n2" then 4 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r64, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r64, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1234r64_counterexample_complex : ¬ rubi1234r64.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1234r64.conditions rubi1234r64.body rubi1234r64.result rubi1234r64.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -1 else if s = "e" then -2 else if s = "c" then 1 else if s = "n" ∨ s = "p" then 2 else if s = "f" ∨ s = "n2" then 4 else 0) (1 : ℂ) (by simp [rubi1234r64, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1234r64, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r64.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -1 else if s = "e" then -2 else if s = "c" then 1 else if s = "n" ∨ s = "p" then 2 else if s = "f" ∨ s = "n2" then 4 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r64, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r64, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1234r66_counterexample_real : ¬ rubi1234r66.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r66.conditions rubi1234r66.body rubi1234r66.result rubi1234r66.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "n" then 1 else if s = "e" ∨ s = "m" ∨ s = "n2" then 2 else if s = "c" then 3 else 0) (1 : ℝ) (by simp [rubi1234r66, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1234r66, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r66.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "n" then 1 else if s = "e" ∨ s = "m" ∨ s = "n2" then 2 else if s = "c" then 3 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r66, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r66, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1234r66_counterexample_complex : ¬ rubi1234r66.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1234r66.conditions rubi1234r66.body rubi1234r66.result rubi1234r66.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "n" then 1 else if s = "e" ∨ s = "m" ∨ s = "n2" then 2 else if s = "c" then 3 else 0) (1 : ℂ) (by simp [rubi1234r66, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1234r66, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r66.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "n" then 1 else if s = "e" ∨ s = "m" ∨ s = "n2" then 2 else if s = "c" then 3 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r66, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r66, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1234r67_counterexample_real : ¬ rubi1234r67.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r67.conditions rubi1234r67.body rubi1234r67.result rubi1234r67.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "f" then -1 else if s = "p" then -3 else if s = "n" then 2 else if s = "d" ∨ s = "m" then 3 else if s = "b" ∨ s = "n2" then 4 else 0) (1 : ℝ) (by simp [rubi1234r67, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi1234r67, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r67.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "f" then -1 else if s = "p" then -3 else if s = "n" then 2 else if s = "d" ∨ s = "m" then 3 else if s = "b" ∨ s = "n2" then 4 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r67, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r67, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1234r67_counterexample_complex : ¬ rubi1234r67.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1234r67.conditions rubi1234r67.body rubi1234r67.result rubi1234r67.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "f" then -1 else if s = "p" then -3 else if s = "n" then 2 else if s = "d" ∨ s = "m" then 3 else if s = "b" ∨ s = "n2" then 4 else 0) (1 : ℂ) (by simp [rubi1234r67, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi1234r67, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, hw] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi1234r67.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "f" then -1 else if s = "p" then -3 else if s = "n" then 2 else if s = "d" ∨ s = "m" then 3 else if s = "b" ∨ s = "n2" then 4 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi1234r67, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi1234r67, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi1235r6_counterexample_real : ¬ rubi1235r6.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1235r6.conditions rubi1235r6.body rubi1235r6.result
  refine not_antiderivHoldsUnder (fun s => if s = "f" then -3 else if s = "e" then 2 else if s = "b" then 4 else 0) (1 : ℝ) (by simp [rubi1235r6, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1235r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1235r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1235r6_counterexample_complex : ¬ rubi1235r6.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1235r6.conditions rubi1235r6.body rubi1235r6.result
  refine not_antiderivHoldsUnder (fun s => if s = "f" then -3 else if s = "e" then 2 else if s = "b" then 4 else 0) (1 : ℂ) (by simp [rubi1235r6, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1235r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1235r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1235r7_counterexample_real : ¬ rubi1235r7.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1235r7.conditions rubi1235r7.body rubi1235r7.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" then -1 else if s = "f" then -3 else if s = "g" then 2 else 0) (1 : ℝ) (by simp [rubi1235r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1235r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1235r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1235r7_counterexample_complex : ¬ rubi1235r7.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1235r7.conditions rubi1235r7.body rubi1235r7.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" then -1 else if s = "f" then -3 else if s = "g" then 2 else 0) (1 : ℂ) (by simp [rubi1235r7, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1235r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1235r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1235r8_counterexample_real : ¬ rubi1235r8.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1235r8.conditions rubi1235r8.body rubi1235r8.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" then -2 else 0) (1 : ℝ) (by simp [rubi1235r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1235r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1235r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1235r8_counterexample_complex : ¬ rubi1235r8.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1235r8.conditions rubi1235r8.body rubi1235r8.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" then -2 else 0) (1 : ℂ) (by simp [rubi1235r8, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1235r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1235r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1235r9_counterexample_real : ¬ rubi1235r9.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi1235r9.conditions rubi1235r9.body rubi1235r9.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" then -2 else if s = "p" then 4 else 0) (1 : ℝ) (by simp [rubi1235r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1235r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1235r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1235r9_counterexample_complex : ¬ rubi1235r9.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi1235r9.conditions rubi1235r9.body rubi1235r9.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" then -2 else if s = "p" then 4 else 0) (1 : ℂ) (by simp [rubi1235r9, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi1235r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num) ?_
  intro h
  simp [rubi1235r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi321r10_counterexample_real : ¬ rubi321r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi321r10.conditions rubi321r10.body rubi321r10.result rubi321r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" then -1 else if s = "f" then 1 else if s = "c" then 2 else if s = "e" then 3 else 0) (1 : ℝ) (by simp [rubi321r10, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi321r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi321r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then -1 else if s = "f" then 1 else if s = "c" then 2 else if s = "e" then 3 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi321r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi321r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi321r10_counterexample_complex : ¬ rubi321r10.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi321r10.conditions rubi321r10.body rubi321r10.result rubi321r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" then -1 else if s = "f" then 1 else if s = "c" then 2 else if s = "e" then 3 else 0) (1 : ℂ) (by simp [rubi321r10, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi321r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi321r10.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" then -1 else if s = "f" then 1 else if s = "c" then 2 else if s = "e" then 3 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi321r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi321r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi321r8_counterexample_real : ¬ rubi321r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi321r8.conditions rubi321r8.body rubi321r8.result rubi321r8.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "f" then -1 else if s = "a" then -2 else if s = "A" ∨ s = "d" then 2 else if s = "e" then 3 else if s = "B" then 4 else 0) (1 : ℝ) (by simp [rubi321r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi321r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi321r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "f" then -1 else if s = "a" then -2 else if s = "A" ∨ s = "d" then 2 else if s = "e" then 3 else if s = "B" then 4 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi321r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi321r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi321r8_counterexample_complex : ¬ rubi321r8.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi321r8.conditions rubi321r8.body rubi321r8.result rubi321r8.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "f" then -1 else if s = "a" then -2 else if s = "A" ∨ s = "d" then 2 else if s = "e" then 3 else if s = "B" then 4 else 0) (1 : ℂ) (by simp [rubi321r8, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (Eventually.of_forall fun w => by simp [rubi321r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num)
    (fun h w => w * (((rubi321r8.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "f" then -1 else if s = "a" then -2 else if s = "A" ∨ s = "d" then 2 else if s = "e" then 3 else if s = "B" then 4 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi321r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi321r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec30
