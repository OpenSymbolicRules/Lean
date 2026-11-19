import OSR.IntegrationRec91

/-!
# Integration (RUBI): refutations at a single point

1.2.2.8 #1, #2 and 1.3.3 #6 split `1/((d + e x) √Q)` with `(d² - e² x²)⁻¹`,
undefined at `d = e x` where the integrand is defined; 1.2.2.3 #47, #48, #51,
#52 and 1.2.2.4 #71, #72 rewrite with `√(e + d/x²)`, undefined at `x = 0`
where the integrand is defined; 3.1.2 #12 divides by `x^(m₁ q₁ + m₂ q₂)`,
undefined at `x = 0` for `n = 0`.  Refuted over ℝ (`arith1#root` has no complex
interpretation in the fragment).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec162

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.2.8 #1 -/
def rubi1228r1 : CRule where
  id := "integration.rubi_1_2_2_8_r1"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "d") (.var "I1")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.pow (.var "d") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1))))),
    ("I2", (.app2 .mul (.var "x") (.pow (.app2 .mul (.app2 .add (.pow (.var "d") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  priority := 11897
  description := "RUBI 1.2.2.8 #1"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p:1" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p.m#1"

/-- RUBI 1.2.2.8 #2 -/
def rubi1228r2 : CRule where
  id := "integration.rubi_1_2_2_8_r2"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "d") (.var "I1")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.pow (.var "d") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1))))),
    ("I2", (.app2 .mul (.var "x") (.pow (.app2 .mul (.app2 .add (.pow (.var "d") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "c", "d", "e"]
  priority := 11898
  description := "RUBI 1.2.2.8 #2"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p:2" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p.m#2"

/-- RUBI 1.3.3 #6 -/
def rubi133r6 : CRule where
  id := "integration.rubi_1_3_3_r6"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))),
    ("I2", (.app2 .mul (.var "x") (.pow (.app2 .mul (.app2 .mul (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  priority := 11899
  description := "RUBI 1.3.3 #6"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:6" "1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions.m#6"

/-- RUBI 1.2.2.3 #47 -/
def rubi1223r47 : CRule where
  id := "integration.rubi_1_2_2_3_r47"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:47"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 3)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "d") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.int 2))) (.app2 .root (.app2 .add (.app2 .add (.var "c") (.app2 .mul (.var "b") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.app2 .mul (.var "a") (.pow (.pow (.var "x") (.int 4)) (.int (-1))))) (.int 2))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 3)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "d") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.int 2))) (.app2 .root (.app2 .add (.app2 .add (.var "c") (.app2 .mul (.var "b") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.app2 .mul (.var "a") (.pow (.pow (.var "x") (.int 4)) (.int (-1))))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)]
  priority := 11900
  description := "RUBI 1.2.2.3 #47"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:47" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#47"

/-- RUBI 1.2.2.3 #48 -/
def rubi1223r48 : CRule where
  id := "integration.rubi_1_2_2_3_r48"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:48"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 3)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "d") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.int 2))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "a") (.pow (.pow (.var "x") (.int 4)) (.int (-1))))) (.int 2))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 3)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "d") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.int 2))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "a") (.pow (.pow (.var "x") (.int 4)) (.int (-1))))) (.int 2))) (.int (-1)))))]
  independent := ["a", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)]
  priority := 11901
  description := "RUBI 1.2.2.3 #48"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:48" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#48"

/-- RUBI 1.2.2.3 #51 -/
def rubi1223r51 : CRule where
  id := "integration.rubi_1_2_2_3_r51"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:51"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "d") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.int 2)) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.var "x") (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .root (.app2 .add (.app2 .add (.var "c") (.app2 .mul (.var "b") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.app2 .mul (.var "a") (.pow (.pow (.var "x") (.int 4)) (.int (-1))))) (.int 2))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.app2 .root (.app2 .add (.app2 .add (.var "c") (.app2 .mul (.var "b") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.app2 .mul (.var "a") (.pow (.pow (.var "x") (.int 4)) (.int (-1))))) (.int 2))) (.pow (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "d") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)]
  priority := 11902
  description := "RUBI 1.2.2.3 #51"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:51" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#51"

/-- RUBI 1.2.2.3 #52 -/
def rubi1223r52 : CRule where
  id := "integration.rubi_1_2_2_3_r52"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:52"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "d") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.int 2)) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.var "x") (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "a") (.pow (.pow (.var "x") (.int 4)) (.int (-1))))) (.int 2))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "a") (.pow (.pow (.var "x") (.int 4)) (.int (-1))))) (.int 2))) (.pow (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "d") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.int 2)) (.int (-1)))))]
  independent := ["a", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0)]
  priority := 11903
  description := "RUBI 1.2.2.3 #52"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:52" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#52"

/-- RUBI 1.2.2.4 #71 -/
def rubi1224r71 : CRule where
  id := "integration.rubi_1_2_2_4_r71"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:71"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 3)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "d") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.int 2))) (.app2 .root (.app2 .add (.app2 .add (.var "c") (.app2 .mul (.var "b") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.app2 .mul (.var "a") (.pow (.pow (.var "x") (.int 4)) (.int (-1))))) (.int 2))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 3)))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "d") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.int 2)) (.app2 .root (.app2 .add (.app2 .add (.var "c") (.app2 .mul (.var "b") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.app2 .mul (.var "a") (.pow (.pow (.var "x") (.int 4)) (.int (-1))))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))]
  priority := 11904
  description := "RUBI 1.2.2.4 #71"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:71" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#71"

/-- RUBI 1.2.2.4 #72 -/
def rubi1224r72 : CRule where
  id := "integration.rubi_1_2_2_4_r72"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:72"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 3)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "d") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.int 2))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "a") (.pow (.pow (.var "x") (.int 4)) (.int (-1))))) (.int 2))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 3)))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "d") (.pow (.pow (.var "x") (.int 2)) (.int (-1))))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "a") (.pow (.pow (.var "x") (.int 4)) (.int (-1))))) (.int 2))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "m"]
  conditions := [.int (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))]
  priority := 11905
  description := "RUBI 1.2.2.4 #72"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:72" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#72"

/-- RUBI 3.1.2 #12 -/
def rubi312r12 : CRule where
  id := "integration.rubi_3_1_2_r12"; legacyId := some "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d1") (.pow (.var "x") (.var "q1"))) (.var "m1")) (.pow (.app2 .mul (.var "d2") (.pow (.var "x") (.var "q2"))) (.var "m2"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d1") (.pow (.var "x") (.var "q1"))) (.var "m1")) (.pow (.app2 .mul (.var "d2") (.pow (.var "x") (.var "q2"))) (.var "m2"))) (.pow (.pow (.var "x") (.app2 .add (.app2 .mul (.var "m1") (.var "q1")) (.app2 .mul (.var "m2") (.var "q2")))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .mul (.var "m1") (.var "q1")) (.app2 .mul (.var "m2") (.var "q2")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d1", "d2", "m1", "m2", "n", "p", "q1", "q2"]
  priority := 11906
  description := "RUBI 3.1.2 #12"
  provenance := migrated "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:12" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#12"

/-! ## Refutations -/

theorem rubi1228r1_counterexample_real : ¬ rubi1228r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1228r1.conditions rubi1228r1.body rubi1228r1.result rubi1228r1.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have im4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "d" ∨ s = "e" ∨ s = "a" then 1 else 0) (1 : ℝ) ?_ ?_ ?_
  · simp [rubi1228r1, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
  · exact by
      have h1 : ∀ᶠ v in 𝓝 (1 : ℝ), (1 : ℝ) + v ≠ 0 := ((continuous_const.add continuous_id).continuousAt).eventually_ne (by norm_num)
      filter_upwards [h1] with v hv
      simp [rubi1228r1, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
      first | exact hv | (intro h; exact hv (by linarith)) | (rw [add_comm] at hv; exact hv) | (trace_state; sorry)
  · first
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1228r1, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩; simp [rubi1228r1, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1228r1, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; norm_num)
      | (trace_state; sorry)

theorem rubi1228r2_counterexample_real : ¬ rubi1228r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1228r2.conditions rubi1228r2.body rubi1228r2.result rubi1228r2.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have im4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "d" ∨ s = "e" ∨ s = "a" then 1 else 0) (1 : ℝ) ?_ ?_ ?_
  · simp [rubi1228r2, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
  · exact by
      have h1 : ∀ᶠ v in 𝓝 (1 : ℝ), (1 : ℝ) + v ≠ 0 := ((continuous_const.add continuous_id).continuousAt).eventually_ne (by norm_num)
      filter_upwards [h1] with v hv
      simp [rubi1228r2, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
      first | exact hv | (intro h; exact hv (by linarith)) | (rw [add_comm] at hv; exact hv) | (trace_state; sorry)
  · first
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1228r2, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩; simp [rubi1228r2, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1228r2, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; norm_num)
      | (trace_state; sorry)

theorem rubi133r6_counterexample_real : ¬ rubi133r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi133r6.conditions rubi133r6.body rubi133r6.result rubi133r6.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have im4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" then 1 else 0) (1 : ℝ) ?_ ?_ ?_
  · simp [rubi133r6, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
  · exact by
      have h1 : ∀ᶠ v in 𝓝 (1 : ℝ), (1 : ℝ) + v ≠ 0 := ((continuous_const.add continuous_id).continuousAt).eventually_ne (by norm_num)
      filter_upwards [h1] with v hv
      simp [rubi133r6, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
      first | exact hv | (intro h; exact hv (by linarith)) | (rw [add_comm] at hv; exact hv) | (trace_state; sorry)
  · first
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi133r6, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩; simp [rubi133r6, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi133r6, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; norm_num)
      | (trace_state; sorry)

theorem rubi1223r47_counterexample_real : ¬ rubi1223r47.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1223r47.conditions rubi1223r47.body rubi1223r47.result rubi1223r47.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have im4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" then -1 else if s = "a" ∨ s = "b" ∨ s = "d" then 1 else 0) (0 : ℝ) ?_ ?_ ?_
  · simp [rubi1223r47, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
  · filter_upwards [Ioo_mem_nhds (by norm_num : (-1/2 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1/2)] with v hv
    obtain ⟨h1, h2⟩ := hv
    have hq : 0 < 1 + -v ^ 2 := by nlinarith
    have hq2 : 0 < 1 + v ^ 2 := by positivity
    simp [rubi1223r47, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
    have habs : |v| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have s1 : ¬√(1 + -v ^ 2) = 0 := (Real.sqrt_pos.2 hq).ne'
    have s2 : ¬√(1 + v ^ 2) = 0 := (Real.sqrt_pos.2 hq2).ne'
    simp [habs, hq2.le, s1, s2]
  · first
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1223r47, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩; simp [rubi1223r47, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1223r47, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; norm_num)
      | (trace_state; sorry)

theorem rubi1223r48_counterexample_real : ¬ rubi1223r48.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1223r48.conditions rubi1223r48.body rubi1223r48.result rubi1223r48.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have im4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "d" ∨ s = "e" then 1 else 0) (0 : ℝ) ?_ ?_ ?_
  · simp [rubi1223r48, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
  · exact Eventually.of_forall fun w => by
      simp [rubi1223r48, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
      exact ⟨by positivity, (Real.sqrt_pos.2 (by positivity)).ne'⟩
  · first
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1223r48, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩; simp [rubi1223r48, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1223r48, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; norm_num)
      | (trace_state; sorry)

theorem rubi1223r51_counterexample_real : ¬ rubi1223r51.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1223r51.conditions rubi1223r51.body rubi1223r51.result rubi1223r51.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have im4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" then -1 else if s = "a" ∨ s = "b" ∨ s = "d" then 1 else 0) (0 : ℝ) ?_ ?_ ?_
  · simp [rubi1223r51, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
  · filter_upwards [Ioo_mem_nhds (by norm_num : (-1/2 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1/2)] with v hv
    obtain ⟨h1, h2⟩ := hv
    have hq : 0 < 1 + -v ^ 2 := by nlinarith
    have hq2 : 0 < 1 + v ^ 2 := by positivity
    simp [rubi1223r51, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
    have habs : |v| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have s1 : ¬√(1 + -v ^ 2) = 0 := (Real.sqrt_pos.2 hq).ne'
    have s2 : ¬√(1 + v ^ 2) = 0 := (Real.sqrt_pos.2 hq2).ne'
    simp [habs, hq2.le, s1, s2]
  · first
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1223r51, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩; simp [rubi1223r51, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1223r51, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; norm_num)
      | (trace_state; sorry)

theorem rubi1223r52_counterexample_real : ¬ rubi1223r52.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1223r52.conditions rubi1223r52.body rubi1223r52.result rubi1223r52.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have im4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "d" ∨ s = "e" then 1 else 0) (0 : ℝ) ?_ ?_ ?_
  · simp [rubi1223r52, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
  · exact Eventually.of_forall fun w => by
      simp [rubi1223r52, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
      exact ⟨by positivity, (Real.sqrt_pos.2 (by positivity)).ne'⟩
  · first
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1223r52, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩; simp [rubi1223r52, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1223r52, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; norm_num)
      | (trace_state; sorry)

theorem rubi1224r71_counterexample_real : ¬ rubi1224r71.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r71.conditions rubi1224r71.body rubi1224r71.result rubi1224r71.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have im4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "b" ∨ s = "d" then 1 else 0) (0 : ℝ) ?_ ?_ ?_
  · simp [rubi1224r71, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
  · exact Eventually.of_forall fun w => by
      simp [rubi1224r71, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
      exact ⟨by positivity, (Real.sqrt_pos.2 (by positivity)).ne'⟩
  · first
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1224r71, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩; simp [rubi1224r71, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1224r71, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; norm_num)
      | (trace_state; sorry)

theorem rubi1224r72_counterexample_real : ¬ rubi1224r72.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r72.conditions rubi1224r72.body rubi1224r72.result rubi1224r72.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have im2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have im4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "d" ∨ s = "a" then 1 else 0) (0 : ℝ) ?_ ?_ ?_
  · simp [rubi1224r72, Cond.Holds, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
  · exact Eventually.of_forall fun w => by simp [rubi1224r72, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]
  · first
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1224r72, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩; simp [rubi1224r72, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; done)
      | (refine ⟨_, List.mem_cons_self, ?_⟩; simp [rubi1224r72, Defined, eval, Interp.real, i0, i1, i2, i4, im1, im2, im4]; norm_num)
      | (trace_state; sorry)

theorem rubi312r12_counterexample_real : ¬ rubi312r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi312r12.conditions rubi312r12.body rubi312r12.result rubi312r12.integrals
  have i0 : intValue? (0 : ℝ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℝ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "d1" ∨ s = "d2" ∨ s = "q1" ∨ s = "m1" ∨ s = "c" then 1 else 0) (0 : ℝ) ?_ ?_
    (fun h w => w * (((rubi312r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d1" ∨ s = "d2" ∨ s = "q1" ∨ s = "m1" ∨ s = "c" then 1 else 0) "x" (0 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi312r12, Cond.Holds, Defined, eval, Interp.real, i0, i1, im1]
  · exact Eventually.of_forall fun w => by simp [rubi312r12, Defined, eval, Interp.real, i0, i1, im1]
  · simp only [rubi312r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    simp [List.lookup]
    exact hasDerivAt_mul_const _
  · intro h
    simp [rubi312r12, Defined, eval, Interp.real, i0, i1, im1, recEnv] at h

theorem rubi312r12_counterexample_complex : ¬ rubi312r12.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi312r12.conditions rubi312r12.body rubi312r12.result rubi312r12.integrals
  have i0 : intValue? (0 : ℂ) = some 0 := (intValue?_eq _ _).2 (by norm_num)
  have i1 : intValue? (1 : ℂ) = some 1 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "d1" ∨ s = "d2" ∨ s = "q1" ∨ s = "m1" ∨ s = "c" then 1 else 0) (0 : ℂ) ?_ ?_
    (fun h w => w * (((rubi312r12.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d1" ∨ s = "d2" ∨ s = "q1" ∨ s = "m1" ∨ s = "c" then 1 else 0) "x" (0 : ℂ)))).getD 0)) ?_ ?_
  · simp [rubi312r12, Cond.Holds, Defined, eval, Interp.complex, i0, i1, im1]
  · exact Eventually.of_forall fun w => by simp [rubi312r12, Defined, eval, Interp.complex, i0, i1, im1]
  · simp only [rubi312r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    simp [List.lookup]
    exact hasDerivAt_mul_const _
  · intro h
    simp [rubi312r12, Defined, eval, Interp.complex, i0, i1, im1, recEnv] at h

end OSR.IntegrationRec162
