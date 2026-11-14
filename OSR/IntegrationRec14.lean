import OSR.IntegrationRec13

/-!
# Integration (RUBI): rules with `EqQ` conditions, refuted

RUBI rules whose conditions include `EqQ`, stated with `relation1#eq`.
The rules of this module were selected by a numerical search for
counterexamples under the real definedness semantics of the fragment: an
assignment satisfying the conditions, a point near which the integrand is
defined, at which the result or a residual integrand is not.  The search only
proposes; each refutation below is a Lean theorem, stated per domain.  The
rule declarations are transcribed by a tool and checked by the Integration
repository's `scripts/v1_faithfulness.py`.  Variables that RUBI constrains
by numeric predicates (`IntegerQ`, `GtQ`, …) but does not list in `FreeQ` are
declared independent of `x`, with an `independence:` finding.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec14

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

def rubi1223r7 : CRule where
  id := "integration.rubi_1_2_2_3_r7"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.var "q"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "q", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 3560
  description := "RUBI 1.2.2.3 #7"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:7" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#7"

def rubi1223r8 : CRule where
  id := "integration.rubi_1_2_2_3_r8"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.var "q"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "q", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 3570
  description := "RUBI 1.2.2.3 #8"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:8" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#8"

def rubi1224r11 : CRule where
  id := "integration.rubi_1_2_2_4_r11"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.var "p")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "q", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 3580
  description := "RUBI 1.2.2.4 #11"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:11" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#11"

def rubi1224r12 : CRule where
  id := "integration.rubi_1_2_2_4_r12"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.var "p")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "f", "q", "m", "q", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p")]
  priority := 3590
  description := "RUBI 1.2.2.4 #12"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:12" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#12"

def rubi131r4 : CRule where
  id := "integration.rubi_1_3_1_r4"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.1 P(x)^p:4"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "d") (.pow (.var "x") (.int 3)))) (.var "p"))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 3) (.app2 .mul (.int 3) (.var "p"))) (.pow (.var "a") (.app2 .mul (.int 2) (.var "p")))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.int 3) (.var "a")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "x"))) (.var "p")) (.pow (.app2 .add (.app2 .mul (.int 3) (.var "a")) (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "x"))) (.app2 .mul (.int 2) (.var "p")))))]
  independent := ["a", "b", "d", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.int 4) (.pow (.var "b") (.int 3))) (.app2 .mul (.app2 .mul (.int 27) (.pow (.var "a") (.int 2))) (.var "d"))) (.int 0),
    .int (.var "p")]
  priority := 3600
  description := "RUBI 1.3.1 #4"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.1 P(x)^p:4" "1 Algebraic functions/1.3 Miscellaneous/1.3.1 P(x)^p.m#4"

def rubi132r1 : CRule where
  id := "integration.rubi_1_3_2_r1"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.2 P(x) Q(x)^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "d") (.pow (.var "x") (.int 3)))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 3) (.app2 .mul (.int 3) (.var "p"))) (.pow (.var "a") (.app2 .mul (.int 2) (.var "p")))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .mul (.int 3) (.var "a")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "x"))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.int 3) (.var "a")) (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "x"))) (.app2 .mul (.int 2) (.var "p")))))]
  independent := ["a", "b", "d", "e", "f", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.int 4) (.pow (.var "b") (.int 3))) (.app2 .mul (.app2 .mul (.int 27) (.pow (.var "a") (.int 2))) (.var "d"))) (.int 0),
    .int (.var "p")]
  priority := 3610
  description := "RUBI 1.3.2 #1"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.2 P(x) Q(x)^p:1" "1 Algebraic functions/1.3 Miscellaneous/1.3.2 P(x) Q(x)^p.m#1"

def rubi23r32 : CRule where
  id := "integration.rubi_2_3_r32"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:32"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.var "e") (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))))
  result := (.app2 .mul (.pow (.var "F") (.app2 .add (.var "e") (.app2 .mul (.app2 .mul (.var "f") (.var "b")) (.pow (.var "d") (.int (-1)))))) (.var "I1"))
  integrals := [("I1", (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "h", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 3620
  description := "RUBI 2.3 #32"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:32" "2 Exponentials/2.3 Miscellaneous exponentials.m#32"

def rubi23r33 : CRule where
  id := "integration.rubi_2_3_r33"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.var "e") (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.var "b") (.var "f"))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "h", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "h"))) (.int 0)]
  priority := 3630
  description := "RUBI 2.3 #33"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:33" "2 Exponentials/2.3 Miscellaneous exponentials.m#33"

def rubi23r39 : CRule where
  id := "integration.rubi_2_3_r39"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:39"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.var "F") (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .mul (.app2 .mul (.var "e") (.pow (.var "F") (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app1 .ln (.var "F"))) (.int (-1))))
  independent := ["F", "a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 3640
  description := "RUBI 2.3 #39"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:39" "2 Exponentials/2.3 Miscellaneous exponentials.m#39"

def rubi23r40 : CRule where
  id := "integration.rubi_2_3_r40"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:40"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.var "F") (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app1 .ln (.var "F"))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.var "e") (.int 2))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app1 .ln (.var "F"))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.var "F") (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["F", "a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 3650
  description := "RUBI 2.3 #40"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:40" "2 Exponentials/2.3 Miscellaneous exponentials.m#40"

def rubi23r42 : CRule where
  id := "integration.rubi_2_3_r42"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:42"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.var "F") (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.app1 .ln (.var "F"))) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.pow (.var "F") (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["F", "a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 3660
  description := "RUBI 2.3 #42"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:42" "2 Exponentials/2.3 Miscellaneous exponentials.m#42"

def rubi23r54 : CRule where
  id := "integration.rubi_2_3_r54"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:54"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "G") (.app2 .mul (.var "h") (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))))) (.pow (.var "H") (.app2 .mul (.var "t") (.app2 .add (.var "r") (.app2 .mul (.var "s") (.var "x")))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "F") (.app2 .mul (.var "e") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))) (.var "p")))
  result := (.app2 .mul (.pow (.var "G") (.app2 .mul (.app2 .add (.var "f") (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "g")) (.pow (.var "d") (.int (-1))))) (.var "h"))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "H") (.app2 .mul (.var "t") (.app2 .add (.var "r") (.app2 .mul (.var "s") (.var "x"))))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "F") (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))) (.var "p"))))]
  independent := ["F", "G", "H", "a", "b", "c", "d", "e", "f", "g", "h", "r", "s", "t", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.var "p")) (.app1 .ln (.var "F"))) (.app2 .mul (.app2 .mul (.var "g") (.var "h")) (.app1 .ln (.var "G")))) (.int 0),
    .int (.var "p")]
  priority := 3680
  description := "RUBI 2.3 #54"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:54" "2 Exponentials/2.3 Miscellaneous exponentials.m#54"

def rubi23r76 : CRule where
  id := "integration.rubi_2_3_r76"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:76"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.int 2)))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.var "f")) (.app1 .ln (.var "F"))))) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.var "f")) (.var "n")) (.app1 .ln (.var "F"))))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.var "f")) (.var "n")) (.app1 .ln (.var "F"))))) (.pow (.var "F") (.app2 .add (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "f")) (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))) (.int 2)))))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "h", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "e") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "h"))) (.int 0)]
  priority := 3690
  description := "RUBI 2.3 #76"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:76" "2 Exponentials/2.3 Miscellaneous exponentials.m#76"

def rubi312r3 : CRule where
  id := "integration.rubi_3_1_2_r3"; legacyId := some "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:3"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.ne (.var "m") (.int (-1)),
    .eq (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n"))) (.int 0)]
  priority := 3700
  description := "RUBI 3.1.2 #3"
  provenance := migrated "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:3" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#3"

def rubi313r1 : CRule where
  id := "integration.rubi_3_1_3_r1"; legacyId := some "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.pow (.var "d") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1))))]
  independent := ["a", "b", "c", "d", "e", "n", "q", "r"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "r") (.app2 .add (.var "q") (.int 1))) (.int 1)) (.int 0)]
  priority := 3710
  description := "RUBI 3.1.3 #1"
  provenance := migrated "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:1" "3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p.m#1"

def rubi314r10 : CRule where
  id := "integration.rubi_3_1_4_r10"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.var "q")) (.int 2)) (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0),
    .gt (.int (-1)) (.var "q")]
  priority := 3720
  description := "RUBI 3.1.4 #10"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:10" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#10"

def rubi314r2 : CRule where
  id := "integration.rubi_3_1_4_r2"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q", "r"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "r") (.app2 .add (.var "q") (.int 1)))) (.int 1)) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 3730
  description := "RUBI 3.1.4 #2"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:2" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#2"

def rubi314r22 : CRule where
  id := "integration.rubi_3_1_4_r22"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:22"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.app2 .add (.var "q") (.int 1)) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.app2 .add (.var "q") (.int 1)) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "q", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "g"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.var "q")) (.int 2)) (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0),
    .gt (.int (-1)) (.var "q")]
  priority := 3740
  description := "RUBI 3.1.4 #22"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:22" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#22"

def rubi315r3 : CRule where
  id := "integration.rubi_3_1_5_r3"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q", "r"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "r") (.app2 .add (.var "q") (.int 1)))) (.int 1)) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 3750
  description := "RUBI 3.1.5 #3"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:3" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#3"

def rubi321r9 : CRule where
  id := "integration.rubi_3_2_1_r9"; legacyId := some "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .ln (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n"))))))) (.pow (.var "g") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "B") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "g") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "A", "B", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "d") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "g"))) (.int 0)]
  priority := 3760
  description := "RUBI 3.2.1 #9"
  provenance := migrated "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:9" "3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.m#9"

def rubi322r1 : CRule where
  id := "integration.rubi_3_2_2_r1"; legacyId := some "rubi:3 Logarithms/3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app2 .add (.var "h") (.app2 .mul (.var "i") (.var "x")))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "h") (.app2 .mul (.var "i") (.var "x")))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n"))))))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "i") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "m") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "n"))) (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "A", "B", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "g"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "d") (.var "h")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "i"))) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int (-2))]
  priority := 3770
  description := "RUBI 3.2.2 #1"
  provenance := migrated "rubi:3 Logarithms/3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p:1" "3 Logarithms/3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p.m#1"

def rubi322r16 : CRule where
  id := "integration.rubi_3_2_2_r16"; legacyId := some "rubi:3 Logarithms/3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .mul (.var "h") (.pow (.var "x") (.int 2)))) (.var "m")) (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.var "h") (.var "m")) (.pow (.app2 .mul (.pow (.var "b") (.var "m")) (.pow (.var "d") (.var "m"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "A", "B", "n", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "h"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "h")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))))) (.int 0),
    .int (.var "m")]
  priority := 3780
  description := "RUBI 3.2.2 #16"
  provenance := migrated "rubi:3 Logarithms/3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p:16" "3 Logarithms/3.2.2 (f+g x)^m (h+i x)^q (A+B log(e ((a+b x) over (c+d x))^n))^p.m#16"

def rubi323r5 : CRule where
  id := "integration.rubi_3_2_3_r5"; legacyId := some "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.int 2)) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.var "I1") (.app2 .mul (.app2 .add (.app2 .add (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r")))) (.app2 .mul (.int (-1)) (.app1 .ln (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "p") (.var "r")))))) (.app2 .mul (.int (-1)) (.app1 .ln (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .mul (.var "q") (.var "r")))))) (.app2 .add (.app2 .mul (.int 2) (.var "I2")) (.var "I3"))))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app1 .ln (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "p") (.var "r")))) (.app1 .ln (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .mul (.var "q") (.var "r"))))) (.int 2)) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .ln (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .mul (.var "q") (.var "r")))) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int (-1))))),
    ("I3", (.app2 .mul (.app2 .add (.app2 .add (.app1 .ln (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "p") (.var "r")))) (.app2 .mul (.int (-1)) (.app1 .ln (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .mul (.var "q") (.var "r")))))) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r"))))) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "p", "q", "r"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h"))) (.int 0)]
  priority := 3790
  description := "RUBI 3.2.3 #5"
  provenance := migrated "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:5" "3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m#5"

def rubi323r8 : CRule where
  id := "integration.rubi_3_2_3_r8"; legacyId := some "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "s") (.app2 .mul (.var "t") (.app1 .ln (.app2 .mul (.var "i") (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "n")))))) (.var "m")) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r"))))) (.pow (.app2 .add (.var "j") (.app2 .mul (.var "k") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "s") (.app2 .mul (.var "t") (.app1 .ln (.app2 .mul (.var "i") (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "n")))))) (.app2 .add (.var "m") (.int 1))) (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "q"))) (.var "r"))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "k") (.var "n")) (.var "t")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "p")) (.var "r")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "k") (.var "n")) (.var "t")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "q")) (.var "r")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "k") (.var "n")) (.var "t")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "s") (.app2 .mul (.var "t") (.app1 .ln (.app2 .mul (.var "i") (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "n")))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "s") (.app2 .mul (.var "t") (.app1 .ln (.app2 .mul (.var "i") (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "n")))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "s", "t", "m", "n", "p", "q", "r"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "h") (.var "j")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.var "k"))) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 3800
  description := "RUBI 3.2.3 #8"
  provenance := migrated "rubi:3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s:8" "3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m#8"

def rubi33r22 : CRule where
  id := "integration.rubi_3_3_r22"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:22"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.var "r")))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.var "g") (.var "r")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.app2 .mul (.var "g") (.var "r")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "q", "r", "p"]
  conditions := [.eq (.var "m") (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "q") (.int (-1)),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 3810
  description := "RUBI 3.3 #22"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:22" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#22"

def rubi33r40 : CRule where
  id := "integration.rubi_3_3_r40"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:40"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "i") (.app2 .mul (.var "j") (.var "x"))) (.var "m"))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.var "x")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "i") (.app2 .mul (.var "j") (.var "x"))) (.var "m"))))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "g")) (.var "m")) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "j")) (.var "n")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app1 .ln (.var "x")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n"))))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.var "x")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "i") (.app2 .mul (.var "j") (.var "x"))) (.var "m"))))))) (.pow (.app2 .add (.var "i") (.app2 .mul (.var "j") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "e") (.var "i")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "j"))) (.int 0)]
  priority := 3820
  description := "RUBI 3.3 #40"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:40" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#40"

def rubi35r14 : CRule where
  id := "integration.rubi_3_5_r14"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "r")) (.pow (.app2 .mul (.var "x") (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q"))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app1 .ln (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q"))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.int (-1)))))]
  independent := ["a", "b", "c", "m", "n", "q", "r"]
  conditions := [.eq (.var "r") (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))]
  priority := 3830
  description := "RUBI 3.5 #14"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:14" "3 Logarithms/3.5 Miscellaneous logarithms.m#14"

def rubi35r16 : CRule where
  id := "integration.rubi_3_5_r16"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "r")) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.var "p"))))]
  independent := ["a", "b", "c", "m", "n", "p", "q", "r"]
  conditions := [.eq (.var "r") (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1))]
  priority := 3840
  description := "RUBI 3.5 #16"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:16" "3 Logarithms/3.5 Miscellaneous logarithms.m#16"

def rubi35r17 : CRule where
  id := "integration.rubi_3_5_r17"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:17"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "e") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "r")))) (.pow (.app2 .mul (.var "x") (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q"))))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "m", "n", "q", "r"]
  conditions := [.eq (.var "r") (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.var "q"))) (.int 0)]
  priority := 3850
  description := "RUBI 3.5 #17"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:17" "3 Logarithms/3.5 Miscellaneous logarithms.m#17"

def rubi35r19 : CRule where
  id := "integration.rubi_3_5_r19"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "e") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "r")))) (.pow (.app2 .mul (.var "x") (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q"))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.var "q")))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "q", "r"]
  conditions := [.eq (.var "r") (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.var "q"))) (.int 0)]
  priority := 3860
  description := "RUBI 3.5 #19"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:19" "3 Logarithms/3.5 Miscellaneous logarithms.m#19"

def rubi35r20 : CRule where
  id := "integration.rubi_3_5_r20"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:20"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "e") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "r")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "m", "n", "p", "q", "r"]
  conditions := [.eq (.var "r") (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1)),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.var "q"))) (.int 0)]
  priority := 3870
  description := "RUBI 3.5 #20"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:20" "3 Logarithms/3.5 Miscellaneous logarithms.m#20"

def rubi35r21 : CRule where
  id := "integration.rubi_3_5_r21"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:21"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "e") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "r")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.var "q")))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p", "q", "r"]
  conditions := [.eq (.var "r") (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1)),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.var "q"))) (.int 0)]
  priority := 3880
  description := "RUBI 3.5 #21"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:21" "3 Logarithms/3.5 Miscellaneous logarithms.m#21"

def rubi35r22 : CRule where
  id := "integration.rubi_3_5_r22"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:22"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "d") (.pow (.var "x") (.var "m"))) (.app2 .mul (.app2 .mul (.var "e") (.pow (.var "x") (.var "m"))) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .mul (.var "f") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.pow (.app2 .mul (.var "x") (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.int 2))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.var "d") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q"))))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "e") (.var "n")) (.app2 .mul (.var "d") (.var "m"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "a") (.var "f")) (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))))) (.int 0)]
  priority := 3890
  description := "RUBI 3.5 #22"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:22" "3 Logarithms/3.5 Miscellaneous logarithms.m#22"

def rubi35r23 : CRule where
  id := "integration.rubi_3_5_r23"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.pow (.pow (.app2 .add (.app2 .mul (.var "a") (.var "x")) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.var "a") (.var "x")) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q"))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "n"))) (.pow (.var "a") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "x") (.app2 .add (.app2 .mul (.var "a") (.var "x")) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q"))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "n", "q"]
  conditions := [.eq (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.var "e") (.var "n")) (.var "q"))) (.int 0)]
  priority := 3900
  description := "RUBI 3.5 #23"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:23" "3 Logarithms/3.5 Miscellaneous logarithms.m#23"

def rubi4112r43 : CRule where
  id := "integration.rubi_4_1_12_r43"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:43"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "n") (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.var "n"))) (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))) (.pow (.var "p") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)) (.int 0),
    .gt (.var "p") (.int 1)]
  priority := 3910
  description := "RUBI 4.1.12 #43"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:43" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#43"

def rubi4112r44 : CRule where
  id := "integration.rubi_4_1_12_r44"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:44"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "n") (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "n")) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))) (.pow (.var "p") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)) (.int 0),
    .gt (.var "p") (.int 1)]
  priority := 3920
  description := "RUBI 4.1.12 #44"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:44" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#44"

def rubi4112r52 : CRule where
  id := "integration.rubi_4_1_12_r52"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:52"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.var "n"))) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "n")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.int 2)) (.pow (.app2 .add (.var "p") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .ne (.var "p") (.int (-2))]
  priority := 3940
  description := "RUBI 4.1.12 #52"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:52" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#52"

def rubi4112r81 : CRule where
  id := "integration.rubi_4_1_12_r81"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:81"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .mul (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1))]
  priority := 3950
  description := "RUBI 4.1.12 #81"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:81" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#81"

def rubi4112r82 : CRule where
  id := "integration.rubi_4_1_12_r82"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:82"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1))]
  priority := 3960
  description := "RUBI 4.1.12 #82"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:82" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#82"

def rubi4113r1 : CRule where
  id := "integration.rubi_4_1_13_r1"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:1"
  shape := .antiderivRec; x := "x"
  body := (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))
  result := (.var "I1")
  integrals := [("I1", (.app1 .sin (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))))]
  independent := ["a", "b", "c"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)]
  priority := 3970
  description := "RUBI 4.1.13 #1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:1" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#1"

def rubi4113r11 : CRule where
  id := "integration.rubi_4_1_13_r11"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:11"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1))))
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)]
  priority := 3980
  description := "RUBI 4.1.13 #11"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:11" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#11"

def rubi4113r12 : CRule where
  id := "integration.rubi_4_1_13_r12"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:12"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .mul (.app2 .mul (.var "e") (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1))))
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)]
  priority := 3990
  description := "RUBI 4.1.13 #12"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:12" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#12"

def rubi4113r13 : CRule where
  id := "integration.rubi_4_1_13_r13"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 4000
  description := "RUBI 4.1.13 #13"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:13" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#13"

def rubi4113r14 : CRule where
  id := "integration.rubi_4_1_13_r14"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 4010
  description := "RUBI 4.1.13 #14"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:14" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#14"

def rubi4113r15 : CRule where
  id := "integration.rubi_4_1_13_r15"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 4020
  description := "RUBI 4.1.13 #15"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:15" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#15"

def rubi4113r16 : CRule where
  id := "integration.rubi_4_1_13_r16"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 4030
  description := "RUBI 4.1.13 #16"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:16" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#16"

def rubi4113r2 : CRule where
  id := "integration.rubi_4_1_13_r2"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:2"
  shape := .antiderivRec; x := "x"
  body := (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))
  result := (.var "I1")
  integrals := [("I1", (.app1 .cos (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))))]
  independent := ["a", "b", "c"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0)]
  priority := 4040
  description := "RUBI 4.1.13 #2"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:2" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#2"

def rubi4312r3 : CRule where
  id := "integration.rubi_4_3_12_r3"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.12 (d+e x)^m tan(a+b x+c x^2)^n:3"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .tan (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app1 .ln (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1))))
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0)]
  priority := 4050
  description := "RUBI 4.3.12 #3"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.12 (d+e x)^m tan(a+b x+c x^2)^n:3" "4 Trig functions/4.3 Tangent/4.3.12 (d+e x)^m tan(a+b x+c x^2)^n.m#3"

def rubi477r5 : CRule where
  id := "integration.rubi_4_7_7_r5"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:5"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.int (-1)))))
  independent := ["F", "a", "b", "c", "d", "e", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.app2 .add (.var "n") (.int 2)) (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int 0),
    .ne (.var "n") (.int (-1)),
    .ne (.var "n") (.int (-2))]
  priority := 4060
  description := "RUBI 4.7.7 #5"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:5" "4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m#5"

def rubi477r6 : CRule where
  id := "integration.rubi_4_7_7_r6"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:6"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.int (-1)))))
  independent := ["F", "a", "b", "c", "d", "e", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.app2 .add (.var "n") (.int 2)) (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int 0),
    .ne (.var "n") (.int (-1)),
    .ne (.var "n") (.int (-2))]
  priority := 4070
  description := "RUBI 4.7.7 #6"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n:6" "4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m#6"

def rubi479r79 : CRule where
  id := "integration.rubi_4_7_9_r79"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:79"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.pow (.app2 .add (.app2 .mul (.var "c") (.app1 .cos (.app2 .mul (.var "a") (.var "x")))) (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app1 .sin (.app2 .mul (.var "a") (.var "x"))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app1 .cos (.app2 .mul (.var "a") (.var "x")))) (.app2 .add (.app2 .mul (.var "c") (.app1 .cos (.app2 .mul (.var "a") (.var "x")))) (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app1 .sin (.app2 .mul (.var "a") (.var "x")))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "d") (.int 2)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.pow (.app1 .cos (.app2 .mul (.var "a") (.var "x"))) (.int 2)) (.int (-1)))))]
  independent := ["a", "c", "d"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.int (-1)) (.var "d"))) (.int 0)]
  priority := 4100
  description := "RUBI 4.7.9 #79"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:79" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#79"

def rubi479r81 : CRule where
  id := "integration.rubi_4_7_9_r81"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:81"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app1 .cos (.app2 .mul (.var "a") (.var "x"))) (.int 2)) (.pow (.pow (.app2 .add (.app2 .mul (.var "c") (.app1 .cos (.app2 .mul (.var "a") (.var "x")))) (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app1 .sin (.app2 .mul (.var "a") (.var "x"))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.var "d") (.int 2)) (.var "x")) (.int (-1)))) (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .cos (.app2 .mul (.var "a") (.var "x")))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "x")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.app1 .sin (.app2 .mul (.var "a") (.var "x")))) (.app2 .mul (.var "c") (.app1 .cos (.app2 .mul (.var "a") (.var "x")))))) (.int (-1)))))
  independent := ["a", "c", "d"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.int (-1)) (.var "d"))) (.int 0)]
  priority := 4110
  description := "RUBI 4.7.9 #81"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:81" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#81"


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
end


private theorem rsin1 : Real.sin 1 ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [Real.pi_gt_three])).ne'

private theorem csin1 : Complex.sin 1 ≠ 0 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sin]; exact_mod_cast rsin1

theorem rubi1223r7_counterexample_real : ¬ rubi1223r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1223r7.conditions rubi1223r7.body rubi1223r7.result rubi1223r7.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi1223r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1223r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1223r7.integrals[0]!, by simp [rubi1223r7], ?_⟩
  intro h
  simp [rubi1223r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1223r7_counterexample_complex : ¬ rubi1223r7.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1223r7.conditions rubi1223r7.body rubi1223r7.result rubi1223r7.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℂ) (by simp [rubi1223r7, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1223r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1223r7.integrals[0]!, by simp [rubi1223r7], ?_⟩
  intro h
  simp [rubi1223r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1223r8_counterexample_real : ¬ rubi1223r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1223r8.conditions rubi1223r8.body rubi1223r8.result rubi1223r8.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi1223r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1223r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1223r8.integrals[0]!, by simp [rubi1223r8], ?_⟩
  intro h
  simp [rubi1223r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1223r8_counterexample_complex : ¬ rubi1223r8.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1223r8.conditions rubi1223r8.body rubi1223r8.result rubi1223r8.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℂ) (by simp [rubi1223r8, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1223r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1223r8.integrals[0]!, by simp [rubi1223r8], ?_⟩
  intro h
  simp [rubi1223r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1224r11_counterexample_real : ¬ rubi1224r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r11.conditions rubi1224r11.body rubi1224r11.result rubi1224r11.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi1224r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1224r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1224r11.integrals[0]!, by simp [rubi1224r11], ?_⟩
  intro h
  simp [rubi1224r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1224r11_counterexample_complex : ¬ rubi1224r11.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1224r11.conditions rubi1224r11.body rubi1224r11.result rubi1224r11.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℂ) (by simp [rubi1224r11, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1224r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1224r11.integrals[0]!, by simp [rubi1224r11], ?_⟩
  intro h
  simp [rubi1224r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1224r12_counterexample_real : ¬ rubi1224r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r12.conditions rubi1224r12.body rubi1224r12.result rubi1224r12.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi1224r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1224r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1224r12.integrals[0]!, by simp [rubi1224r12], ?_⟩
  intro h
  simp [rubi1224r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi1224r12_counterexample_complex : ¬ rubi1224r12.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi1224r12.conditions rubi1224r12.body rubi1224r12.result rubi1224r12.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℂ) (by simp [rubi1224r12, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi1224r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi1224r12.integrals[0]!, by simp [rubi1224r12], ?_⟩
  intro h
  simp [rubi1224r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi131r4_counterexample_real : ¬ rubi131r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi131r4.conditions rubi131r4.body rubi131r4.result rubi131r4.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi131r4, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi131r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi131r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi131r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi131r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi131r4_counterexample_complex : ¬ rubi131r4.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi131r4.conditions rubi131r4.body rubi131r4.result rubi131r4.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi131r4, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi131r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi131r4.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi131r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi131r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi132r1_counterexample_real : ¬ rubi132r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi132r1.conditions rubi132r1.body rubi132r1.result rubi132r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi132r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi132r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi132r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi132r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi132r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi132r1_counterexample_complex : ¬ rubi132r1.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi132r1.conditions rubi132r1.body rubi132r1.result rubi132r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi132r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi132r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi132r1.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi132r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi132r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi23r32_counterexample_real : ¬ rubi23r32.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi23r32.conditions rubi23r32.body rubi23r32.result rubi23r32.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi23r32, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r32, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi23r32.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi23r32, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi23r32, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi23r32_counterexample_complex : ¬ rubi23r32.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi23r32.conditions rubi23r32.body rubi23r32.result rubi23r32.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi23r32, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r32, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi23r32.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi23r32, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi23r32, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi23r33_counterexample_real : ¬ rubi23r33.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi23r33.conditions rubi23r33.body rubi23r33.result rubi23r33.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "F" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi23r33, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi23r33.integrals[0]!, by simp [rubi23r33], ?_⟩
  intro h
  simp [rubi23r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi23r33_counterexample_complex : ¬ rubi23r33.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi23r33.conditions rubi23r33.body rubi23r33.result rubi23r33.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "F" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi23r33, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r33, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi23r33.integrals[0]!, by simp [rubi23r33], ?_⟩
  intro h
  simp [rubi23r33, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi23r39_counterexample_real : ¬ rubi23r39.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi23r39.conditions rubi23r39.body rubi23r39.result
  refine not_antiderivHoldsUnder (fun s => if s = "a" ∨ s = "d" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi23r39, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r39, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi23r39, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi23r39_counterexample_complex : ¬ rubi23r39.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi23r39.conditions rubi23r39.body rubi23r39.result
  refine not_antiderivHoldsUnder (fun s => if s = "a" ∨ s = "d" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi23r39, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r39, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi23r39, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi23r40_counterexample_real : ¬ rubi23r40.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi23r40.conditions rubi23r40.body rubi23r40.result rubi23r40.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi23r40, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r40, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi23r40.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi23r40, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi23r40, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi23r40_counterexample_complex : ¬ rubi23r40.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi23r40.conditions rubi23r40.body rubi23r40.result rubi23r40.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi23r40, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r40, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi23r40.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi23r40, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi23r40, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi23r42_counterexample_real : ¬ rubi23r42.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi23r42.conditions rubi23r42.body rubi23r42.result rubi23r42.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "F" ∨ s = "a" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi23r42, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r42, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi23r42.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "F" ∨ s = "a" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi23r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi23r42, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi23r42_counterexample_complex : ¬ rubi23r42.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi23r42.conditions rubi23r42.body rubi23r42.result rubi23r42.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "F" ∨ s = "a" ∨ s = "d" then 1 else 0) (1 : ℂ) (by simp [rubi23r42, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r42, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi23r42.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -3 else if s = "F" ∨ s = "a" ∨ s = "d" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi23r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi23r42, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi23r54_counterexample_real : ¬ rubi23r54.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi23r54.conditions rubi23r54.body rubi23r54.result rubi23r54.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "F" ∨ s = "G" ∨ s = "H" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "h" ∨ s = "p" ∨ s = "r" ∨ s = "t" then 1 else 0) (1 : ℝ) (by simp [rubi23r54, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r54, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi23r54.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "F" ∨ s = "G" ∨ s = "H" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "h" ∨ s = "p" ∨ s = "r" ∨ s = "t" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi23r54, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi23r54, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi23r54_counterexample_complex : ¬ rubi23r54.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi23r54.conditions rubi23r54.body rubi23r54.result rubi23r54.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "F" ∨ s = "G" ∨ s = "H" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "h" ∨ s = "p" ∨ s = "r" ∨ s = "t" then 1 else 0) (1 : ℂ) (by simp [rubi23r54, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r54, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi23r54.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "F" ∨ s = "G" ∨ s = "H" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "h" ∨ s = "p" ∨ s = "r" ∨ s = "t" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi23r54, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi23r54, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi23r76_counterexample_real : ¬ rubi23r76.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi23r76.conditions rubi23r76.body rubi23r76.result rubi23r76.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi23r76, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r76, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi23r76.integrals[0]!, by simp [rubi23r76], ?_⟩
  intro h
  simp [rubi23r76, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi23r76_counterexample_complex : ¬ rubi23r76.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi23r76.conditions rubi23r76.body rubi23r76.result rubi23r76.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi23r76, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi23r76, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi23r76.integrals[0]!, by simp [rubi23r76], ?_⟩
  intro h
  simp [rubi23r76, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi312r3_counterexample_real : ¬ rubi312r3.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi312r3.conditions rubi312r3.body rubi312r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "c" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi312r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi312r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi312r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi312r3_counterexample_complex : ¬ rubi312r3.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi312r3.conditions rubi312r3.body rubi312r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "c" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi312r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi312r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi312r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi313r1_counterexample_real : ¬ rubi313r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi313r1.conditions rubi313r1.body rubi313r1.result rubi313r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -2 else if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "r" then 1 else 0) (1 : ℝ) (by simp [rubi313r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi313r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi313r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -2 else if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "r" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi313r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi313r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi313r1_counterexample_complex : ¬ rubi313r1.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi313r1.conditions rubi313r1.body rubi313r1.result rubi313r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -2 else if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "r" then 1 else 0) (1 : ℂ) (by simp [rubi313r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi313r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi313r1.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "q" then -2 else if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "r" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi313r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi313r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi314r10_counterexample_real : ¬ rubi314r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi314r10.conditions rubi314r10.body rubi314r10.result rubi314r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi314r10, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi314r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi314r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -3 else if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi314r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi314r10_counterexample_complex : ¬ rubi314r10.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi314r10.conditions rubi314r10.body rubi314r10.result rubi314r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi314r10, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi314r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi314r10.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "q" then -3 else if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi314r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi314r2_counterexample_real : ¬ rubi314r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi314r2.conditions rubi314r2.body rubi314r2.result rubi314r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "r" then 1 else 0) (1 : ℝ) (by simp [rubi314r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi314r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi314r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -3 else if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "r" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi314r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi314r2_counterexample_complex : ¬ rubi314r2.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi314r2.conditions rubi314r2.body rubi314r2.result rubi314r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "r" then 1 else 0) (1 : ℂ) (by simp [rubi314r2, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi314r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi314r2.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "q" then -3 else if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "r" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi314r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi314r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi314r22_counterexample_real : ¬ rubi314r22.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi314r22.conditions rubi314r22.body rubi314r22.result rubi314r22.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "q" then -3 else if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (0 : ℝ) (by simp [rubi314r22, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi314r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi314r22.integrals[0]!, by simp [rubi314r22], ?_⟩
  intro h
  simp [rubi314r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi314r22_counterexample_complex : ¬ rubi314r22.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi314r22.conditions rubi314r22.body rubi314r22.result rubi314r22.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "q" then -3 else if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" then 1 else 0) (0 : ℂ) (by simp [rubi314r22, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi314r22, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi314r22.integrals[0]!, by simp [rubi314r22], ?_⟩
  intro h
  simp [rubi314r22, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi315r3_counterexample_real : ¬ rubi315r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi315r3.conditions rubi315r3.body rubi315r3.result rubi315r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "r" then 1 else 0) (1 : ℝ) (by simp [rubi315r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi315r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi315r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -3 else if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "r" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi315r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi315r3_counterexample_complex : ¬ rubi315r3.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi315r3.conditions rubi315r3.body rubi315r3.result rubi315r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "r" then 1 else 0) (1 : ℂ) (by simp [rubi315r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi315r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi315r3.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "q" then -3 else if s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "r" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi315r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi315r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi321r9_counterexample_real : ¬ rubi321r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi321r9.conditions rubi321r9.body rubi321r9.result rubi321r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) (1 : ℝ) (by simp [rubi321r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi321r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi321r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi321r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi321r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi321r9_counterexample_complex : ¬ rubi321r9.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi321r9.conditions rubi321r9.body rubi321r9.result rubi321r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) (1 : ℂ) (by simp [rubi321r9, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi321r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi321r9.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi321r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi321r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi322r1_counterexample_real : ¬ rubi322r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi322r1.conditions rubi322r1.body rubi322r1.result rubi322r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi322r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi322r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi322r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi322r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi322r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi322r1_counterexample_complex : ¬ rubi322r1.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi322r1.conditions rubi322r1.body rubi322r1.result rubi322r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi322r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi322r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi322r1.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "m" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi322r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi322r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi322r16_counterexample_real : ¬ rubi322r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi322r16.conditions rubi322r16.body rubi322r16.result rubi322r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi322r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi322r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi322r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi322r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi322r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi322r16_counterexample_complex : ¬ rubi322r16.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi322r16.conditions rubi322r16.body rubi322r16.result rubi322r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi322r16, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi322r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi322r16.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "A" ∨ s = "B" ∨ s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi322r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi322r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi323r5_counterexample_real : ¬ rubi323r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi323r5.conditions rubi323r5.body rubi323r5.result rubi323r5.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "p" ∨ s = "r" then -1 else if s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi323r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi323r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi323r5.integrals[0]!, by simp [rubi323r5], ?_⟩
  intro h
  simp [rubi323r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi323r8_counterexample_real : ¬ rubi323r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi323r8.conditions rubi323r8.body rubi323r8.result rubi323r8.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" then -3 else if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "i" ∨ s = "j" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "s" ∨ s = "t" then 1 else 0) (1 : ℝ) (by simp [rubi323r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi323r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi323r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then -3 else if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "i" ∨ s = "j" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "s" ∨ s = "t" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi323r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi323r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi323r8_counterexample_complex : ¬ rubi323r8.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi323r8.conditions rubi323r8.body rubi323r8.result rubi323r8.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" then -3 else if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "i" ∨ s = "j" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "s" ∨ s = "t" then 1 else 0) (1 : ℂ) (by simp [rubi323r8, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi323r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi323r8.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" then -3 else if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "i" ∨ s = "j" ∨ s = "m" ∨ s = "n" ∨ s = "p" ∨ s = "q" ∨ s = "s" ∨ s = "t" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi323r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi323r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi33r22_counterexample_real : ¬ rubi33r22.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi33r22.conditions rubi33r22.body rubi33r22.result rubi33r22.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else if s = "r" then 2 else 0) (-1 : ℝ) (by simp [rubi33r22, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi33r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi33r22.integrals[0]!, by simp [rubi33r22], ?_⟩
  intro h
  simp [rubi33r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi33r22_counterexample_complex : ¬ rubi33r22.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi33r22.conditions rubi33r22.body rubi33r22.result rubi33r22.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "g" ∨ s = "m" ∨ s = "p" ∨ s = "q" then 1 else if s = "r" then 2 else 0) (-1 : ℂ) (by simp [rubi33r22, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi33r22, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi33r22.integrals[0]!, by simp [rubi33r22], ?_⟩
  intro h
  simp [rubi33r22, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi33r40_counterexample_real : ¬ rubi33r40.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi33r40.conditions rubi33r40.body rubi33r40.result rubi33r40.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "h" ∨ s = "i" ∨ s = "m" ∨ s = "n" then 1 else 0) (-1 : ℝ) (by simp [rubi33r40, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (-1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi33r40, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi33r40.integrals[0]!, by simp [rubi33r40], ?_⟩
  intro h
  simp [rubi33r40, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi35r14_counterexample_real : ¬ rubi35r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi35r14.conditions rubi35r14.body rubi35r14.result rubi35r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "r" then 2 else if s = "q" then 3 else 0) (1 : ℝ) (by simp [rubi35r14, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi35r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi35r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "r" then 2 else if s = "q" then 3 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi35r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi35r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi35r16_counterexample_real : ¬ rubi35r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi35r16.conditions rubi35r16.body rubi35r16.result rubi35r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "m" ∨ s = "p" ∨ s = "r" then 1 else if s = "q" then 2 else 0) (1 : ℝ) (by simp [rubi35r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi35r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi35r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "m" ∨ s = "p" ∨ s = "r" then 1 else if s = "q" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi35r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi35r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi35r16_counterexample_complex : ¬ rubi35r16.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi35r16.conditions rubi35r16.body rubi35r16.result rubi35r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "m" ∨ s = "p" ∨ s = "r" then 1 else if s = "q" then 2 else 0) (1 : ℂ) (by simp [rubi35r16, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi35r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi35r16.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" ∨ s = "m" ∨ s = "p" ∨ s = "r" then 1 else if s = "q" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi35r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi35r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi35r17_counterexample_real : ¬ rubi35r17.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi35r17.conditions rubi35r17.body rubi35r17.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "c" ∨ s = "e" ∨ s = "m" ∨ s = "r" then 2 else if s = "q" then 3 else 0) (1 : ℝ) (by simp [rubi35r17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi35r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi35r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi35r19_counterexample_real : ¬ rubi35r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi35r19.conditions rubi35r19.body rubi35r19.result rubi35r19.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "m" ∨ s = "r" then 1 else if s = "q" then 2 else 0) (1 : ℝ) (by simp [rubi35r19, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi35r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi35r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "m" ∨ s = "r" then 1 else if s = "q" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi35r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi35r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi35r19_counterexample_complex : ¬ rubi35r19.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi35r19.conditions rubi35r19.body rubi35r19.result rubi35r19.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "m" ∨ s = "r" then 1 else if s = "q" then 2 else 0) (1 : ℂ) (by simp [rubi35r19, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi35r19, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi35r19.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "m" ∨ s = "r" then 1 else if s = "q" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi35r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi35r19, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi35r20_counterexample_real : ¬ rubi35r20.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi35r20.conditions rubi35r20.body rubi35r20.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "p" ∨ s = "r" then 1 else if s = "q" then 2 else 0) (1 : ℝ) (by simp [rubi35r20, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi35r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi35r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi35r20_counterexample_complex : ¬ rubi35r20.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi35r20.conditions rubi35r20.body rubi35r20.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "m" ∨ s = "p" ∨ s = "r" then 1 else if s = "q" then 2 else 0) (1 : ℂ) (by simp [rubi35r20, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi35r20, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi35r20, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi35r21_counterexample_real : ¬ rubi35r21.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi35r21.conditions rubi35r21.body rubi35r21.result rubi35r21.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "m" ∨ s = "p" ∨ s = "r" then 1 else if s = "q" then 2 else 0) (1 : ℝ) (by simp [rubi35r21, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi35r21, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi35r21.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "m" ∨ s = "p" ∨ s = "r" then 1 else if s = "q" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi35r21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi35r21, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi35r21_counterexample_complex : ¬ rubi35r21.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi35r21.conditions rubi35r21.body rubi35r21.result rubi35r21.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "m" ∨ s = "p" ∨ s = "r" then 1 else if s = "q" then 2 else 0) (1 : ℂ) (by simp [rubi35r21, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi35r21, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi35r21.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "c" ∨ s = "e" ∨ s = "m" ∨ s = "p" ∨ s = "r" then 1 else if s = "q" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi35r21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi35r21, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi35r22_counterexample_real : ¬ rubi35r22.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi35r22.conditions rubi35r22.body rubi35r22.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "q" then 1 else if s = "c" then 2 else 0) (1 : ℝ) (by simp [rubi35r22, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi35r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, hw] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi35r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi35r23_counterexample_real : ¬ rubi35r23.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi35r23.conditions rubi35r23.body rubi35r23.result rubi35r23.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then 1 else if s = "c" then 2 else 0) (1 : ℝ) (by simp [rubi35r23, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi35r23, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi35r23.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" ∨ s = "q" then 1 else if s = "c" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi35r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi35r23, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4112r43_counterexample_real : ¬ rubi4112r43.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4112r43.conditions rubi4112r43.body rubi4112r43.result rubi4112r43.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else if s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi4112r43, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4112r43, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4112r43.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else if s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r43, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r43, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4112r43_counterexample_complex : ¬ rubi4112r43.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4112r43.conditions rubi4112r43.body rubi4112r43.result rubi4112r43.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else if s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi4112r43, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4112r43, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4112r43.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else if s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r43, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r43, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4112r44_counterexample_real : ¬ rubi4112r44.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4112r44.conditions rubi4112r44.body rubi4112r44.result rubi4112r44.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else if s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi4112r44, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4112r44, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4112r44.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else if s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r44, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r44, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4112r44_counterexample_complex : ¬ rubi4112r44.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4112r44.conditions rubi4112r44.body rubi4112r44.result rubi4112r44.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else if s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi4112r44, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4112r44, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4112r44.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else if s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r44, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r44, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4112r52_counterexample_real : ¬ rubi4112r52.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4112r52.conditions rubi4112r52.body rubi4112r52.result rubi4112r52.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi4112r52, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4112r52, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4112r52.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r52, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r52, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4112r52_counterexample_complex : ¬ rubi4112r52.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4112r52.conditions rubi4112r52.body rubi4112r52.result rubi4112r52.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi4112r52, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4112r52, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4112r52.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4112r52, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4112r52, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4112r81_counterexample_real : ¬ rubi4112r81.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4112r81.conditions rubi4112r81.body rubi4112r81.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi4112r81, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4112r81, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi4112r81, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4112r81_counterexample_complex : ¬ rubi4112r81.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi4112r81.conditions rubi4112r81.body rubi4112r81.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi4112r81, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4112r81, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi4112r81, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4112r82_counterexample_real : ¬ rubi4112r82.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4112r82.conditions rubi4112r82.body rubi4112r82.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi4112r82, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4112r82, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi4112r82, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4112r82_counterexample_complex : ¬ rubi4112r82.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi4112r82.conditions rubi4112r82.body rubi4112r82.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi4112r82, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4112r82, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi4112r82, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4113r1_counterexample_real : ¬ rubi4113r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r1.conditions rubi4113r1.body rubi4113r1.result rubi4113r1.integrals
  refine not_antiderivRecHolds_integrand (fun s => 0) (1 : ℝ) (by simp [rubi4113r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi4113r1.integrals[0]!, by simp [rubi4113r1], ?_⟩
  intro h
  simp [rubi4113r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4113r1_counterexample_complex : ¬ rubi4113r1.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4113r1.conditions rubi4113r1.body rubi4113r1.result rubi4113r1.integrals
  refine not_antiderivRecHolds_integrand (fun s => 0) (1 : ℂ) (by simp [rubi4113r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi4113r1.integrals[0]!, by simp [rubi4113r1], ?_⟩
  intro h
  simp [rubi4113r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4113r11_counterexample_real : ¬ rubi4113r11.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4113r11.conditions rubi4113r11.body rubi4113r11.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi4113r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi4113r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4113r11_counterexample_complex : ¬ rubi4113r11.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi4113r11.conditions rubi4113r11.body rubi4113r11.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi4113r11, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi4113r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4113r12_counterexample_real : ¬ rubi4113r12.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4113r12.conditions rubi4113r12.body rubi4113r12.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi4113r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi4113r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4113r12_counterexample_complex : ¬ rubi4113r12.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi4113r12.conditions rubi4113r12.body rubi4113r12.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi4113r12, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi4113r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4113r13_counterexample_real : ¬ rubi4113r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r13.conditions rubi4113r13.body rubi4113r13.result rubi4113r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi4113r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4113r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4113r13_counterexample_complex : ¬ rubi4113r13.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4113r13.conditions rubi4113r13.body rubi4113r13.result rubi4113r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi4113r13, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4113r13.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4113r14_counterexample_real : ¬ rubi4113r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r14.conditions rubi4113r14.body rubi4113r14.result rubi4113r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi4113r14, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4113r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4113r14_counterexample_complex : ¬ rubi4113r14.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4113r14.conditions rubi4113r14.body rubi4113r14.result rubi4113r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi4113r14, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4113r14.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4113r15_counterexample_real : ¬ rubi4113r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r15.conditions rubi4113r15.body rubi4113r15.result rubi4113r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi4113r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4113r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4113r15_counterexample_complex : ¬ rubi4113r15.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4113r15.conditions rubi4113r15.body rubi4113r15.result rubi4113r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℂ) (by simp [rubi4113r15, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r15, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4113r15.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r15, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4113r16_counterexample_real : ¬ rubi4113r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r16.conditions rubi4113r16.body rubi4113r16.result rubi4113r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi4113r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4113r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4113r16_counterexample_complex : ¬ rubi4113r16.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4113r16.conditions rubi4113r16.body rubi4113r16.result rubi4113r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℂ) (by simp [rubi4113r16, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi4113r16.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi4113r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi4113r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi4113r2_counterexample_real : ¬ rubi4113r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r2.conditions rubi4113r2.body rubi4113r2.result rubi4113r2.integrals
  refine not_antiderivRecHolds_integrand (fun s => 0) (1 : ℝ) (by simp [rubi4113r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi4113r2.integrals[0]!, by simp [rubi4113r2], ?_⟩
  intro h
  simp [rubi4113r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4113r2_counterexample_complex : ¬ rubi4113r2.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi4113r2.conditions rubi4113r2.body rubi4113r2.result rubi4113r2.integrals
  refine not_antiderivRecHolds_integrand (fun s => 0) (1 : ℂ) (by simp [rubi4113r2, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4113r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ⟨rubi4113r2.integrals[0]!, by simp [rubi4113r2], ?_⟩
  intro h
  simp [rubi4113r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4312r3_counterexample_real : ¬ rubi4312r3.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4312r3.conditions rubi4312r3.body rubi4312r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi4312r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4312r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi4312r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi4312r3_counterexample_complex : ¬ rubi4312r3.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi4312r3.conditions rubi4312r3.body rubi4312r3.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi4312r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi4312r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi4312r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi477r5_counterexample_real : ¬ rubi477r5.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi477r5.conditions rubi477r5.body rubi477r5.result
  refine not_antiderivHoldsUnder (fun s => if s = "F" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi477r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi477r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi477r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi477r5_counterexample_complex : ¬ rubi477r5.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi477r5.conditions rubi477r5.body rubi477r5.result
  refine not_antiderivHoldsUnder (fun s => if s = "F" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi477r5, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi477r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi477r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi477r6_counterexample_real : ¬ rubi477r6.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi477r6.conditions rubi477r6.body rubi477r6.result
  refine not_antiderivHoldsUnder (fun s => if s = "F" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi477r6, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi477r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi477r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi477r6_counterexample_complex : ¬ rubi477r6.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi477r6.conditions rubi477r6.body rubi477r6.result
  refine not_antiderivHoldsUnder (fun s => if s = "F" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi477r6, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi477r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi477r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi479r79_counterexample_real : ¬ rubi479r79.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi479r79.conditions rubi479r79.body rubi479r79.result rubi479r79.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" then 1 else 0) (1 : ℝ) (by simp [rubi479r79, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi479r79, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi479r79.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi479r79, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r79, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi479r79_counterexample_complex : ¬ rubi479r79.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi479r79.conditions rubi479r79.body rubi479r79.result rubi479r79.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" then 1 else 0) (1 : ℂ) (by simp [rubi479r79, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi479r79, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (fun h w => w * (((rubi479r79.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "c" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi479r79, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi479r79, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg, ivm6, recEnv] at h <;> norm_num at h

theorem rubi479r81_counterexample_real : ¬ rubi479r81.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi479r81.conditions rubi479r81.body rubi479r81.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" then 1 else 0) (1 : ℝ) (by simp [rubi479r81, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi479r81, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi479r81, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

theorem rubi479r81_counterexample_complex : ¬ rubi479r81.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi479r81.conditions rubi479r81.body rubi479r81.result
  refine not_antiderivHoldsUnder (fun s => if s = "c" then 1 else 0) (1 : ℂ) (by simp [rubi479r81, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4])
    (Eventually.of_forall fun w => by simp [rubi479r81, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] <;> first | positivity | norm_num [iv2, ivm6, ivex2, ivexm6, ivexm1, ivexm4]) ?_
  intro h
  simp [rubi479r81, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivnat, ivneg] at h <;> norm_num at h

end OSR.IntegrationRec14
