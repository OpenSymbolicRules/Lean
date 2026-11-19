import OSR.IntegrationRec91

/-!
# Integration (RUBI): refutations of rules written with Simp or compound conditions

RUBI rules transcribed as stated.  Each is refuted by an explicit assignment:
the conditions hold and the integrand is defined near a point where the
result or a residual integrand is not (RUBI excludes these cases by its rule
order).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec170

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/





/-- RUBI 1.1.1.3 #19 -/
def rubi1113r19 : CRule where
  id := "integration.rubi_1_1_1_3_r19"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "e")) (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1)))))))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 4))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 2))))))) (.var "x")))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 3)) (.int 0)]
  priority := 12104
  description := "RUBI 1.1.1.3 #19"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:19" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#19"

/-- RUBI 1.1.3.5 #7 -/
def rubi1135r7 : CRule where
  id := "integration.rubi_1_1_3_5_r7"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.var "p") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 2))) (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "q", "p"]
  conditions := [.gt (.int (-1)) (.var "p")]
  priority := 12105
  description := "RUBI 1.1.3.5 #7"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:7" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#7"

/-- RUBI 1.1.3.6 #14 -/
def rubi1136r14 : CRule where
  id := "integration.rubi_1_1_3_6_r14"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.var "g") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "g") (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.var "q"))) (.int 1))) (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.app2 .mul (.var "f") (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.var "p"))) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)))) (.int 1)))))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "p", "q", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))]
  priority := 12106
  description := "RUBI 1.1.3.6 #14"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:14" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#14"

/-- RUBI 1.1.3.4 #29 -/
def rubi1134r29 : CRule where
  id := "integration.rubi_1_1_3_4_r29"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int 2)))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "e") (.app2 .add (.var "n") (.int 1)))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 2)))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 2)))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "c") (.int 2))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 2)))) (.int 1))) (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.var "n")) (.app2 .add (.var "p") (.int 1))))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 2)))) (.int 1)) (.int 0)]
  priority := 12107
  description := "RUBI 1.1.3.4 #29"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:29" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#29"

/-- RUBI 1.2.1.2 #77 -/
def rubi1212r77 : CRule where
  id := "integration.rubi_1_2_1_2_r77"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:77"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "e") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.var "e")) (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 12108
  description := "RUBI 1.2.1.2 #77"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:77" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#77"

/-- RUBI 1.2.1.6 #23 -/
def rubi1216r23 : CRule where
  id := "integration.rubi_1_2_1_6_r23"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "h") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "h")) (.var "e")) (.var "p")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app2 .add (.app2 .mul (.var "h") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "g")) (.var "f")))) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "h")) (.var "p")) (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.var "x"))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "h") (.var "c")) (.var "e")) (.var "p")) (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "h") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "g")) (.var "f")))) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))))) (.pow (.var "x") (.int 2))))))]
  independent := ["a", "c", "d", "e", "f", "g", "h", "q", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0),
    .gt (.var "p") (.int 0),
    .ne (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)) (.int 0)]
  priority := 12109
  description := "RUBI 1.2.1.6 #23"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:23" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#23"

/-- RUBI 1.2.2.4 #70 -/
def rubi1224r70 : CRule where
  id := "integration.rubi_1_2_2_4_r70"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:70"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1)))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.app2 .add (.var "m") (.int 3))) (.pow (.var "x") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.var "m") (.int 3))) (.pow (.var "x") (.int 4))))))]
  independent := ["a", "c", "d", "e", "m"]
  conditions := [.int (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1)))),
    .gt (.int 0) (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))]
  priority := 12110
  description := "RUBI 1.2.2.4 #70"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:70" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#70"

/-- RUBI 1.2.2.3 #39 -/
def rubi1223r39 : CRule where
  id := "integration.rubi_1_2_2_3_r39"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:39"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.var "x")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2)) (.int (-1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))) (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 3))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.app2 .add (.var "q") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "e")) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.app2 .add (.var "q") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.app2 .add (.var "q") (.int 2))))) (.pow (.var "x") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int 2))) (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 5))) (.pow (.var "x") (.int 4))))))]
  independent := ["a", "b", "c", "d", "e", "q"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "q"),
    .gt (.int (-1)) (.var "q")]
  priority := 12111
  description := "RUBI 1.2.2.3 #39"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:39" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#39"

/-- RUBI 1.2.3.4 #36 -/
def rubi1234r36 : CRule where
  id := "integration.rubi_1_2_3_4_r36"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:36"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "f")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.app2 .add (.app2 .mul (.var "d") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))) (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "c", "d", "e", "f", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p"),
    .int (.var "p")]
  priority := 12112
  description := "RUBI 1.2.3.4 #36"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:36" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#36"

/-- RUBI 1.2.3.2 #8 -/
def rubi1232r8 : CRule where
  id := "integration.rubi_1_2_3_2_r8"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.app2 .mul (.int (-1)) (.int 1))))) (.int 1))) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.app2 .mul (.int (-1)) (.int 1))))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "n")) (.var "p")) (.pow (.var "d") (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.app2 .mul (.int (-1)) (.int 1))))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.app2 .mul (.int (-1)) (.int 1))))) (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.int 1))))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0),
    .gt (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1)) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.app2 .mul (.int (-1)) (.int 1))))) (.int 1)) (.int 0)]
  priority := 12113
  description := "RUBI 1.2.3.2 #8"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:8" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p.m#8"






/-- RUBI 7.2.5 #10 -/
def rubi725r10 : CRule where
  id := "integration.rubi_7_2_5_r10"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.5 u (a+b arccosh(c x))^n:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app2 .root (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app2 .add (.app2 .mul (.var "d1") (.var "d2")) (.app2 .mul (.app2 .mul (.var "e1") (.var "e2")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.app2 .mul (.app2 .mul (.int (-1)) (.var "d1")) (.var "d2")) (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.app2 .mul (.app2 .mul (.int (-1)) (.var "d1")) (.var "d2")) (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d1") (.var "d2")) (.var "g")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e1")) (.var "e2")) (.var "f")) (.var "x"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e1") (.var "e2")) (.var "g")) (.app2 .add (.var "m") (.int 2))) (.pow (.var "x") (.int 2)))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d1", "e1", "d2", "e2", "f", "g", "m", "n"]
  conditions := [.eq (.app2 .add (.var "e1") (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d1"))) (.int 0),
    .eq (.app2 .add (.var "e2") (.app2 .mul (.var "c") (.var "d2"))) (.int 0),
    .int (.var "m"),
    .gt (.int 0) (.var "m"),
    .gt (.var "d1") (.int 0),
    .gt (.int 0) (.var "d2"),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 12119
  description := "RUBI 7.2.5 #10"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.5 u (a+b arccosh(c x))^n:10" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.5 u (a+b arccosh(c x))^n.m#10"

/-- RUBI 1.1.1.4 #10 -/
def rubi1114r10 : CRule where
  id := "integration.rubi_1_1_1_4_r10"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.var "c") (.var "f")))) (.var "g"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "e")) (.var "h"))) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h")))) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1)))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "f")) (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h")))) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 3))) (.var "x")))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "n", "p", "m"]
  conditions := [.int (.var "m"),
    .gt (.int (-1)) (.var "m")]
  priority := 12120
  description := "RUBI 1.1.1.4 #10"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:10" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#10"


/-- RUBI 1.1.1.7 #16 -/
def rubi1117r16 : CRule where
  id := "integration.rubi_1_1_1_7_r16"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.var "x"))) (.app2 .mul (.var "C") (.pow (.var "x") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "C") (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "h")) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "C") (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "h")))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "d")) (.var "f")) (.var "h")) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "d")) (.var "f")) (.var "h")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int 2)) (.pow (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .mul (.int 3) (.pow (.int 2) (.int (-1))))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.int (-1)))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "A")) (.var "b")) (.var "d")) (.var "f")) (.var "h")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "e")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "f")) (.var "h"))))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "B")) (.var "d")) (.var "f")) (.var "h")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.var "h")) (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.var "g")) (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.var "h"))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.var "h"))))))) (.var "x")))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "A", "B", "C"]
  priority := 12122
  description := "RUBI 1.1.1.7 #16"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:16" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#16"

/-- RUBI 1.1.1.3 #27 -/
def rubi1113r27 : CRule where
  id := "integration.rubi_1_1_1_3_r27"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "e")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1)))))))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.var "n")) (.var "p"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "m") (.var "n"))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "m") (.var "p"))))))) (.var "x")))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "p", "m"]
  conditions := [.gt (.var "m") (.int 1),
    .ne (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 1)) (.int 0),
    .int (.var "m")]
  priority := 12123
  description := "RUBI 1.1.1.3 #27"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:27" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#27"

/-- RUBI 1.1.3.5 #8 -/
def rubi1135r8 : CRule where
  id := "integration.rubi_1_1_3_5_r8"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .add (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "n")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))))) (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "n")) (.var "q")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "e")) (.var "n")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "p", "q"]
  conditions := [.gt (.var "q") (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int 1)) (.int 0)]
  priority := 12124
  description := "RUBI 1.1.3.5 #8"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:8" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#8"

/-- RUBI 1.1.3.6 #15 -/
def rubi1136r15 : CRule where
  id := "integration.rubi_1_1_3_6_r15"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "g")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.pow (.var "g") (.var "n"))) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.var "c")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "n")) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "p")) (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "q"))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 2)))) (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "p", "q", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 12125
  description := "RUBI 1.1.3.6 #15"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:15" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#15"



/-- RUBI 1.2.1.6 #24 -/
def rubi1216r24 : CRule where
  id := "integration.rubi_1_2_1_6_r24"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "h") (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "h") (.var "p")) (.var "b")) (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.int (-2))) (.var "g")) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "h")) (.var "p")) (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.int (-2))) (.var "g")) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)))) (.var "x"))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "h") (.var "p")) (.int (-1))) (.var "b")) (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.int (-2))) (.var "g")) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)))) (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c", "d", "f", "g", "h", "q", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.var "p") (.int 0),
    .ne (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)) (.int 0)]
  priority := 12128
  description := "RUBI 1.2.1.6 #24"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:24" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#24"


/-- RUBI 1.2.2.3 #40 -/
def rubi1223r40 : CRule where
  id := "integration.rubi_1_2_2_3_r40"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:40"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.var "x")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2)) (.int (-1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))) (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 3))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.var "d") (.int 2))) (.app2 .add (.var "q") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "e")) (.var "c")) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.pow (.var "x") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int 2))) (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 5))) (.pow (.var "x") (.int 4))))))]
  independent := ["a", "c", "d", "e", "q"]
  conditions := [.int (.var "q"),
    .gt (.int (-1)) (.var "q")]
  priority := 12130
  description := "RUBI 1.2.2.3 #40"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:40" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#40"

/-- RUBI 1.2.3.3 #17 -/
def rubi1233r17 : CRule where
  id := "integration.rubi_1_2_3_3_r17"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.var "x")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "e") (.int 2))) (.var "n")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 1))) (.var "d")) (.pow (.var "e") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 1))) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "e")) (.var "n")) (.app2 .add (.var "q") (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "n", "n2", "q"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "q")]
  priority := 12131
  description := "RUBI 1.2.3.3 #17"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:17" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#17"

/-- RUBI 1.2.3.4 #31 -/
def rubi1234r31 : CRule where
  id := "integration.rubi_1_2_3_4_r31"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "n")) (.var "p")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.var "m")) (.int 1))) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.var "m")) (.int 1))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "n") (.var "p")) (.pow (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.var "m")) (.int 1))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "e")) (.app2 .add (.var "m") (.int 1)))) (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.var "e")) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.var "m")) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.var "p"))) (.int 1)))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.var "p") (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.var "m")) (.int 1)) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1)) (.int 0),
    .int (.var "p")]
  priority := 12132
  description := "RUBI 1.2.3.4 #31"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:31" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#31"

/-- RUBI 1.2.3.4 #37 -/
def rubi1234r37 : CRule where
  id := "integration.rubi_1_2_3_4_r37"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:37"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.var "f") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.var "n"))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.var "p"))) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1)))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "m", "n", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1)) (.int 0),
    .int (.var "p")]
  priority := 12133
  description := "RUBI 1.2.3.4 #37"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:37" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#37"




/-- RUBI 1.1.1.4 #23 -/
def rubi1114r23 : CRule where
  id := "integration.rubi_1_1_1_4_r23"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h")))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "g")) (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "h"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")) (.var "h"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "h")) (.var "x"))) (.pow (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h"]
  priority := 12137
  description := "RUBI 1.1.1.4 #23"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:23" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#23"


/-- RUBI 1.1.1.7 #17 -/
def rubi1117r17 : CRule where
  id := "integration.rubi_1_1_1_7_r17"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.var "x") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "C") (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "h")) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "C") (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "h")))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "d")) (.var "f")) (.var "h")) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "d")) (.var "f")) (.var "h")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int 2)) (.pow (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .mul (.int 3) (.pow (.int 2) (.int (-1))))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.int (-1)))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "A")) (.var "b")) (.var "d")) (.var "f")) (.var "h")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "e")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "f")) (.var "h"))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.var "h")) (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.var "g")) (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.var "h"))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.var "h")))))) (.var "x")))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "A", "C"]
  priority := 12139
  description := "RUBI 1.1.1.7 #17"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:17" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#17"


/-- RUBI 1.1.3.6 #25 -/
def rubi1136r25 : CRule where
  id := "integration.rubi_1_1_3_6_r25"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "g")) (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.var "p") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 2)))) (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "q", "p"]
  conditions := [.gt (.int (-1)) (.var "p")]
  priority := 12141
  description := "RUBI 1.1.3.6 #25"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:25" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#25"



/-- RUBI 1.2.1.6 #17 -/
def rubi1216r17 : CRule where
  id := "integration.rubi_1_2_1_6_r17"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "h")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.var "c")) (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 2) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.var "c")) (.var "d")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h")) (.var "e")) (.var "q"))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.var "c")) (.var "e")) (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.var "q")) (.int 3))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.int 2)) (.var "h")) (.var "f")) (.var "q"))) (.var "x"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.var "c")) (.var "f")) (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.app2 .mul (.int 2) (.var "q"))) (.int 3))) (.pow (.var "x") (.int 2))))))]
  independent := ["a", "c", "d", "e", "f", "g", "h", "p", "q"]
  conditions := [.ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "q") (.int 0)]
  priority := 12144
  description := "RUBI 1.2.1.6 #17"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:17" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#17"


/-- RUBI 1.2.3.3 #18 -/
def rubi1233r18 : CRule where
  id := "integration.rubi_1_2_3_3_r18"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.var "x")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "e") (.int 2))) (.var "n")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 1))) (.var "d")) (.pow (.var "e") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 1))) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "e")) (.var "n")) (.app2 .add (.var "q") (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "c", "d", "e", "n", "n2", "q"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "q")]
  priority := 12146
  description := "RUBI 1.2.3.3 #18"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:18" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#18"

/-- RUBI 1.2.3.4 #32 -/
def rubi1234r32 : CRule where
  id := "integration.rubi_1_2_3_4_r32"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:32"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.var "m")) (.int 1))) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.var "m")) (.int 1))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.var "m")) (.int 1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .add (.app2 .mul (.var "d") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1))) (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.var "m")) (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "c", "d", "e", "f", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.var "p") (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.var "m")) (.int 1)) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1)))) (.int 1)) (.int 0),
    .int (.var "p")]
  priority := 12147
  description := "RUBI 1.2.3.4 #32"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:32" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#32"

/-- RUBI 1.2.3.4 #39 -/
def rubi1234r39 : CRule where
  id := "integration.rubi_1_2_3_4_r39"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:39"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "f") (.var "n"))) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "m", "n", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "m"),
    .int (.var "p")]
  priority := 12148
  description := "RUBI 1.2.3.4 #39"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:39" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#39"






/-- RUBI 1.3.3 #28 -/
def rubi133r28 : CRule where
  id := "integration.rubi_1_3_3_r28"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:28"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-6)) (.var "a")) (.pow (.var "d") (.int 3))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "b") (.pow (.var "c") (.int 3))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 28)) (.var "a")) (.pow (.var "d") (.int 3))))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "b") (.pow (.var "c") (.int 3))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 28)) (.var "a")) (.pow (.var "d") (.int 3))))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "b") (.pow (.var "c") (.int 3))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 22)) (.var "a")) (.pow (.var "d") (.int 3))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 6) (.var "a")) (.pow (.var "d") (.int 4))) (.var "x"))) (.pow (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 6))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 20)) (.var "a")) (.var "b")) (.pow (.var "c") (.int 3))) (.pow (.var "d") (.int 3)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 8)) (.pow (.var "a") (.int 2))) (.pow (.var "d") (.int 6)))) (.int 0)]
  priority := 12154
  description := "RUBI 1.3.3 #28"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:28" "1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions.m#28"

/-- RUBI 1.1.1.4 #8 -/
def rubi1114r8 : CRule where
  id := "integration.rubi_1_1_1_4_r8"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "h")))) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.var "n")) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1)))))) (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "h")))) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.app2 .mul (.var "b") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "h")))) (.app2 .add (.app2 .add (.var "n") (.var "p")) (.int 1))))) (.var "x")))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "p", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.int (-1)) (.var "m"),
    .gt (.var "n") (.int 0)]
  priority := 12155
  description := "RUBI 1.1.1.4 #8"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:8" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#8"



/-- RUBI 1.1.1.7 #14 -/
def rubi1117r14 : CRule where
  id := "integration.rubi_1_1_1_7_r14"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.var "x"))) (.app2 .mul (.var "C") (.pow (.var "x") (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "C")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m"))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.var "h")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 3))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.var "h")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 3))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.int 2))) (.app2 .root (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.int 2))) (.int (-1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.var "g")) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.var "g"))) (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.var "h")))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.var "e")) (.var "g")) (.var "m"))))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.var "a") (.var "B"))) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.var "g")) (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.var "h"))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.var "h")))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.var "g")) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.var "g"))) (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.var "h"))))))) (.var "x"))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 3))) (.app2 .mul (.app2 .mul (.int 2) (.var "C")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.var "h")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.var "g")) (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.var "h"))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.var "h"))))))) (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "A", "B", "C", "m"]
  conditions := [.int (.app2 .mul (.int 2) (.var "m")),
    .gt (.var "m") (.int 0)]
  priority := 12158
  description := "RUBI 1.1.1.7 #14"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:14" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.7 P(x) (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#14"


/-- RUBI 1.1.3.5 #6 -/
def rubi1135r6 : CRule where
  id := "integration.rubi_1_1_3_5_r6"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .add (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .mul (.var "b") (.var "e"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.app2 .add (.app2 .mul (.var "n") (.var "q")) (.int 1))))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "p", "q"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .gt (.var "q") (.int 0)]
  priority := 12160
  description := "RUBI 1.1.3.5 #6"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:6" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#6"

/-- RUBI 1.1.3.6 #11 -/
def rubi1136r11 : CRule where
  id := "integration.rubi_1_1_3_6_r11"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "g")) (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.var "p") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 2)))) (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "q", "n", "p"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p")]
  priority := 12161
  description := "RUBI 1.1.3.6 #11"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:11" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#11"

/-- RUBI 1.1.3.4 #28 -/
def rubi1134r28 : CRule where
  id := "integration.rubi_1_1_3_4_r28"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:28"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int 2)))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "b") (.int 2))) (.var "e")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "b") (.int 2))) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.var "n")) (.app2 .add (.var "p") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.pow (.var "d") (.int 2))) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p")]
  priority := 12162
  description := "RUBI 1.1.3.4 #28"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:28" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#28"

/-- RUBI 1.2.1.2 #76 -/
def rubi1212r76 : CRule where
  id := "integration.rubi_1_2_1_2_r76"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:76"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "e") (.int 2)))) (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 12163
  description := "RUBI 1.2.1.2 #76"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:76" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#76"


/-- RUBI 1.2.1.3 #34 -/
def rubi1213r34 : CRule where
  id := "integration.rubi_1_2_1_3_r34"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:34"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .add (.app2 .mul (.var "a") (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")) (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 5))) (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "c", "f", "g", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.pow (.var "g") (.int 2))) (.app2 .mul (.pow (.var "f") (.int 2)) (.var "c"))) (.int 0),
    .gt (.int (-2)) (.var "p")]
  priority := 12165
  description := "RUBI 1.2.1.3 #34"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:34" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#34"

/-- RUBI 1.2.1.6 #22 -/
def rubi1216r22 : CRule where
  id := "integration.rubi_1_2_1_6_r22"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:22"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "h") (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "h") (.var "p")) (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e")))) (.app2 .mul (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.var "h") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "g")) (.var "f")))) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "h")) (.var "p")) (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "h") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "g")) (.var "f")))) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)))) (.var "x"))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "h") (.var "p")) (.app2 .add (.app2 .mul (.var "c") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")))) (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "h") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "g")) (.var "f")))) (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)))) (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "q", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.pow (.var "e") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "d")) (.var "f"))) (.int 0),
    .gt (.var "p") (.int 0),
    .ne (.app2 .add (.app2 .add (.var "p") (.var "q")) (.int 1)) (.int 0)]
  priority := 12166
  description := "RUBI 1.2.1.6 #22"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:22" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#22"

/-- RUBI 1.2.2.4 #69 -/
def rubi1224r69 : CRule where
  id := "integration.rubi_1_2_2_4_r69"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:69"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2))) (.int (-1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "m") (.int 2)))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.app2 .add (.var "m") (.int 2))) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.app2 .add (.var "m") (.int 3)))) (.pow (.var "x") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "e")) (.app2 .add (.var "m") (.int 3))) (.pow (.var "x") (.int 4))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1)))),
    .gt (.int 0) (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))]
  priority := 12167
  description := "RUBI 1.2.2.4 #69"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:69" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#69"

/-- RUBI 1.2.3.4 #35 -/
def rubi1234r35 : CRule where
  id := "integration.rubi_1_2_3_4_r35"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:35"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "d") (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c")))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "e"))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "e"))) (.var "c")) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1)))) (.int 1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "e")) (.app2 .add (.var "m") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))) (.int 1))) (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "e")))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p"),
    .int (.var "p")]
  priority := 12168
  description := "RUBI 1.2.3.4 #35"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p:35" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#35"


/-- RUBI 1.2.3.2 #14 -/
def rubi1232r14 : CRule where
  id := "integration.rubi_1_2_3_2_r14"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.int 1))) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "p", "m", "n", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p"))) (.int 1)) (.int 0),
    .int (.var "p")]
  priority := 12170
  description := "RUBI 1.2.3.2 #14"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:14" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p.m#14"






/-- RUBI 1.3.3 #27 -/
def rubi133r27 : CRule where
  id := "integration.rubi_1_3_3_r27"; legacyId := some "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.pow (.app2 .mul (.int 3) (.var "c")) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.int 3) (.var "c")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "d")) (.var "x"))) (.pow (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 3)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.pow (.var "c") (.int 3))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.pow (.var "d") (.int 3)))) (.int 0)]
  priority := 12176
  description := "RUBI 1.3.3 #27"
  provenance := migrated "rubi:1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions:27" "1 Algebraic functions/1.3 Miscellaneous/1.3.3 Miscellaneous algebraic functions.m#27"

/-- RUBI 1.1.1.4 #12 -/
def rubi1114r12 : CRule where
  id := "integration.rubi_1_1_1_4_r12"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "h") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p"))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.var "g")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "h")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "e")) (.var "m")) (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.var "p") (.int 1)))))))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "f")) (.var "g")) (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2))) (.app2 .mul (.var "h") (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.var "m")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)))))))) (.var "x")))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "n", "p", "m"]
  conditions := [.gt (.var "m") (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .add (.var "m") (.var "n")) (.var "p")) (.int 2)) (.int 0),
    .int (.var "m")]
  priority := 12177
  description := "RUBI 1.1.1.4 #12"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:12" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#12"





/-- RUBI 1.1.3.6 #10 -/
def rubi1136r10 : CRule where
  id := "integration.rubi_1_1_3_6_r10"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "g") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "g") (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.var "q"))) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.app2 .add (.app2 .mul (.var "c") (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "e")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "q", "m", "n", "p"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.int 0)]
  priority := 12182
  description := "RUBI 1.1.3.6 #10"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:10" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#10"

/-- RUBI 1.1.3.4 #27 -/
def rubi1134r27 : CRule where
  id := "integration.rubi_1_1_3_4_r27"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.int 2)))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "e") (.var "n"))) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "c") (.int 2))) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "d")))) (.app2 .add (.var "m") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app2 .add (.var "m") (.int 1))) (.pow (.var "d") (.int 2))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "p", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "m"),
    .gt (.var "n") (.int 0)]
  priority := 12183
  description := "RUBI 1.1.3.4 #27"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:27" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#27"



/-- RUBI 1.2.3.3 #26 -/
def rubi1233r26 : CRule where
  id := "integration.rubi_1_2_3_3_r26"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:26"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.var "d") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "e"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c")) (.var "d"))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "e"))) (.var "c")) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "n") (.var "p")) (.var "n")) (.int 1)) (.var "d")) (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "e"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c")) (.var "d")) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.app2 .mul (.int 2) (.var "n"))) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.var "p")) (.app2 .mul (.int 3) (.var "n"))) (.int 1)) (.app2 .add (.app2 .mul (.var "d") (.var "b")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "e")))) (.var "c")) (.pow (.var "x") (.var "n")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "p"),
    .gt (.int (-1)) (.var "p")]
  priority := 12186
  description := "RUBI 1.2.3.3 #26"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:26" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#26"


/-- RUBI 1.2.3.2 #13 -/
def rubi1232r13 : CRule where
  id := "integration.rubi_1_2_3_2_r13"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app2 .add (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c"))) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int 2) (.var "n")) (.app2 .add (.var "p") (.int 1)))) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))) (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "m", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.int (-1)) (.var "p")]
  priority := 12188
  description := "RUBI 1.2.3.2 #13"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p:13" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p.m#13"


/-! ## Refutations -/

theorem rubi1113r19_counterexample_real : ¬ rubi1113r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1113r19.conditions rubi1113r19.body rubi1113r19.result rubi1113r19.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1113r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1113r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1113r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1113r19, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1113r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1113r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1135r7_counterexample_real : ¬ rubi1135r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1135r7.conditions rubi1135r7.body rubi1135r7.result rubi1135r7.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (1 : ℝ) else if s = "f" then (4 : ℝ) else if s = "p" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1135r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1135r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1135r7.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "f" then (4 : ℝ) else if s = "p" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1135r7, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1135r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1135r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1136r14_counterexample_real : ¬ rubi1136r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1136r14.conditions rubi1136r14.body rubi1136r14.result rubi1136r14.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (2 : ℝ) else if s = "g" then (1 : ℝ) else if s = "m" then (3 : ℝ) else if s = "n" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1136r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1136r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1136r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (2 : ℝ) else if s = "g" then (1 : ℝ) else if s = "m" then (3 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1136r14, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1136r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1136r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1134r29_counterexample_real : ¬ rubi1134r29.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1134r29.conditions rubi1134r29.body rubi1134r29.result rubi1134r29.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (4 : ℝ) else if s = "d" then (-1 : ℝ) else if s = "n" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1134r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1134r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1134r29.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (4 : ℝ) else if s = "d" then (-1 : ℝ) else if s = "n" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1134r29, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1134r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1134r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1212r77_counterexample_real : ¬ rubi1212r77.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r77.conditions rubi1212r77.body rubi1212r77.result rubi1212r77.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-3 : ℝ) else if s = "e" then (1 : ℝ) else if s = "m" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1212r77, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1212r77, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1212r77.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-3 : ℝ) else if s = "e" then (1 : ℝ) else if s = "m" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1212r77, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1212r77, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1212r77, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1216r23_counterexample_real : ¬ rubi1216r23.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1216r23.conditions rubi1216r23.body rubi1216r23.result rubi1216r23.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "e" then ((1 : ℝ) / 2) else if s = "p" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1216r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1216r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1216r23.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "e" then ((1 : ℝ) / 2) else if s = "p" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1216r23, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1216r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1216r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1224r70_counterexample_real : ¬ rubi1224r70.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r70.conditions rubi1224r70.body rubi1224r70.result rubi1224r70.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "c" then (1 : ℝ) else if s = "d" then (2 : ℝ) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1224r70, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1224r70, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1224r70.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then (1 : ℝ) else if s = "d" then (2 : ℝ) else if s = "m" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1224r70, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1224r70, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1224r70, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1223r39_counterexample_real : ¬ rubi1223r39.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1223r39.conditions rubi1223r39.body rubi1223r39.result rubi1223r39.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "d" then (-1 : ℝ) else if s = "q" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1223r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1223r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1223r39.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "d" then (-1 : ℝ) else if s = "q" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1223r39, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1223r39, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1223r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1234r36_counterexample_real : ¬ rubi1234r36.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r36.conditions rubi1234r36.body rubi1234r36.result rubi1234r36.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "c" then (2 : ℝ) else if s = "m" then (3 : ℝ) else if s = "n" then (1 : ℝ) else if s = "n2" then (2 : ℝ) else if s = "p" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1234r36, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1234r36, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1234r36.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then (2 : ℝ) else if s = "m" then (3 : ℝ) else if s = "n" then (1 : ℝ) else if s = "n2" then (2 : ℝ) else if s = "p" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1234r36, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1234r36, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1234r36, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1232r8_counterexample_real : ¬ rubi1232r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1232r8.conditions rubi1232r8.body rubi1232r8.result rubi1232r8.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (3 : ℝ) else if s = "m" then (1 : ℝ) else if s = "n" then (1 : ℝ) else if s = "n2" then (2 : ℝ) else if s = "p" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1232r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1232r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1232r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (3 : ℝ) else if s = "m" then (1 : ℝ) else if s = "n" then (1 : ℝ) else if s = "n2" then (2 : ℝ) else if s = "p" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1232r8, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1232r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1232r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi725r10_counterexample_real : ¬ rubi725r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi725r10.conditions rubi725r10.body rubi725r10.result rubi725r10.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "c" then (1 : ℝ) else if s = "d1" then (2 : ℝ) else if s = "d2" then (-1 : ℝ) else if s = "e1" then (2 : ℝ) else if s = "e2" then (1 : ℝ) else if s = "f" then (-1 : ℝ) else if s = "g" then (1 : ℝ) else if s = "m" then (-1 : ℝ) else if s = "n" then (1 : ℝ) else 0) (2 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi725r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (2 : ℝ) - 1/16 < 2 by norm_num) (show (2 : ℝ) < 2 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi725r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi725r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then (1 : ℝ) else if s = "d1" then (2 : ℝ) else if s = "d2" then (-1 : ℝ) else if s = "e1" then (2 : ℝ) else if s = "e2" then (1 : ℝ) else if s = "f" then (-1 : ℝ) else if s = "g" then (1 : ℝ) else if s = "m" then (-1 : ℝ) else if s = "n" then (1 : ℝ) else 0) "x" (2 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi725r10, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi725r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi725r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1114r10_counterexample_real : ¬ rubi1114r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1114r10.conditions rubi1114r10.body rubi1114r10.result rubi1114r10.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (4 : ℝ) else if s = "d" then (-3 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1114r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1114r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1114r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (4 : ℝ) else if s = "d" then (-3 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1114r10, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1114r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1114r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1117r16_counterexample_real : ¬ rubi1117r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1117r16.conditions rubi1117r16.body rubi1117r16.result rubi1117r16.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (-3 : ℝ) else if s = "c" then (4 : ℝ) else if s = "e" then (2 : ℝ) else if s = "h" then (-1 : ℝ) else 0) (-1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1117r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) - 1/16 < -1 by norm_num) (show (-1 : ℝ) < -1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1117r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1117r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (-3 : ℝ) else if s = "c" then (4 : ℝ) else if s = "e" then (2 : ℝ) else if s = "h" then (-1 : ℝ) else 0) "x" (-1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1117r16, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1117r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1117r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1113r27_counterexample_real : ¬ rubi1113r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1113r27.conditions rubi1113r27.body rubi1113r27.result rubi1113r27.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "m" then (4 : ℝ) else if s = "n" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1113r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1113r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1113r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then (4 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1113r27, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1113r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1113r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1135r8_counterexample_real : ¬ rubi1135r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1135r8.conditions rubi1135r8.body rubi1135r8.result rubi1135r8.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "e" then (1 : ℝ) else if s = "q" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1135r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1135r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1135r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "e" then (1 : ℝ) else if s = "q" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1135r8, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1135r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1135r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1136r15_counterexample_real : ¬ rubi1136r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1136r15.conditions rubi1136r15.body rubi1136r15.result rubi1136r15.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (1 : ℝ) else if s = "g" then (4 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (1 : ℝ) else if s = "q" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1136r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1136r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1136r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (1 : ℝ) else if s = "g" then (4 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (1 : ℝ) else if s = "q" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1136r15, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1136r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1136r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1216r24_counterexample_real : ¬ rubi1216r24.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1216r24.conditions rubi1216r24.body rubi1216r24.result rubi1216r24.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (-2 : ℝ) else if s = "c" then (3 : ℝ) else if s = "p" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1216r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1216r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1216r24.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (-2 : ℝ) else if s = "c" then (3 : ℝ) else if s = "p" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1216r24, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1216r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1216r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1223r40_counterexample_real : ¬ rubi1223r40.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1223r40.conditions rubi1223r40.body rubi1223r40.result rubi1223r40.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (3 : ℝ) else if s = "e" then (-3 : ℝ) else if s = "q" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1223r40, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1223r40, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1223r40.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (3 : ℝ) else if s = "e" then (-3 : ℝ) else if s = "q" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1223r40, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1223r40, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1223r40, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1233r17_counterexample_real : ¬ rubi1233r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1233r17.conditions rubi1233r17.body rubi1233r17.result rubi1233r17.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-3 : ℝ) else if s = "c" then (1 : ℝ) else if s = "e" then (2 : ℝ) else if s = "q" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1233r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1233r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1233r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-3 : ℝ) else if s = "c" then (1 : ℝ) else if s = "e" then (2 : ℝ) else if s = "q" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1233r17, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1233r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1233r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1234r31_counterexample_real : ¬ rubi1234r31.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r31.conditions rubi1234r31.body rubi1234r31.result rubi1234r31.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (3 : ℝ) else if s = "d" then (2 : ℝ) else if s = "n" then (1 : ℝ) else if s = "n2" then (2 : ℝ) else if s = "p" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1234r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1234r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1234r31.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (3 : ℝ) else if s = "d" then (2 : ℝ) else if s = "n" then (1 : ℝ) else if s = "n2" then (2 : ℝ) else if s = "p" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1234r31, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1234r31, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1234r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1234r37_counterexample_real : ¬ rubi1234r37.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r37.conditions rubi1234r37.body rubi1234r37.result rubi1234r37.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (-1 : ℝ) else if s = "d" then (4 : ℝ) else if s = "m" then (4 : ℝ) else if s = "n" then (2 : ℝ) else if s = "n2" then (4 : ℝ) else if s = "p" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1234r37, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1234r37, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1234r37.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (-1 : ℝ) else if s = "d" then (4 : ℝ) else if s = "m" then (4 : ℝ) else if s = "n" then (2 : ℝ) else if s = "n2" then (4 : ℝ) else if s = "p" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1234r37, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1234r37, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1234r37, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1114r23_counterexample_real : ¬ rubi1114r23.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1114r23.conditions rubi1114r23.body rubi1114r23.result rubi1114r23.integrals
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
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" then (-2 : ℝ) else if s = "d" then ((1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1114r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1114r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi1114r23, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi1114r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi1117r17_counterexample_real : ¬ rubi1117r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1117r17.conditions rubi1117r17.body rubi1117r17.result rubi1117r17.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (3 : ℝ) else if s = "d" then ((1 : ℝ) / 2) else if s = "e" then (1 : ℝ) else if s = "g" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1117r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1117r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1117r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (3 : ℝ) else if s = "d" then ((1 : ℝ) / 2) else if s = "e" then (1 : ℝ) else if s = "g" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1117r17, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1117r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1117r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1136r25_counterexample_real : ¬ rubi1136r25.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1136r25.conditions rubi1136r25.body rubi1136r25.result rubi1136r25.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "m" then (1 : ℝ) else if s = "p" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1136r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1136r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1136r25.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "m" then (1 : ℝ) else if s = "p" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1136r25, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1136r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1136r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1216r17_counterexample_real : ¬ rubi1216r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1216r17.conditions rubi1216r17.body rubi1216r17.result rubi1216r17.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "c" then ((1 : ℝ) / 2) else if s = "e" then (-3 : ℝ) else if s = "p" then (-2 : ℝ) else if s = "q" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1216r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1216r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1216r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then ((1 : ℝ) / 2) else if s = "e" then (-3 : ℝ) else if s = "p" then (-2 : ℝ) else if s = "q" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1216r17, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1216r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1216r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1233r18_counterexample_real : ¬ rubi1233r18.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1233r18.conditions rubi1233r18.body rubi1233r18.result rubi1233r18.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "c" then ((-1 : ℝ) / 2) else if s = "d" then (2 : ℝ) else if s = "q" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1233r18, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1233r18, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1233r18.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then ((-1 : ℝ) / 2) else if s = "d" then (2 : ℝ) else if s = "q" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1233r18, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1233r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1233r18, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1234r32_counterexample_real : ¬ rubi1234r32.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r32.conditions rubi1234r32.body rubi1234r32.result rubi1234r32.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (3 : ℝ) else if s = "c" then ((-1 : ℝ) / 2) else if s = "n" then (1 : ℝ) else if s = "n2" then (2 : ℝ) else if s = "p" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1234r32, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1234r32, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1234r32.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (3 : ℝ) else if s = "c" then ((-1 : ℝ) / 2) else if s = "n" then (1 : ℝ) else if s = "n2" then (2 : ℝ) else if s = "p" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1234r32, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1234r32, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1234r32, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1234r39_counterexample_real : ¬ rubi1234r39.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r39.conditions rubi1234r39.body rubi1234r39.result rubi1234r39.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (-1 : ℝ) else if s = "d" then (1 : ℝ) else if s = "f" then (-3 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (2 : ℝ) else if s = "n2" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1234r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1234r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1234r39.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (-1 : ℝ) else if s = "d" then (1 : ℝ) else if s = "f" then (-3 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (2 : ℝ) else if s = "n2" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1234r39, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1234r39, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1234r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi133r28_counterexample_real : ¬ rubi133r28.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi133r28.conditions rubi133r28.body rubi133r28.result rubi133r28.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (4 : ℝ) else if s = "c" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi133r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi133r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi133r28.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (4 : ℝ) else if s = "c" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi133r28, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi133r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi133r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1114r8_counterexample_real : ¬ rubi1114r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1114r8.conditions rubi1114r8.body rubi1114r8.result rubi1114r8.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (4 : ℝ) else if s = "d" then (-3 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1114r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1114r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1114r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (4 : ℝ) else if s = "d" then (-3 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1114r8, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1114r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1114r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1117r14_counterexample_real : ¬ rubi1117r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1117r14.conditions rubi1117r14.body rubi1117r14.result rubi1117r14.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "A" then (2 : ℝ) else if s = "c" then ((1 : ℝ) / 2) else if s = "e" then (1 : ℝ) else if s = "h" then (3 : ℝ) else if s = "m" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1117r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1117r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1117r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then (2 : ℝ) else if s = "c" then ((1 : ℝ) / 2) else if s = "e" then (1 : ℝ) else if s = "h" then (3 : ℝ) else if s = "m" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1117r14, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1117r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1117r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1135r6_counterexample_real : ¬ rubi1135r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1135r6.conditions rubi1135r6.body rubi1135r6.result rubi1135r6.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-3 : ℝ) else if s = "p" then (-3 : ℝ) else if s = "q" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1135r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1135r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1135r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-3 : ℝ) else if s = "p" then (-3 : ℝ) else if s = "q" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1135r6, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1135r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1135r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1136r11_counterexample_real : ¬ rubi1136r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1136r11.conditions rubi1136r11.body rubi1136r11.result rubi1136r11.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "n" then (1 : ℝ) else if s = "p" then (-2 : ℝ) else if s = "q" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1136r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1136r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1136r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "n" then (1 : ℝ) else if s = "p" then (-2 : ℝ) else if s = "q" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1136r11, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1136r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1136r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1134r28_counterexample_real : ¬ rubi1134r28.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1134r28.conditions rubi1134r28.body rubi1134r28.result rubi1134r28.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (4 : ℝ) else if s = "c" then (4 : ℝ) else if s = "n" then (2 : ℝ) else if s = "p" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1134r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1134r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1134r28.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (4 : ℝ) else if s = "c" then (4 : ℝ) else if s = "n" then (2 : ℝ) else if s = "p" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1134r28, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1134r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1134r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1212r76_counterexample_real : ¬ rubi1212r76.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1212r76.conditions rubi1212r76.body rubi1212r76.result rubi1212r76.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (1 : ℝ) else if s = "d" then (2 : ℝ) else if s = "e" then (-3 : ℝ) else if s = "m" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1212r76, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1212r76, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1212r76.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (1 : ℝ) else if s = "d" then (2 : ℝ) else if s = "e" then (-3 : ℝ) else if s = "m" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1212r76, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1212r76, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1212r76, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1213r34_counterexample_real : ¬ rubi1213r34.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1213r34.conditions rubi1213r34.body rubi1213r34.result rubi1213r34.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (1 : ℝ) else if s = "p" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1213r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1213r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1213r34.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "p" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1213r34, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1213r34, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1213r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1216r22_counterexample_real : ¬ rubi1216r22.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1216r22.conditions rubi1216r22.body rubi1216r22.result rubi1216r22.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (2 : ℝ) else if s = "e" then (1 : ℝ) else if s = "g" then (4 : ℝ) else if s = "p" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1216r22, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1216r22, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1216r22.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (2 : ℝ) else if s = "e" then (1 : ℝ) else if s = "g" then (4 : ℝ) else if s = "p" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1216r22, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1216r22, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1216r22, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1224r69_counterexample_real : ¬ rubi1224r69.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1224r69.conditions rubi1224r69.body rubi1224r69.result rubi1224r69.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "d" then (-1 : ℝ) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1224r69, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1224r69, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1224r69.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "d" then (-1 : ℝ) else if s = "m" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1224r69, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1224r69, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1224r69, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1234r35_counterexample_real : ¬ rubi1234r35.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1234r35.conditions rubi1234r35.body rubi1234r35.result rubi1234r35.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (-1 : ℝ) else if s = "d" then (4 : ℝ) else if s = "m" then (4 : ℝ) else if s = "n" then (2 : ℝ) else if s = "n2" then (4 : ℝ) else if s = "p" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1234r35, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1234r35, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1234r35.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (-1 : ℝ) else if s = "d" then (4 : ℝ) else if s = "m" then (4 : ℝ) else if s = "n" then (2 : ℝ) else if s = "n2" then (4 : ℝ) else if s = "p" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1234r35, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1234r35, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1234r35, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1232r14_counterexample_real : ¬ rubi1232r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1232r14.conditions rubi1232r14.body rubi1232r14.result rubi1232r14.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "b" then ((1 : ℝ) / 2) else if s = "m" then (3 : ℝ) else if s = "n" then (1 : ℝ) else if s = "n2" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1232r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1232r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1232r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "b" then ((1 : ℝ) / 2) else if s = "m" then (3 : ℝ) else if s = "n" then (1 : ℝ) else if s = "n2" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1232r14, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1232r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1232r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi133r27_counterexample_real : ¬ rubi133r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi133r27.conditions rubi133r27.body rubi133r27.result rubi133r27.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (4 : ℝ) else if s = "d" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi133r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi133r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi133r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (4 : ℝ) else if s = "d" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi133r27, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi133r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi133r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1114r12_counterexample_real : ¬ rubi1114r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1114r12.conditions rubi1114r12.body rubi1114r12.result rubi1114r12.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (-1 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1114r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1114r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1114r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (-1 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1114r12, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1114r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1114r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1136r10_counterexample_real : ¬ rubi1136r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1136r10.conditions rubi1136r10.body rubi1136r10.result rubi1136r10.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (-3 : ℝ) else if s = "d" then (3 : ℝ) else if s = "m" then (1 : ℝ) else if s = "n" then (1 : ℝ) else if s = "p" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1136r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1136r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1136r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (-3 : ℝ) else if s = "d" then (3 : ℝ) else if s = "m" then (1 : ℝ) else if s = "n" then (1 : ℝ) else if s = "p" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1136r10, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1136r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1136r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1134r27_counterexample_real : ¬ rubi1134r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1134r27.conditions rubi1134r27.body rubi1134r27.result rubi1134r27.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then ((-1 : ℝ) / 2) else if s = "c" then (-1 : ℝ) else if s = "e" then (1 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1134r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1134r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1134r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then ((-1 : ℝ) / 2) else if s = "c" then (-1 : ℝ) else if s = "e" then (1 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1134r27, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1134r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1134r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1233r26_counterexample_real : ¬ rubi1233r26.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1233r26.conditions rubi1233r26.body rubi1233r26.result rubi1233r26.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (-2 : ℝ) else if s = "p" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1233r26, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1233r26, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1233r26.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (-2 : ℝ) else if s = "p" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1233r26, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1233r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1233r26, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi1232r13_counterexample_real : ¬ rubi1232r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi1232r13.conditions rubi1232r13.body rubi1232r13.result rubi1232r13.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (1 : ℝ) else if s = "n" then (1 : ℝ) else if s = "n2" then (2 : ℝ) else if s = "p" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi1232r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi1232r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi1232r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (1 : ℝ) else if s = "n" then (1 : ℝ) else if s = "n2" then (2 : ℝ) else if s = "p" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi1232r13, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi1232r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi1232r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

end OSR.IntegrationRec170
