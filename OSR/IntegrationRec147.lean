import OSR.IntegrationRec91

/-!
# Integration (RUBI): reductions of `trig^n/(a + b trig)`

4.7.9 #17 to #20 and 6.7.9 #8, #16 to #18 split `(e + f x)^m F^n/(a + b G)` with
`sin² + cos² = 1` (or `cosh² - sinh² = 1`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec147

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 4.7.9 #17 -/
def rubi479r17 : CRule where
  id := "integration.rubi_4_7_9_r17"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.int 2))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 11814
  description := "RUBI 4.7.9 #17"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:17" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#17"

/-- RUBI 4.7.9 #18 -/
def rubi479r18 : CRule where
  id := "integration.rubi_4_7_9_r18"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csc (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csc (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.int 2))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csc (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.app1 .cot (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 11815
  description := "RUBI 4.7.9 #18"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:18" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#18"

/-- RUBI 4.7.9 #19 -/
def rubi479r19 : CRule where
  id := "integration.rubi_4_7_9_r19"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sec (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 11816
  description := "RUBI 4.7.9 #19"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:19" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#19"

/-- RUBI 4.7.9 #20 -/
def rubi479r20 : CRule where
  id := "integration.rubi_4_7_9_r20"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csc (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csc (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csc (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 11817
  description := "RUBI 4.7.9 #20"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:20" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#20"

/-- RUBI 6.7.9 #8 -/
def rubi679r8 : CRule where
  id := "integration.rubi_6_7_9_r8"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 1),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 11818
  description := "RUBI 6.7.9 #8"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:8" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#8"

/-- RUBI 6.7.9 #16 -/
def rubi679r16 : CRule where
  id := "integration.rubi_6_7_9_r16"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.int 2))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 11819
  description := "RUBI 6.7.9 #16"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:16" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#16"

/-- RUBI 6.7.9 #17 -/
def rubi679r17 : CRule where
  id := "integration.rubi_6_7_9_r17"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 11820
  description := "RUBI 6.7.9 #17"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:17" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#17"

/-- RUBI 6.7.9 #18 -/
def rubi679r18 : CRule where
  id := "integration.rubi_6_7_9_r18"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 11821
  description := "RUBI 6.7.9 #18"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:18" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#18"

/-! ## Proofs -/

theorem rubi479r17_real : rubi479r17.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r17.conditions rubi479r17.body rubi479r17.result rubi479r17.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi479r17, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi479r17, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hab : env "a" ^ 2 = env "b" ^ 2 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi479r17])
    simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at h
    linear_combination h
  have hD0 : env "a" + env "b" * Real.sin (env "c" + env "d" * t) ≠ 0 := by
    have h := hF.self_of_nhds
    simp [rubi479r17, Defined, eval, Interp.real, i2, im1, hk_m, hk_n] at h
    first | tauto | (trace_state; sorry)
  have ha : env "a" ≠ 0 := by
    intro h0; apply hD0; rw [h0] at hab ⊢; have : env "b" = 0 := by nlinarith
    rw [this]; ring
  have hb : env "b" ≠ 0 := by
    intro h0; apply hD0; rw [h0] at hab ⊢; have : env "a" = 0 := by nlinarith
    rw [this]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r17, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi479r17, Defined, eval, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢ <;>
    first | tauto | (refine ⟨?_, fun h => absurd h (by omega)⟩; tauto) | (simp only [(Real.cosh_pos _).ne', not_false_eq_true, implies_true, and_true, true_and] at hw ⊢; tauto) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi479r17, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi479r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi479r17, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add ((hΦ2.const_mul _).neg)) ?_
    have hrel := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    have hB : Real.cos (env "c" + env "d" * t) ≠ 0 := by first | assumption | tauto | (intro h; simp_all) | (trace_state; sorry)
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ht ⊢
    generalize Real.cos (env "c" + env "d" * t) ^ kn = P at *
    generalize (env "e" + env "f" * t) ^ km = M at *
    generalize Real.sin (env "c" + env "d" * t) = S at *
    generalize Real.cos (env "c" + env "d" * t) = C at *
    field_simp
    linear_combination (-M*env "a"*env "b"/P) * hrel + (-M*S/P) * hab

theorem rubi479r18_real : rubi479r18.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r18.conditions rubi479r18.body rubi479r18.result rubi479r18.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi479r18, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi479r18, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hab : env "a" ^ 2 = env "b" ^ 2 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi479r18])
    simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at h
    linear_combination h
  have hD0 : env "a" + env "b" * Real.cos (env "c" + env "d" * t) ≠ 0 := by
    have h := hF.self_of_nhds
    simp [rubi479r18, Defined, eval, Interp.real, i2, im1, hk_m, hk_n] at h
    first | tauto | (trace_state; sorry)
  have ha : env "a" ≠ 0 := by
    intro h0; apply hD0; rw [h0] at hab ⊢; have : env "b" = 0 := by nlinarith
    rw [this]; ring
  have hb : env "b" ≠ 0 := by
    intro h0; apply hD0; rw [h0] at hab ⊢; have : env "a" = 0 := by nlinarith
    rw [this]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r18, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi479r18, Defined, eval, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢ <;>
    first | tauto | (refine ⟨?_, fun h => absurd h (by omega)⟩; tauto) | (simp only [(Real.cosh_pos _).ne', not_false_eq_true, implies_true, and_true, true_and] at hw ⊢; tauto) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi479r18, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi479r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi479r18, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add ((hΦ2.const_mul _).neg)) ?_
    have hrel := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    have hB : Real.sin (env "c" + env "d" * t) ≠ 0 := by first | assumption | tauto | (intro h; simp_all) | (trace_state; sorry)
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ht ⊢
    generalize Real.sin (env "c" + env "d" * t) ^ kn = P at *
    generalize (env "e" + env "f" * t) ^ km = M at *
    generalize Real.sin (env "c" + env "d" * t) = S at *
    generalize Real.cos (env "c" + env "d" * t) = C at *
    field_simp
    linear_combination (-M*env "a"*env "b"/P) * hrel + (-C*M/P) * hab

theorem rubi479r19_real : rubi479r19.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r19.conditions rubi479r19.body rubi479r19.result rubi479r19.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi479r19, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi479r19, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hab : ¬ (env "a" ^ 2 + -env "b" ^ 2 = 0) := by
    have h := hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi479r19])
    simpa [Cond.Holds, Defined, eval, Interp.real, i2, im1] using h
  have hD0 : env "a" + env "b" * Real.sin (env "c" + env "d" * t) ≠ 0 := by
    have h := hF.self_of_nhds
    simp [rubi479r19, Defined, eval, Interp.real, i2, im1, hk_m, hk_n] at h
    first | tauto | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r19, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi479r19, Defined, eval, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢ <;>
    first | tauto | (refine ⟨?_, fun h => absurd h (by omega)⟩; tauto) | (simp only [(Real.cosh_pos _).ne', not_false_eq_true, implies_true, and_true, true_and] at hw ⊢; tauto) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi479r19, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi479r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi479r19, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add ((hΦ2.const_mul _).neg)) ?_
    have hrel := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    have hB : Real.cos (env "c" + env "d" * t) ≠ 0 := by first | assumption | tauto | (intro h; simp_all) | (trace_state; sorry)
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ht ⊢
    generalize Real.cos (env "c" + env "d" * t) ^ kn = P at *
    generalize (env "e" + env "f" * t) ^ km = M at *
    generalize Real.sin (env "c" + env "d" * t) = S at *
    generalize Real.cos (env "c" + env "d" * t) = C at *
    field_simp
    linear_combination (-M*env "b"^2/P) * hrel

theorem rubi479r20_real : rubi479r20.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi479r20.conditions rubi479r20.body rubi479r20.result rubi479r20.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi479r20, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi479r20, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hab : ¬ (env "a" ^ 2 + -env "b" ^ 2 = 0) := by
    have h := hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi479r20])
    simpa [Cond.Holds, Defined, eval, Interp.real, i2, im1] using h
  have hD0 : env "a" + env "b" * Real.cos (env "c" + env "d" * t) ≠ 0 := by
    have h := hF.self_of_nhds
    simp [rubi479r20, Defined, eval, Interp.real, i2, im1, hk_m, hk_n] at h
    first | tauto | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi479r20, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi479r20, Defined, eval, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢ <;>
    first | tauto | (refine ⟨?_, fun h => absurd h (by omega)⟩; tauto) | (simp only [(Real.cosh_pos _).ne', not_false_eq_true, implies_true, and_true, true_and] at hw ⊢; tauto) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi479r20, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi479r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi479r20, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sec, Fn.csc, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add ((hΦ2.const_mul _).neg)) ?_
    have hrel := Real.sin_sq_add_cos_sq (env "c" + env "d" * t)
    have hB : Real.sin (env "c" + env "d" * t) ≠ 0 := by first | assumption | tauto | (intro h; simp_all) | (trace_state; sorry)
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ht ⊢
    generalize Real.sin (env "c" + env "d" * t) ^ kn = P at *
    generalize (env "e" + env "f" * t) ^ km = M at *
    generalize Real.sin (env "c" + env "d" * t) = S at *
    generalize Real.cos (env "c" + env "d" * t) = C at *
    field_simp
    linear_combination (-M*env "b"^2/P) * hrel

theorem rubi679r8_real : rubi679r8.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r8.conditions rubi679r8.body rubi679r8.result rubi679r8.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r8, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r8, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hab : env "a" ^ 2 = env "b" ^ 2 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi679r8])
    simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at h
    linear_combination h
  have hD0 : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) ≠ 0 := by
    have h := hF.self_of_nhds
    simp [rubi679r8, Defined, eval, Interp.real, i2, im1, hk_m, hk_n] at h
    first | tauto | (trace_state; sorry)
  have ha : env "a" ≠ 0 := by
    intro h0; apply hD0; rw [h0] at hab ⊢; have : env "b" = 0 := by nlinarith
    rw [this]; ring
  have hb : env "b" ≠ 0 := by
    intro h0; apply hD0; rw [h0] at hab ⊢; have : env "a" = 0 := by nlinarith
    rw [this]; ring
  have hn1 : 1 < kn := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi679r8])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.real] at h
    exact_mod_cast h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r8, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r8, Defined, eval, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢ <;>
    first | tauto | (refine ⟨?_, fun h => absurd h (by omega)⟩; tauto) | (simp only [(Real.cosh_pos _).ne', not_false_eq_true, implies_true, and_true, true_and] at hw ⊢; tauto) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi679r8, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi679r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi679r8, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add ((hΦ2.const_mul _).neg)) ?_
    have hrel := Real.cosh_sq_sub_sinh_sq (env "c" + env "d" * t)
    have hCne : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ kn - 2)
    have e1 : Real.sinh (env "c" + env "d" * t) ^ (kn - 2) = Real.sinh (env "c" + env "d" * t) ^ j := by rw [hj, zpow_natCast]
    have e2 : Real.sinh (env "c" + env "d" * t) ^ kn = Real.sinh (env "c" + env "d" * t) ^ j * Real.sinh (env "c" + env "d" * t) ^ 2 := by
      rw [show kn = ((j + 2 : ℕ) : ℤ) by omega, zpow_natCast, pow_add]
    rw [e1, e2]
    generalize Real.sinh (env "c" + env "d" * t) ^ j = P
    generalize (env "e" + env "f" * t) ^ km = M at *
    generalize Real.sinh (env "c" + env "d" * t) = S at *
    generalize Real.cosh (env "c" + env "d" * t) = C at *
    field_simp
    linear_combination (M*P*env "a"*env "b") * hrel + (C*M*P) * hab

theorem rubi679r8_complex : rubi679r8.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r8.conditions rubi679r8.body rubi679r8.result rubi679r8.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r8, Defined, eval, Interp.complex, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r8, Defined, eval, Interp.complex, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℂ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hab : env "a" ^ 2 = env "b" ^ 2 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi679r8])
    simp [Cond.Holds, Defined, eval, Interp.complex, i2, im1] at h
    linear_combination h
  have hD0 : env "a" + env "b" * Complex.cosh (env "c" + env "d" * t) ≠ 0 := by
    have h := hF.self_of_nhds
    simp [rubi679r8, Defined, eval, Interp.complex, i2, im1, hk_m, hk_n] at h
    first | tauto | (trace_state; sorry)
  have ha : env "a" ≠ 0 := by
    intro h0; apply hD0; rw [h0] at hab ⊢; have : env "b" = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by rw [← hab]; ring)
    rw [this]; ring
  have hb : env "b" ≠ 0 := by
    intro h0; apply hD0; rw [h0] at hab ⊢; have : env "a" = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by rw [hab]; ring)
    rw [this]; ring
  have hn1 : 1 < kn := by
    have h := hc (.gt (.var "n") (.int 1)) (by simp [rubi679r8])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2 | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r8, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r8, Defined, eval, Interp.complex, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢ <;>
    first | tauto | (refine ⟨?_, fun h => absurd h (by omega)⟩; tauto) | (simp only [(Complex.cosh_pos _).ne', not_false_eq_true, implies_true, and_true, true_and] at hw ⊢; tauto) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi679r8, Defined, eval, recEnv, Interp.complex, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi679r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi679r8, Defined, eval, recEnv, Interp.complex, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add ((hΦ2.const_mul _).neg)) ?_
    have hrel := Complex.cosh_sq_sub_sinh_sq (env "c" + env "d" * t)
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ kn - 2)
    have e1 : Complex.sinh (env "c" + env "d" * t) ^ (kn - 2) = Complex.sinh (env "c" + env "d" * t) ^ j := by rw [hj, zpow_natCast]
    have e2 : Complex.sinh (env "c" + env "d" * t) ^ kn = Complex.sinh (env "c" + env "d" * t) ^ j * Complex.sinh (env "c" + env "d" * t) ^ 2 := by
      rw [show kn = ((j + 2 : ℕ) : ℤ) by omega, zpow_natCast, pow_add]
    rw [e1, e2]
    generalize Complex.sinh (env "c" + env "d" * t) ^ j = P
    generalize (env "e" + env "f" * t) ^ km = M at *
    generalize Complex.sinh (env "c" + env "d" * t) = S at *
    generalize Complex.cosh (env "c" + env "d" * t) = C at *
    field_simp
    linear_combination (M*P*env "a"*env "b") * hrel + (C*M*P) * hab

theorem rubi679r16_real : rubi679r16.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r16.conditions rubi679r16.body rubi679r16.result rubi679r16.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r16, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r16, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hab : env "a" ^ 2 = env "b" ^ 2 := by
    have h := hc (.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi679r16])
    simp [Cond.Holds, Defined, eval, Interp.real, i2, im1] at h
    linear_combination h
  have hD0 : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) ≠ 0 := by
    have h := hF.self_of_nhds
    simp [rubi679r16, Defined, eval, Interp.real, i2, im1, hk_m, hk_n] at h
    first | tauto | (trace_state; sorry)
  have ha : env "a" ≠ 0 := by
    intro h0; apply hD0; rw [h0] at hab ⊢; have : env "b" = 0 := by nlinarith
    rw [this]; ring
  have hb : env "b" ≠ 0 := by
    intro h0; apply hD0; rw [h0] at hab ⊢; have : env "a" = 0 := by nlinarith
    rw [this]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r16, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r16, Defined, eval, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢ <;>
    first | tauto | (refine ⟨?_, fun h => absurd h (by omega)⟩; tauto) | (simp only [(Real.cosh_pos _).ne', not_false_eq_true, implies_true, and_true, true_and] at hw ⊢; tauto) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi679r16, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi679r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi679r16, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add ((hΦ2.const_mul _).neg)) ?_
    have hrel := Real.cosh_sq_sub_sinh_sq (env "c" + env "d" * t)
    have hCne : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hB : Real.sinh (env "c" + env "d" * t) ≠ 0 := by first | assumption | tauto | (intro h; simp_all) | (trace_state; sorry)
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ht ⊢
    generalize Real.sinh (env "c" + env "d" * t) ^ kn = P at *
    generalize (env "e" + env "f" * t) ^ km = M at *
    generalize Real.sinh (env "c" + env "d" * t) = S at *
    generalize Real.cosh (env "c" + env "d" * t) = C at *
    field_simp
    linear_combination (M*env "a"*env "b"/P) * hrel + (C*M/P) * hab

theorem rubi679r17_real : rubi679r17.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r17.conditions rubi679r17.body rubi679r17.result rubi679r17.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r17, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r17, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hab : ¬ (env "a" ^ 2 + env "b" ^ 2 = 0) := by
    have h := hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)) (by simp [rubi679r17])
    simpa [Cond.Holds, Defined, eval, Interp.real, i2, im1] using h
  have hD0 : env "a" + env "b" * Real.sinh (env "c" + env "d" * t) ≠ 0 := by
    have h := hF.self_of_nhds
    simp [rubi679r17, Defined, eval, Interp.real, i2, im1, hk_m, hk_n] at h
    first | tauto | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r17, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r17, Defined, eval, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢ <;>
    first | tauto | (refine ⟨?_, fun h => absurd h (by omega)⟩; tauto) | (simp only [(Real.cosh_pos _).ne', not_false_eq_true, implies_true, and_true, true_and] at hw ⊢; tauto) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi679r17, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi679r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi679r17, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add ((hΦ2.const_mul _).neg)) ?_
    have hrel := Real.cosh_sq_sub_sinh_sq (env "c" + env "d" * t)
    have hCne : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hB : Real.cosh (env "c" + env "d" * t) ≠ 0 := by first | assumption | tauto | (intro h; simp_all) | (trace_state; sorry)
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ht ⊢
    generalize Real.cosh (env "c" + env "d" * t) ^ kn = P at *
    generalize (env "e" + env "f" * t) ^ km = M at *
    generalize Real.sinh (env "c" + env "d" * t) = S at *
    generalize Real.cosh (env "c" + env "d" * t) = C at *
    field_simp
    linear_combination (M*env "b"^2/P) * hrel

theorem rubi679r18_real : rubi679r18.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r18.conditions rubi679r18.body rubi679r18.result rubi679r18.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r18, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r18, Defined, eval, Interp.real, hk_m, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n1 : intValue? (env "n" + 1) = some (kn + 1) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n2 : intValue? (env "n" + 2) = some (kn + 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n3 : intValue? (env "n" + -2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n4 : intValue? (env "n" - 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have n5 : intValue? (env "n" + -1 * 2) = some (kn - 2) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hab : ¬ (env "a" ^ 2 + -env "b" ^ 2 = 0) := by
    have h := hc (.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)) (by simp [rubi679r18])
    simpa [Cond.Holds, Defined, eval, Interp.real, i2, im1] using h
  have hD0 : env "a" + env "b" * Real.cosh (env "c" + env "d" * t) ≠ 0 := by
    have h := hF.self_of_nhds
    simp [rubi679r18, Defined, eval, Interp.real, i2, im1, hk_m, hk_n] at h
    first | tauto | (trace_state; sorry)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r18, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r18, Defined, eval, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢ <;>
    first | tauto | (refine ⟨?_, fun h => absurd h (by omega)⟩; tauto) | (simp only [(Real.cosh_pos _).ne', not_false_eq_true, implies_true, and_true, true_and] at hw ⊢; tauto) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi679r18, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at hw ⊢
    first | tauto | (trace_state; sorry)
  · simp only [rubi679r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have ht := hF.self_of_nhds
    simp [rubi679r18, Defined, eval, recEnv, Interp.real, i2, im1, hk_m, hk_n, n1, n2, n3, n4, n5, Fn.sech, Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh] at ht hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add ((hΦ2.const_mul _).neg)) ?_
    have hrel := Real.cosh_sq_sub_sinh_sq (env "c" + env "d" * t)
    have hCne : Real.cosh (env "c" + env "d" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hB : Real.sinh (env "c" + env "d" * t) ≠ 0 := by first | assumption | tauto | (intro h; simp_all) | (trace_state; sorry)
    simp only [zpow_add₀ hB, zpow_sub₀ hB, zpow_neg, zpow_ofNat, zpow_one] at ht ⊢
    generalize Real.sinh (env "c" + env "d" * t) ^ kn = P at *
    generalize (env "e" + env "f" * t) ^ km = M at *
    generalize Real.sinh (env "c" + env "d" * t) = S at *
    generalize Real.cosh (env "c" + env "d" * t) = C at *
    field_simp
    linear_combination (-M*env "b"^2/P) * hrel

end OSR.IntegrationRec147
