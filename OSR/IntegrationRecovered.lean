import OSR.IntegrationRec120
import OSR.IntegrationRec13
import OSR.IntegrationRec163
import OSR.IntegrationRec196

/-! RUBI entries from the default source profile. The original mathematical
conditions are retained. Catalogue membership and proof status are independent. -/

namespace OSR.IntegrationRecovered
open Calculus

private def source (legacy locator revision : String) : Provenance :=
  { method := .derived, sources := [
    { name := "OpenSymbolicRules/Integration", locator := legacy,
      revision := some "155e92f4dd42b84291dcd3516f4b932857923b98", license := some "MIT" },
    { name := "Rubi", locator, revision := some revision, license := some "MIT" }] }

private abbrev v (s : String) : Expr := .var s
private abbrev z (n : Int) : Expr := .int n
private abbrev add (a b : Expr) : Expr := .app2 .add a b
private abbrev mul (a b : Expr) : Expr := .app2 .mul a b
private abbrev pow (a b : Expr) : Expr := .pow a b
private abbrev root (a b : Expr) : Expr := .app2 .root a b

/-- RUBI 1.1.1.2, source rule 22 (OSR legacy ID). -/
def rubi_1_1_1_2_r22 : CRule where
  id := "integration.source_1_1_1_2_r22"
  legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:22"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (v "x"))) (z 2)) (root (add (v "c") (mul (v
    "d") (v "x"))) (z 2))) (z (-1))))
  result := (v "osrIntegral1")
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (add (mul (v "a") (v "c")) (mul (mul (mul (z (-1))
    (v "b")) (add (v "a") (mul (z (-1)) (v "c")))) (v "x"))) (mul (mul (z (-1)) (pow (v "b") (z 2))) (pow (v
    "x") (z 2)))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.eq (add (v "b") (v "d")) (z 0)), (.gt (add (v "a") (v "c")) (z 0))]
  priority := 100027
  description := "RUBI 1.1.1.2, source rule 22 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:22"
    "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.m#22" "4.16.1"

/-- RUBI 1.1.1.2, source rule 23 (OSR legacy ID). -/
def rubi_1_1_1_2_r23 : CRule where
  id := "integration.source_1_1_1_2_r23"
  legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:23"
  x := "x"
  shape := .antiderivSubst
  body := (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (v "x"))) (z 2)) (root (add (v "c") (mul (v
    "d") (v "x"))) (z 2))) (z (-1))))
  result := (mul (mul (z 2) (pow (root (v "b") (z 2)) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v
    "a")) (v "d"))) (mul (v "d") (pow (v "x") (z 2)))) (z 2)) (z (-1)))))]
  substs := [("osrIntegral1", (root (add (v "a") (mul (v "b") (v "x"))) (z 2)))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.gt (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.gt (v "b") (z
    0))]
  priority := 100028
  description := "RUBI 1.1.1.2, source rule 23 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n:23"
    "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.2 (a+b x)^m (c+d x)^n.m#23" "4.16.1"

/-- RUBI 1.1.1.4, source rule 28 (OSR legacy ID). -/
def rubi_1_1_1_4_r28 : CRule where
  id := "integration.source_1_1_1_4_r28"
  legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:28"
  x := "x"
  shape := .antiderivSubst
  body := (mul (z 1) (pow (mul (mul (mul (add (v "a") (mul (v "b") (v "x"))) (root (add (v "c") (mul (v "d")
    (v "x"))) (z 2))) (root (add (v "e") (mul (v "f") (v "x"))) (z 2))) (root (add (v "g") (mul (v "h") (v
    "x"))) (z 2))) (z (-1))))
  result := (mul (z (-2)) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (mul (mul (add (add (mul (v "b") (v "c")) (mul (mul (z (-1))
    (v "a")) (v "d"))) (mul (mul (z (-1)) (v "b")) (pow (v "x") (z 2)))) (root (add (mul (add (mul (v "d") (v
    "e")) (mul (mul (z (-1)) (v "c")) (v "f"))) (pow (v "d") (z (-1)))) (mul (mul (v "f") (pow (v "x") (z 2)))
    (pow (v "d") (z (-1))))) (z 2))) (root (add (mul (add (mul (v "d") (v "g")) (mul (mul (z (-1)) (v "c")) (v
    "h"))) (pow (v "d") (z (-1)))) (mul (mul (v "h") (pow (v "x") (z 2))) (pow (v "d") (z (-1))))) (z 2))) (z
    (-1)))))]
  substs := [("osrIntegral1", (root (add (v "c") (mul (v "d") (v "x"))) (z 2)))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h"]
  conditions := [(.gt (mul (add (mul (v "d") (v "e")) (mul (mul (z (-1)) (v "c")) (v "f"))) (pow (v "d") (z
    (-1)))) (z 0))]
  priority := 100146
  description := "RUBI 1.1.1.4, source rule 28 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:28"
    "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#28" "4.16.1"

/-- RUBI 1.1.2.1, source rule 19 (OSR legacy ID). -/
def rubi_1_1_2_1_r19 : CRule := { OSR.IntegrationRec196.rubi1131r21 with
  id := "integration.source_1_1_2_1_r19"
  legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.1 (a+b x^2)^p:19"
  priority := 100184
  description := "RUBI 1.1.2.1, source rule 19 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.1 (a+b x^2)^p:19"
    "1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.1 (a+b x^2)^p.m#18" "61e9c18ea248061cd83c67882f7c91a73cef912d" }

theorem rubi_1_1_2_1_r19_counterexample_real : ¬ rubi_1_1_2_1_r19.Holds .real :=
  OSR.IntegrationRec196.rubi1131r21_counterexample_real

/-- RUBI 1.1.2.3, source rule 29 (OSR legacy ID). -/
def rubi_1_1_2_3_r29 : CRule where
  id := "integration.source_1_1_2_3_r29"
  legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.3 (a+b x^2)^p (c+d x^2)^q:29"
  x := "x"
  shape := .antiderivSubst
  body := (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (pow (v "x") (z 2)))) (z 2)) (add (v "c") (mul
    (v "d") (pow (v "x") (z 2))))) (z (-1))))
  result := (v "osrIntegral1")
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (v "c") (mul (mul (z (-1)) (add (mul (v "b") (v "c"))
    (mul (mul (z (-1)) (v "a")) (v "d")))) (pow (v "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (v "x") (pow (root (add (v "a") (mul (v "b") (pow (v "x") (z 2)))) (z 2))
    (z (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0))]
  priority := 100251
  description := "RUBI 1.1.2.3, source rule 29 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.3 (a+b x^2)^p (c+d x^2)^q:29"
    "1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.3 (a+b x^2)^p (c+d x^2)^q.m#12" "61e9c18ea248061cd83c67882f7c91a73cef912d"

/-- RUBI 1.1.2.7, source rule 47 (OSR legacy ID). -/
def rubi_1_1_2_7_r47 : CRule where
  id := "integration.source_1_1_2_7_r47"
  legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.7 (c+d x)^n (a+b x^2)^p:47"
  x := "x"
  shape := .antiderivSubst
  body := (mul (z 1) (pow (mul (add (v "c") (mul (v "d") (v "x"))) (root (add (v "a") (mul (v "b") (pow (v
    "x") (z 2)))) (z 2))) (z (-1))))
  result := (mul (z (-1)) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (add (mul (v "b") (pow (v "c") (z 2))) (mul (v "a") (pow
    (v "d") (z 2)))) (mul (z (-1)) (pow (v "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (add (mul (v "a") (v "d")) (mul (mul (mul (z (-1)) (v "b")) (v "c")) (v
    "x"))) (pow (root (add (v "a") (mul (v "b") (pow (v "x") (z 2)))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d"]
  priority := 100458
  description := "RUBI 1.1.2.7, source rule 47 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.7 (c+d x)^n (a+b x^2)^p:47"
    "1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.7 (c+d x)^n (a+b x^2)^p.m#38" "61e9c18ea248061cd83c67882f7c91a73cef912d"

/-- RUBI 1.1.2.9, source rule 36 (OSR legacy ID). -/
def rubi_1_1_2_9_r36 : CRule := { OSR.IntegrationRec13.rubi1213r14 with
  id := "integration.source_1_1_2_9_r36"
  legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.9 (c+d x)^m (e+f x)^n (a+b x^2)^p:36"
  priority := 100641
  description := "RUBI 1.1.2.9, source rule 36 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.9 (c+d x)^m (e+f x)^n (a+b x^2)^p:36"
    "1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.9 (c+d x)^m (e+f x)^n (a+b x^2)^p.m#36" "61e9c18ea248061cd83c67882f7c91a73cef912d" }

theorem rubi_1_1_2_9_r36_counterexample_real : ¬ rubi_1_1_2_9_r36.Holds .real :=
  OSR.IntegrationRec13.rubi1213r14_counterexample_real

theorem rubi_1_1_2_9_r36_counterexample_complex : ¬ rubi_1_1_2_9_r36.Holds .complex :=
  OSR.IntegrationRec13.rubi1213r14_counterexample_complex

/-- RUBI 1.2.1.1, source rule 12 (OSR legacy ID). -/
def rubi_1_2_1_1_r12 : CRule where
  id := "integration.source_1_2_1_1_r12"
  legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:12"
  x := "x"
  shape := .antiderivSubst
  body := (mul (z 1) (pow (root (add (add (v "a") (mul (v "b") (v "x"))) (mul (v "c") (pow (v "x") (z 2)))) (z
    2)) (z (-1))))
  result := (mul (z 2) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (mul (z 4) (v "c")) (mul (z (-1)) (pow (v "x") (z 2))))
    (z (-1)))))]
  substs := [("osrIntegral1", (mul (add (v "b") (mul (mul (z 2) (v "c")) (v "x"))) (pow (root (add (add (v
    "a") (mul (v "b") (v "x"))) (mul (v "c") (pow (v "x") (z 2)))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c"]
  conditions := [(.ne (add (pow (v "b") (z 2)) (mul (mul (mul (z (-1)) (z 4)) (v "a")) (v "c"))) (z 0))]
  priority := 101144
  description := "RUBI 1.2.1.1, source rule 12 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:12"
    "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p.m#12" "4.16.1"

/-- RUBI 1.2.1.2, source rule 97 (OSR legacy ID). -/
def rubi_1_2_1_2_r97 : CRule where
  id := "integration.source_1_2_1_2_r97"
  legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:97"
  x := "x"
  shape := .antiderivSubst
  body := (mul (z 1) (pow (mul (add (v "d") (mul (v "e") (v "x"))) (root (add (add (v "a") (mul (v "b") (v
    "x"))) (mul (v "c") (pow (v "x") (z 2)))) (z 2))) (z (-1))))
  result := (mul (z (-2)) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (add (add (mul (mul (z 4) (v "c")) (pow (v "d") (z 2)))
    (mul (mul (mul (mul (z (-1)) (z 4)) (v "b")) (v "d")) (v "e"))) (mul (mul (z 4) (v "a")) (pow (v "e") (z
    2)))) (mul (z (-1)) (pow (v "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (add (add (mul (mul (z 2) (v "a")) (v "e")) (mul (mul (z (-1)) (v "b")) (v
    "d"))) (mul (mul (z (-1)) (add (mul (mul (z 2) (v "c")) (v "d")) (mul (mul (z (-1)) (v "b")) (v "e")))) (v
    "x"))) (pow (root (add (add (v "a") (mul (v "b") (v "x"))) (mul (v "c") (pow (v "x") (z 2)))) (z 2)) (z
    (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [(.ne (add (pow (v "b") (z 2)) (mul (mul (mul (z (-1)) (z 4)) (v "a")) (v "c"))) (z 0)), (.ne
    (add (mul (mul (z 2) (v "c")) (v "d")) (mul (mul (z (-1)) (v "b")) (v "e"))) (z 0))]
  priority := 101245
  description := "RUBI 1.2.1.2, source rule 97 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:97"
    "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#97" "4.16.1"

/-- RUBI 1.2.1.3, source rule 5 (OSR legacy ID). -/
def rubi_1_2_1_3_r5 : CRule := { OSR.IntegrationRec13.rubi1213r5 with
  id := "integration.source_1_2_1_3_r5"
  legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:5"
  priority := 101288
  description := "RUBI 1.2.1.3, source rule 5 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p:5"
    "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p.m#5" "61e9c18ea248061cd83c67882f7c91a73cef912d" }

theorem rubi_1_2_1_3_r5_counterexample_real : ¬ rubi_1_2_1_3_r5.Holds .real :=
  OSR.IntegrationRec13.rubi1213r5_counterexample_real

theorem rubi_1_2_1_3_r5_counterexample_complex : ¬ rubi_1_2_1_3_r5.Holds .complex :=
  OSR.IntegrationRec13.rubi1213r5_counterexample_complex

/-- RUBI 1.2.2.3, source rule 34 (OSR legacy ID). -/
def rubi_1_2_2_3_r34 : CRule where
  id := "integration.source_1_2_2_3_r34"
  legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:34"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (root (add (add (v "a") (mul (v
    "b") (pow (v "x") (z 2)))) (mul (v "c") (pow (v "x") (z 4)))) (z 2))) (z (-1))))
  result := (add (mul (mul (z 1) (pow (mul (z 2) (v "d")) (z (-1)))) (v "osrIntegral1")) (mul (mul (z 1) (pow
    (mul (z 2) (v "d")) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (add (v "a") (mul (v "b") (pow (v "x") (z 2))))
    (mul (v "c") (pow (v "x") (z 4)))) (z 2)) (z (-1))))), ("osrIntegral2", (mul (add (v "d") (mul (mul (z
    (-1)) (v "e")) (pow (v "x") (z 2)))) (pow (mul (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (root (add
    (add (v "a") (mul (v "b") (pow (v "x") (z 2)))) (mul (v "c") (pow (v "x") (z 4)))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [(.ne (add (pow (v "b") (z 2)) (mul (mul (mul (z (-1)) (z 4)) (v "a")) (v "c"))) (z 0)), (.ne
    (add (add (mul (v "c") (pow (v "d") (z 2))) (mul (mul (mul (z (-1)) (v "b")) (v "d")) (v "e"))) (mul (v
    "a") (pow (v "e") (z 2)))) (z 0)), (.eq (add (mul (v "c") (pow (v "d") (z 2))) (mul (mul (z (-1)) (v "a"))
    (pow (v "e") (z 2)))) (z 0))]
  priority := 101570
  description := "RUBI 1.2.2.3, source rule 34 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:34"
    "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#34" "4.16.1"

/-- RUBI 1.2.2.3, source rule 35 (OSR legacy ID). -/
def rubi_1_2_2_3_r35 : CRule where
  id := "integration.source_1_2_2_3_r35"
  legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:35"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (root (add (v "a") (mul (v "c")
    (pow (v "x") (z 4)))) (z 2))) (z (-1))))
  result := (add (mul (mul (z 1) (pow (mul (z 2) (v "d")) (z (-1)))) (v "osrIntegral1")) (mul (mul (z 1) (pow
    (mul (z 2) (v "d")) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (v "a") (mul (v "c") (pow (v "x") (z 4)))) (z 2))
    (z (-1))))), ("osrIntegral2", (mul (add (v "d") (mul (mul (z (-1)) (v "e")) (pow (v "x") (z 2)))) (pow
    (mul (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (root (add (v "a") (mul (v "c") (pow (v "x") (z 4))))
    (z 2))) (z (-1)))))]
  independent := ["a", "c", "d", "e"]
  conditions := [(.ne (add (mul (v "c") (pow (v "d") (z 2))) (mul (v "a") (pow (v "e") (z 2)))) (z 0)), (.eq
    (add (mul (v "c") (pow (v "d") (z 2))) (mul (mul (z (-1)) (v "a")) (pow (v "e") (z 2)))) (z 0))]
  priority := 101571
  description := "RUBI 1.2.2.3, source rule 35 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:35"
    "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#35" "4.16.1"

/-- RUBI 1.4.1, source rule 26 (OSR legacy ID). -/
def rubi_1_4_1_r26 : CRule := { OSR.IntegrationRec13.rubi1117r6 with
  id := "integration.source_1_4_1_r26"
  legacyId := some "rubi:1 Algebraic functions/1.4 Miscellaneous/1.4.1 Algebraic function simplification:26"
  priority := 102050
  description := "RUBI 1.4.1, source rule 26 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.4 Miscellaneous/1.4.1 Algebraic function simplification:26"
    "1 Algebraic functions/1.4 Miscellaneous/1.4.1 Algebraic function simplification.m#26" "61e9c18ea248061cd83c67882f7c91a73cef912d" }

theorem rubi_1_4_1_r26_counterexample_real : ¬ rubi_1_4_1_r26.Holds .real :=
  OSR.IntegrationRec13.rubi1117r6_counterexample_real

theorem rubi_1_4_1_r26_counterexample_complex : ¬ rubi_1_4_1_r26.Holds .complex :=
  OSR.IntegrationRec13.rubi1117r6_counterexample_complex

/-- RUBI 1.2.2.7, source rule 10 (OSR legacy ID). -/
def rubi_1_2_2_7_r10 : CRule where
  id := "integration.source_1_2_2_7_r10"
  legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p:10"
  x := "x"
  shape := .antiderivSubst
  body := (mul (add (v "A") (mul (v "B") (pow (v "x") (z 2)))) (pow (mul (add (v "d") (mul (v "e") (pow (v
    "x") (z 2)))) (root (add (v "a") (mul (v "c") (pow (v "x") (z 4)))) (z 2))) (z (-1))))
  result := (mul (v "A") (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (v "d") (mul (mul (mul (z 2) (v "a")) (v "e")) (pow (v
    "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (v "x") (pow (root (add (v "a") (mul (v "c") (pow (v "x") (z 4)))) (z 2))
    (z (-1)))))]
  independent := ["A", "B", "a", "c", "d", "e"]
  conditions := [(.ne (add (mul (v "c") (pow (v "d") (z 2))) (mul (v "a") (pow (v "e") (z 2)))) (z 0)), (.eq
    (add (mul (v "c") (pow (v "d") (z 2))) (mul (mul (z (-1)) (v "a")) (pow (v "e") (z 2)))) (z 0)), (.eq (add
    (mul (v "B") (v "d")) (mul (v "A") (v "e"))) (z 0))]
  priority := 102269
  description := "RUBI 1.2.2.7, source rule 10 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p:10"
    "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p.m#10" "4.16.1"

/-- RUBI 1.2.2.7, source rule 11 (OSR legacy ID). -/
def rubi_1_2_2_7_r11 : CRule where
  id := "integration.source_1_2_2_7_r11"
  legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p:11"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "A") (mul (v "B") (pow (v "x") (z 2)))) (pow (mul (add (v "d") (mul (v "e") (pow (v
    "x") (z 2)))) (root (add (add (v "a") (mul (v "b") (pow (v "x") (z 2)))) (mul (v "c") (pow (v "x") (z
    4)))) (z 2))) (z (-1))))
  result := (add (mul (mul (add (mul (v "B") (v "d")) (mul (v "A") (v "e"))) (pow (mul (mul (z 2) (v "d")) (v
    "e")) (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (add (mul (v "B") (v "d")) (mul (mul (z (-1))
    (v "A")) (v "e")))) (pow (mul (mul (z 2) (v "d")) (v "e")) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (add (v "a") (mul (v "b") (pow (v "x") (z 2))))
    (mul (v "c") (pow (v "x") (z 4)))) (z 2)) (z (-1))))), ("osrIntegral2", (mul (add (v "d") (mul (mul (z
    (-1)) (v "e")) (pow (v "x") (z 2)))) (pow (mul (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (root (add
    (add (v "a") (mul (v "b") (pow (v "x") (z 2)))) (mul (v "c") (pow (v "x") (z 4)))) (z 2))) (z (-1)))))]
  independent := ["A", "B", "a", "b", "c", "d", "e"]
  conditions := [(.ne (add (pow (v "b") (z 2)) (mul (mul (mul (z (-1)) (z 4)) (v "a")) (v "c"))) (z 0)), (.ne
    (add (add (mul (v "c") (pow (v "d") (z 2))) (mul (mul (mul (z (-1)) (v "b")) (v "d")) (v "e"))) (mul (v
    "a") (pow (v "e") (z 2)))) (z 0)), (.eq (add (mul (v "c") (pow (v "d") (z 2))) (mul (mul (z (-1)) (v "a"))
    (pow (v "e") (z 2)))) (z 0)), (.ne (add (mul (v "B") (v "d")) (mul (v "A") (v "e"))) (z 0))]
  priority := 102270
  description := "RUBI 1.2.2.7, source rule 11 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p:11"
    "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p.m#11" "4.16.1"

/-- RUBI 1.2.2.7, source rule 12 (OSR legacy ID). -/
def rubi_1_2_2_7_r12 : CRule where
  id := "integration.source_1_2_2_7_r12"
  legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p:12"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "A") (mul (v "B") (pow (v "x") (z 2)))) (pow (mul (add (v "d") (mul (v "e") (pow (v
    "x") (z 2)))) (root (add (v "a") (mul (v "c") (pow (v "x") (z 4)))) (z 2))) (z (-1))))
  result := (add (mul (mul (add (mul (v "B") (v "d")) (mul (v "A") (v "e"))) (pow (mul (mul (z 2) (v "d")) (v
    "e")) (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (add (mul (v "B") (v "d")) (mul (mul (z (-1))
    (v "A")) (v "e")))) (pow (mul (mul (z 2) (v "d")) (v "e")) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (v "a") (mul (v "c") (pow (v "x") (z 4)))) (z 2))
    (z (-1))))), ("osrIntegral2", (mul (add (v "d") (mul (mul (z (-1)) (v "e")) (pow (v "x") (z 2)))) (pow
    (mul (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (root (add (v "a") (mul (v "c") (pow (v "x") (z 4))))
    (z 2))) (z (-1)))))]
  independent := ["A", "B", "a", "c", "d", "e"]
  conditions := [(.ne (add (mul (v "c") (pow (v "d") (z 2))) (mul (v "a") (pow (v "e") (z 2)))) (z 0)), (.eq
    (add (mul (v "c") (pow (v "d") (z 2))) (mul (mul (z (-1)) (v "a")) (pow (v "e") (z 2)))) (z 0)), (.ne (add
    (mul (v "B") (v "d")) (mul (v "A") (v "e"))) (z 0))]
  priority := 102271
  description := "RUBI 1.2.2.7, source rule 12 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p:12"
    "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.7 P(x) (d+e x^2)^q (a+b x^2+c x^4)^p.m#12" "4.16.1"

/-- RUBI 1.4.3, source rule 12 (OSR legacy ID). -/
def rubi_1_4_3_r12 : CRule := { OSR.IntegrationRec120.rubi133r7 with
  id := "integration.source_1_4_3_r12"
  legacyId := some "rubi:1 Algebraic functions/1.4 Miscellaneous/1.4.3 Miscellaneous algebraic functions:12"
  priority := 102580
  description := "RUBI 1.4.3, source rule 12 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.4 Miscellaneous/1.4.3 Miscellaneous algebraic functions:12"
    "1 Algebraic functions/1.4 Miscellaneous/1.4.3 Miscellaneous algebraic functions.m#12" "61e9c18ea248061cd83c67882f7c91a73cef912d" }

theorem rubi_1_4_3_r12_counterexample_real : ¬ rubi_1_4_3_r12.Holds .real :=
  OSR.IntegrationRec120.rubi133r7_counterexample_real

/-- RUBI 1.4.3, source rule 29 (OSR legacy ID). -/
def rubi_1_4_3_r29 : CRule := { OSR.IntegrationRec120.rubi133r22 with
  id := "integration.source_1_4_3_r29"
  legacyId := some "rubi:1 Algebraic functions/1.4 Miscellaneous/1.4.3 Miscellaneous algebraic functions:29"
  priority := 102595
  description := "RUBI 1.4.3, source rule 29 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.4 Miscellaneous/1.4.3 Miscellaneous algebraic functions:29"
    "1 Algebraic functions/1.4 Miscellaneous/1.4.3 Miscellaneous algebraic functions.m#29" "61e9c18ea248061cd83c67882f7c91a73cef912d" }

theorem rubi_1_4_3_r29_counterexample_real : ¬ rubi_1_4_3_r29.Holds .real :=
  OSR.IntegrationRec120.rubi133r22_counterexample_real

/-- RUBI 1.4.3, source rule 31 (OSR legacy ID). -/
def rubi_1_4_3_r31 : CRule := { OSR.IntegrationRec163.rubi133r24 with
  id := "integration.source_1_4_3_r31"
  legacyId := some "rubi:1 Algebraic functions/1.4 Miscellaneous/1.4.3 Miscellaneous algebraic functions:31"
  priority := 102597
  description := "RUBI 1.4.3, source rule 31 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.4 Miscellaneous/1.4.3 Miscellaneous algebraic functions:31"
    "1 Algebraic functions/1.4 Miscellaneous/1.4.3 Miscellaneous algebraic functions.m#31" "61e9c18ea248061cd83c67882f7c91a73cef912d" }

theorem rubi_1_4_3_r31_real : rubi_1_4_3_r31.Holds .real :=
  OSR.IntegrationRec163.rubi133r24_real

/-- RUBI 3.3, source rule 5 (OSR legacy ID). -/
def rubi_3_3_r5 : CRule where
  id := "integration.source_3_3_r5"
  legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:5"
  x := "x"
  shape := .antiderivSubst
  body := (mul (add (v "a") (mul (v "b") (.app1 .ln (mul (v "c") (add (v "d") (mul (v "e") (v "x"))))))) (pow
    (add (v "f") (mul (v "g") (v "x"))) (z (-1))))
  result := (mul (mul (z 1) (pow (v "g") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (add (v "a") (mul (v "b") (.app1 .ln (add (z 1) (mul (mul (mul (v "c")
    (v "e")) (v "x")) (pow (v "g") (z (-1)))))))) (pow (v "x") (z (-1)))))]
  substs := [("osrIntegral1", (add (v "f") (mul (v "g") (v "x"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  conditions := [(.ne (add (mul (v "e") (v "f")) (mul (mul (z (-1)) (v "d")) (v "g"))) (z 0)), (.eq (add (v
    "g") (mul (v "c") (add (mul (v "e") (v "f")) (mul (mul (z (-1)) (v "d")) (v "g"))))) (z 0))]
  priority := 102902
  description := "RUBI 3.3, source rule 5 (OSR legacy ID)"
  provenance := source "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:5"
    "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#5" "4.16.1"

/-- RUBI 4.1.0.1, source rule 11 (OSR legacy ID). -/
def rubi_4_1_0_1_r11 : CRule where
  id := "integration.source_4_1_0_1_r11"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.0.1 (a sin)^m (b trg)^n:11"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (root (mul (v "a") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2))
    (root (mul (v "b") (.app1 .cos (add (v "e") (mul (v "f") (v "x"))))) (z 2))) (z (-1))))
  result := (mul (mul (root (.app1 .sin (add (mul (z 2) (v "e")) (mul (mul (z 2) (v "f")) (v "x")))) (z 2))
    (pow (mul (root (mul (v "a") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (root (mul (v "b")
    (.app1 .cos (add (v "e") (mul (v "f") (v "x"))))) (z 2))) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (.app1 .sin (add (mul (z 2) (v "e")) (mul (mul (z 2) (v
    "f")) (v "x")))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "e", "f"]
  priority := 103116
  description := "RUBI 4.1.0.1, source rule 11 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.0.1 (a sin)^m (b trg)^n:11"
    "4 Trig functions/4.1 Sine/4.1.0.1 (a sin)^m (b trg)^n.m#11" "4.16.1"

/-- RUBI 4.1.0.2, source rule 24 (OSR legacy ID). -/
def rubi_4_1_0_2_r24 : CRule where
  id := "integration.source_4_1_0_2_r24"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.0.2 (a trg)^m (b tan)^n:24"
  x := "x"
  shape := .antiderivRec
  body := (mul (.app1 .sec (add (v "e") (mul (v "f") (v "x")))) (pow (root (mul (v "b") (.app1 .tan (add (v
    "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1))))
  result := (mul (mul (root (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (z 2)) (pow (mul (root (.app1
    .cos (add (v "e") (mul (v "f") (v "x")))) (z 2)) (root (mul (v "b") (.app1 .tan (add (v "e") (mul (v "f")
    (v "x"))))) (z 2))) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (mul (root (.app1 .cos (add (v "e") (mul (v "f") (v "x"))))
    (z 2)) (root (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (z 2))) (z (-1)))))]
  independent := ["b", "e", "f"]
  priority := 103157
  description := "RUBI 4.1.0.2, source rule 24 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.0.2 (a trg)^m (b tan)^n:24"
    "4 Trig functions/4.1 Sine/4.1.0.2 (a trg)^m (b tan)^n.m#24" "4.16.1"

/-- RUBI 4.1.1.1, source rule 26 (OSR legacy ID). -/
def rubi_4_1_1_1_r26 : CRule where
  id := "integration.source_4_1_1_1_r26"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n:26"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "c") (mul (v "d") (v "x"))))))
    (z 2)) (z (-1))))
  result := (mul (mul (root (mul (add (v "a") (mul (v "b") (.app1 .sin (add (v "c") (mul (v "d") (v "x"))))))
    (pow (add (v "a") (v "b")) (z (-1)))) (z 2)) (pow (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "c")
    (mul (v "d") (v "x")))))) (z 2)) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (mul (v "a") (pow (add (v "a") (v "b")) (z (-1))))
    (mul (mul (v "b") (pow (add (v "a") (v "b")) (z (-1)))) (.app1 .sin (add (v "c") (mul (v "d") (v "x"))))))
    (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ge (z 0) (add (v
    "a") (v "b")))]
  priority := 103205
  description := "RUBI 4.1.1.1, source rule 26 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n:26"
    "4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n.m#26" "4.16.1"

/-- RUBI 4.1.1.3, source rule 25 (OSR legacy ID). -/
def rubi_4_1_1_3_r25 : CRule where
  id := "integration.source_4_1_1_3_r25"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m:25"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (root (mul (v "g") (.app1 .tan (add (v "e") (mul (v "f") (v "x"))))) (z 2))
    (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (mul (mul (root (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (z 2)) (pow (mul (root (.app1
    .cos (add (v "e") (mul (v "f") (v "x")))) (z 2)) (root (mul (v "g") (.app1 .tan (add (v "e") (mul (v "f")
    (v "x"))))) (z 2))) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (root (.app1 .cos (add (v "e") (mul (v "f") (v "x")))) (z 2)) (pow (mul
    (root (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (z 2)) (add (v "a") (mul (v "b") (.app1 .sin (add
    (v "e") (mul (v "f") (v "x"))))))) (z (-1)))))]
  independent := ["a", "b", "e", "f", "g"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 103272
  description := "RUBI 4.1.1.3, source rule 25 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m:25"
    "4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m.m#25" "4.16.1"

/-- RUBI 4.1.2.1, source rule 8 (OSR legacy ID). -/
def rubi_4_1_2_1_r8 : CRule where
  id := "integration.source_4_1_2_1_r8"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:8"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z
    2))) (z (-1))))
  result := (mul (mul (.app1 .cos (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root (add (v "a") (mul (v
    "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .sin
    (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (.app1 .cos (add (v "e") (mul (v "f") (v "x")))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.eq (add (mul (v "b") (v "c")) (mul (v "a") (v "d"))) (z 0)), (.eq (add (pow (v "a") (z 2))
    (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 103283
  description := "RUBI 4.1.2.1, source rule 8 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:8"
    "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#8" "4.16.1"

/-- RUBI 4.1.2.1, source rule 41 (OSR legacy ID). -/
def rubi_4_1_2_1_r41 : CRule where
  id := "integration.source_4_1_2_1_r41"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:41"
  x := "x"
  shape := .antiderivSubst
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (root (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1))))
  result := (mul (mul (z (-2)) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (z 1) (mul (mul (z (-1)) (pow (v "x") (z 2))) (pow
    (v "a") (z (-1))))) (z 2)) (z (-1)))))]
  substs := [("osrIntegral1", (mul (mul (v "b") (.app1 .cos (add (v "e") (mul (v "f") (v "x"))))) (pow (root
    (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "d", "e", "f"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.eq (v "d") (mul
    (v "a") (pow (v "b") (z (-1)))))]
  priority := 103316
  description := "RUBI 4.1.2.1, source rule 41 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:41"
    "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#41" "4.16.1"

/-- RUBI 4.1.2.1, source rule 47 (OSR legacy ID). -/
def rubi_4_1_2_1_r47 : CRule where
  id := "integration.source_4_1_2_1_r47"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:47"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (v "b") (pow (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z
    (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (v "d")) (pow (add (mul (v "b") (v "c")) (mul (mul (z
    (-1)) (v "a")) (v "d"))) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul
    (v "f") (v "x")))))) (z 2)) (z (-1))))), ("osrIntegral2", (mul (root (add (v "a") (mul (v "b") (.app1 .sin
    (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul
    (v "f") (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 103322
  description := "RUBI 4.1.2.1, source rule 47 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:47"
    "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#47" "4.16.1"

/-- RUBI 4.1.2.1, source rule 48 (OSR legacy ID). -/
def rubi_4_1_2_1_r48 : CRule where
  id := "integration.source_4_1_2_1_r48"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:48"
  x := "x"
  shape := .antiderivSubst
  body := (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (root (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2))) (z (-1))))
  result := (mul (mul (mul (z (-1)) (root (z 2) (z 2))) (pow (mul (root (v "a") (z 2)) (v "f")) (z (-1)))) (v
    "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (z 1) (mul (z (-1)) (pow (v "x") (z 2)))) (z 2))
    (z (-1)))))]
  substs := [("osrIntegral1", (mul (mul (v "b") (.app1 .cos (add (v "e") (mul (v "f") (v "x"))))) (pow (add (v
    "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "d", "e", "f"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.eq (v "d") (mul
    (v "a") (pow (v "b") (z (-1))))), (.gt (v "a") (z 0))]
  priority := 103323
  description := "RUBI 4.1.2.1, source rule 48 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:48"
    "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#48" "4.16.1"

/-- RUBI 4.1.2.1, source rule 74 (OSR legacy ID). -/
def rubi_4_1_2_1_r74 : CRule where
  id := "integration.source_4_1_2_1_r74"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:74"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))
    (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))
  result := (mul (mul (root (mul (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))
    (pow (add (v "c") (v "d")) (z (-1)))) (z 2)) (pow (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e")
    (mul (v "f") (v "x")))))) (z 2)) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (mul (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul
    (v "f") (v "x")))))) (root (add (mul (v "c") (pow (add (v "c") (v "d")) (z (-1)))) (mul (mul (v "d") (pow
    (add (v "c") (v "d")) (z (-1)))) (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0)), (.ge (z 0) (add (v "c") (v "d")))]
  priority := 103349
  description := "RUBI 4.1.2.1, source rule 74 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:74"
    "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#74" "4.16.1"

/-- RUBI 4.1.2.2, source rule 73 (OSR legacy ID). -/
def rubi_4_1_2_2_r73 : CRule where
  id := "integration.source_4_1_2_2_r73"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:73"
  x := "x"
  shape := .antiderivSubst
  body := (mul (root (mul (v "g") (.app1 .cos (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (pow (mul (root
    (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (z 2)) (add (v "a") (mul (v "b") (.app1 .sin (add (v "e")
    (mul (v "f") (v "x"))))))) (z (-1))))
  result := (mul (mul (mul (mul (z (-4)) (root (z 2) (z 2))) (v "g")) (pow (v "f") (z (-1)))) (v
    "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (v "x") (z 2)) (pow (mul (add (mul (add (v "a") (v "b")) (pow (v
    "g") (z 2))) (mul (add (v "a") (mul (z (-1)) (v "b"))) (pow (v "x") (z 4)))) (root (add (z 1) (mul (mul (z
    (-1)) (pow (v "x") (z 4))) (pow (pow (v "g") (z 2)) (z (-1))))) (z 2))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (root (mul (v "g") (.app1 .cos (add (v "e") (mul (v "f") (v "x"))))) (z 2))
    (pow (root (add (z 1) (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "e", "f", "g"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 103447
  description := "RUBI 4.1.2.2, source rule 73 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:73"
    "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#73" "4.16.1"

/-- RUBI 4.1.2.2, source rule 74 (OSR legacy ID). -/
def rubi_4_1_2_2_r74 : CRule where
  id := "integration.source_4_1_2_2_r74"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:74"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (mul (v "g") (.app1 .cos (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (pow (mul (root
    (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (add (v "a") (mul (v "b") (.app1
    .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (mul (mul (root (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (z 2)) (pow (root (mul (v "d")
    (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (root (mul (v "g") (.app1 .cos (add (v "e") (mul (v "f") (v "x"))))) (z
    2)) (pow (mul (root (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (z 2)) (add (v "a") (mul (v "b")
    (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1)))))]
  independent := ["a", "b", "d", "e", "f", "g"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 103448
  description := "RUBI 4.1.2.2, source rule 74 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:74"
    "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#74" "4.16.1"

/-- RUBI 4.1.2.2, source rule 75 (OSR legacy ID). -/
def rubi_4_1_2_2_r75 : CRule where
  id := "integration.source_4_1_2_2_r75"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:75"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (pow (mul (root
    (mul (v "g") (.app1 .cos (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (add (v "a") (mul (v "b") (.app1
    .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (mul (mul (root (.app1 .cos (add (v "e") (mul (v "f") (v "x")))) (z 2)) (pow (root (mul (v "g")
    (.app1 .cos (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (root (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z
    2)) (pow (mul (root (.app1 .cos (add (v "e") (mul (v "f") (v "x")))) (z 2)) (add (v "a") (mul (v "b")
    (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1)))))]
  independent := ["a", "b", "d", "e", "f", "g"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 103450
  description := "RUBI 4.1.2.2, source rule 75 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:75"
    "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#75" "4.16.1"

/-- RUBI 4.1.2.3, source rule 3 (OSR legacy ID). -/
def rubi_4_1_2_3_r3 : CRule where
  id := "integration.source_4_1_2_3_r3"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:3"
  x := "x"
  shape := .antiderivSubst
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (mul (root (mul (v "g") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (add (v "c") (mul (v "d")
    (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (mul (mul (mul (z (-2)) (v "b")) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (add (mul (v "b") (v "c")) (mul (v "a") (v "d"))) (mul
    (mul (v "c") (v "g")) (pow (v "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (mul (v "b") (.app1 .cos (add (v "e") (mul (v "f") (v "x"))))) (pow (mul
    (root (mul (v "g") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (root (add (v "a") (mul (v
    "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 103472
  description := "RUBI 4.1.2.3, source rule 3 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:3"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#3" "4.16.1"

/-- RUBI 4.1.2.3, source rule 6 (OSR legacy ID). -/
def rubi_4_1_2_3_r6 : CRule where
  id := "integration.source_4_1_2_3_r6"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:6"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (mul (root (mul (v "g") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (add (v "c") (mul (v "d")
    (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (v "a") (pow (v "c") (z (-1)))) (v "osrIntegral1")) (mul (mul (add (mul (v "b") (v
    "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (pow (mul (v "c") (v "g")) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (mul (root (mul (v "g") (.app1 .sin (add (v "e") (mul (v "f")
    (v "x"))))) (z 2)) (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z
    2))) (z (-1))))), ("osrIntegral2", (mul (root (mul (v "g") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x"))))) (z 2)) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z
    (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 103475
  description := "RUBI 4.1.2.3, source rule 6 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:6"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#6" "4.16.1"

/-- RUBI 4.1.2.3, source rule 7 (OSR legacy ID). -/
def rubi_4_1_2_3_r7 : CRule where
  id := "integration.source_4_1_2_3_r7"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:7"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (mul (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (add (v "c") (mul (v "d") (.app1 .sin (add (v "e")
    (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (z 1) (pow (v "c") (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (v "d"))
    (pow (v "c") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (z (-1))))), ("osrIntegral2", (mul
    (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow (add (v
    "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 103476
  description := "RUBI 4.1.2.3, source rule 7 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:7"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#7" "4.16.1"

/-- RUBI 4.1.2.3, source rule 11 (OSR legacy ID). -/
def rubi_4_1_2_3_r11 : CRule where
  id := "integration.source_4_1_2_3_r11"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:11"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (mul (root (mul (v "g") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z
    2)) (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (add (v
    "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (v "b") (pow (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z
    (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (v "d")) (pow (add (mul (v "b") (v "c")) (mul (mul (z
    (-1)) (v "a")) (v "d"))) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (mul (root (mul (v "g") (.app1 .sin (add (v "e") (mul (v "f")
    (v "x"))))) (z 2)) (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z
    2))) (z (-1))))), ("osrIntegral2", (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v
    "f") (v "x")))))) (z 2)) (pow (mul (root (mul (v "g") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z
    2)) (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.or (.eq (add
    (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)) (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0)))]
  priority := 103480
  description := "RUBI 4.1.2.3, source rule 11 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:11"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#11" "4.16.1"

/-- RUBI 4.1.2.3, source rule 12 (OSR legacy ID). -/
def rubi_4_1_2_3_r12 : CRule where
  id := "integration.source_4_1_2_3_r12"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:12"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (mul (root (mul (v "g") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z
    2)) (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (add (v
    "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (z 1) (pow (v "c") (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (v "d"))
    (pow (mul (v "c") (v "g")) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (mul (root (mul (v "g") (.app1 .sin (add (v "e") (mul (v "f")
    (v "x"))))) (z 2)) (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z
    2))) (z (-1))))), ("osrIntegral2", (mul (root (mul (v "g") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x"))))) (z 2)) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z
    (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 103481
  description := "RUBI 4.1.2.3, source rule 12 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:12"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#12" "4.16.1"

/-- RUBI 4.1.2.3, source rule 13 (OSR legacy ID). -/
def rubi_4_1_2_3_r13 : CRule where
  id := "integration.source_4_1_2_3_r13"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:13"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (mul (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul
    (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (add (v "c") (mul (v "d") (.app1 .sin
    (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (pow (v "d") (z 2)) (pow (mul (v "c") (add (mul (v "b") (v "c")) (mul (mul (z (-1))
    (v "a")) (v "d")))) (z (-1)))) (v "osrIntegral1")) (mul (mul (z 1) (pow (mul (v "c") (add (mul (v "b") (v
    "c")) (mul (mul (z (-1)) (v "a")) (v "d")))) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z
    (-1))))), ("osrIntegral2", (mul (add (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (mul
    (mul (mul (z (-1)) (v "b")) (v "d")) (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (pow (mul (.app1
    .sin (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v
    "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 103482
  description := "RUBI 4.1.2.3, source rule 13 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:13"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#13" "4.16.1"

/-- RUBI 4.1.2.3, source rule 15 (OSR legacy ID). -/
def rubi_4_1_2_3_r15 : CRule where
  id := "integration.source_4_1_2_3_r15"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:15"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (mul (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (root (add (v "c") (mul (v "d") (.app1 .sin (add (v
    "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))
  result := (add (mul (mul (mul (z (-1)) (v "d")) (pow (v "c") (z (-1)))) (v "osrIntegral1")) (mul (mul (z 1)
    (pow (v "c") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))
    (z 2)) (z (-1))))), ("osrIntegral2", (mul (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e")
    (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2))) (pow (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.eq (add (mul (v "b") (v "c")) (mul (v "a") (v
    "d"))) (z 0))]
  priority := 103484
  description := "RUBI 4.1.2.3, source rule 15 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:15"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#15" "4.16.1"

/-- RUBI 4.1.2.3, source rule 16 (OSR legacy ID). -/
def rubi_4_1_2_3_r16 : CRule where
  id := "integration.source_4_1_2_3_r16"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:16"
  x := "x"
  shape := .antiderivSubst
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (mul (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (root (add (v "c") (mul (v "d") (.app1 .sin (add (v
    "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))
  result := (mul (mul (mul (z (-2)) (v "a")) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (z 1) (mul (mul (mul (z (-1)) (v "a")) (v "c")) (pow (v
    "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (.app1 .cos (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root (add (v
    "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v
    "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (mul (v "b") (v "c")) (mul (v "a") (v
    "d"))) (z 0))]
  priority := 103485
  description := "RUBI 4.1.2.3, source rule 16 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:16"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#16" "4.16.1"

/-- RUBI 4.1.2.3, source rule 17 (OSR legacy ID). -/
def rubi_4_1_2_3_r17 : CRule where
  id := "integration.source_4_1_2_3_r17"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:17"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (mul (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (root (add (v "c") (mul (v "d") (.app1 .sin (add (v
    "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))
  result := (add (mul (mul (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (pow (v "c") (z
    (-1)))) (v "osrIntegral1")) (mul (mul (v "a") (pow (v "c") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e")
    (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2))) (z (-1))))), ("osrIntegral2", (mul (root (add (v "c") (mul (v "d") (.app1 .sin (add (v
    "e") (mul (v "f") (v "x")))))) (z 2)) (pow (mul (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (root
    (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 103486
  description := "RUBI 4.1.2.3, source rule 17 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:17"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#17" "4.16.1"

/-- RUBI 4.1.2.3, source rule 19 (OSR legacy ID). -/
def rubi_4_1_2_3_r19 : CRule where
  id := "integration.source_4_1_2_3_r19"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:19"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (mul (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul
    (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (root (add (v "c") (mul (v "d") (.app1
    .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))
  result := (mul (mul (.app1 .cos (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root (add (v "a") (mul (v
    "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .sin
    (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (mul (.app1 .cos (add (v "e") (mul (v "f") (v "x")))) (.app1
    .sin (add (v "e") (mul (v "f") (v "x"))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 103488
  description := "RUBI 4.1.2.3, source rule 19 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:19"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#19" "4.16.1"

/-- RUBI 4.1.2.3, source rule 20 (OSR legacy ID). -/
def rubi_4_1_2_3_r20 : CRule where
  id := "integration.source_4_1_2_3_r20"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:20"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (mul (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul
    (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (root (add (v "c") (mul (v "d") (.app1
    .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))
  result := (add (mul (mul (mul (z (-1)) (v "b")) (pow (v "a") (z (-1)))) (v "osrIntegral1")) (mul (mul (z 1)
    (pow (v "a") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e")
    (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2))) (z (-1))))), ("osrIntegral2", (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v
    "e") (mul (v "f") (v "x")))))) (z 2)) (pow (mul (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (root
    (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.or (.ne (add
    (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)) (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0)))]
  priority := 103489
  description := "RUBI 4.1.2.3, source rule 20 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:20"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#20" "4.16.1"

/-- RUBI 4.1.2.3, source rule 21 (OSR legacy ID). -/
def rubi_4_1_2_3_r21 : CRule where
  id := "integration.source_4_1_2_3_r21"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:21"
  x := "x"
  shape := .antiderivRec
  body := (mul (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))
    (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow (.app1
    .sin (add (v "e") (mul (v "f") (v "x")))) (z (-1))))
  result := (mul (mul (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))
    (z 2)) (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow
    (.app1 .cos (add (v "e") (mul (v "f") (v "x")))) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (.app1 .cot (add (v "e") (mul (v "f") (v "x")))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 103490
  description := "RUBI 4.1.2.3, source rule 21 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:21"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#21" "4.16.1"

/-- RUBI 4.1.2.3, source rule 22 (OSR legacy ID). -/
def rubi_4_1_2_3_r22 : CRule where
  id := "integration.source_4_1_2_3_r22"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:22"
  x := "x"
  shape := .antiderivRec
  body := (mul (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))
    (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow (.app1
    .sin (add (v "e") (mul (v "f") (v "x")))) (z (-1))))
  result := (add (mul (v "d") (v "osrIntegral1")) (mul (v "c") (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))
    (z 2)) (z (-1))))), ("osrIntegral2", (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v
    "f") (v "x")))))) (z 2)) (pow (mul (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (root (add (v "c")
    (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.or (.ne (add
    (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)) (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0)))]
  priority := 103491
  description := "RUBI 4.1.2.3, source rule 22 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n:22"
    "4 Trig functions/4.1 Sine/4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n.m#22" "4.16.1"

/-- RUBI 4.1.3.1, source rule 4 (OSR legacy ID). -/
def rubi_4_1_3_1_r4 : CRule where
  id := "integration.source_4_1_3_1_r4"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):4"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "A") (mul (v "B") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (pow (mul (root
    (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c")
    (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))
  result := (add (mul (mul (add (mul (v "A") (v "b")) (mul (v "a") (v "B"))) (pow (mul (mul (z 2) (v "a")) (v
    "b")) (z (-1)))) (v "osrIntegral1")) (mul (mul (add (mul (v "B") (v "c")) (mul (v "A") (v "d"))) (pow (mul
    (mul (z 2) (v "c")) (v "d")) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))
    (z 2)) (z (-1))))), ("osrIntegral2", (mul (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v
    "f") (v "x")))))) (z 2)) (pow (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (z (-1)))))]
  independent := ["A", "B", "a", "b", "c", "d", "e", "f"]
  conditions := [(.eq (add (mul (v "b") (v "c")) (mul (v "a") (v "d"))) (z 0)), (.eq (add (pow (v "a") (z 2))
    (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 103511
  description := "RUBI 4.1.3.1, source rule 4 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):4"
    "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#4" "4.16.1"

/-- RUBI 4.1.3.1, source rule 17 (OSR legacy ID). -/
def rubi_4_1_3_1_r17 : CRule where
  id := "integration.source_4_1_3_1_r17"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):17"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "A") (mul (v "B") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (pow (mul (root
    (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c")
    (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))
  result := (add (mul (mul (add (mul (v "A") (v "b")) (mul (mul (z (-1)) (v "a")) (v "B"))) (pow (v "b") (z
    (-1)))) (v "osrIntegral1")) (mul (mul (v "B") (pow (v "b") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e")
    (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2))) (z (-1))))), ("osrIntegral2", (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v
    "e") (mul (v "f") (v "x")))))) (z 2)) (pow (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul
    (v "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["A", "B", "a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 103524
  description := "RUBI 4.1.3.1, source rule 17 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):17"
    "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#17" "4.16.1"

/-- RUBI 4.1.3.1, source rule 20 (OSR legacy ID). -/
def rubi_4_1_3_1_r20 : CRule where
  id := "integration.source_4_1_3_1_r20"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):20"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "A") (mul (v "B") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (pow (mul (root
    (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (add (v "c") (mul (v
    "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (add (mul (v "A") (v "b")) (mul (mul (z (-1)) (v "a")) (v "B"))) (pow (add (mul (v
    "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z (-1)))) (v "osrIntegral1")) (mul (mul (add (mul (v
    "B") (v "c")) (mul (mul (z (-1)) (v "A")) (v "d"))) (pow (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v
    "a")) (v "d"))) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul
    (v "f") (v "x")))))) (z 2)) (z (-1))))), ("osrIntegral2", (mul (root (add (v "a") (mul (v "b") (.app1 .sin
    (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul
    (v "f") (v "x")))))) (z (-1)))))]
  independent := ["A", "B", "a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 103527
  description := "RUBI 4.1.3.1, source rule 20 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):20"
    "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#20" "4.16.1"

/-- RUBI 4.1.3.1, source rule 40 (OSR legacy ID). -/
def rubi_4_1_3_1_r40 : CRule where
  id := "integration.source_4_1_3_1_r40"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):40"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "A") (mul (v "B") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (pow (mul (root
    (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (mul (v "d")
    (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2))) (z (-1))))
  result := (mul (mul (root (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (z 2)) (pow (root (mul (v "d")
    (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (add (v "A") (mul (v "B") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (pow (mul (root (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (z 2)) (root (add (v "a") (mul
    (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["A", "B", "a", "b", "d", "e", "f"]
  conditions := [(.gt (v "b") (z 0)), (.gt (add (pow (v "b") (z 2)) (mul (z (-1)) (pow (v "a") (z 2)))) (z
    0)), (.eq (v "A") (v "B"))]
  priority := 103547
  description := "RUBI 4.1.3.1, source rule 40 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):40"
    "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#40" "4.16.1"

/-- RUBI 4.1.3.1, source rule 41 (OSR legacy ID). -/
def rubi_4_1_3_1_r41 : CRule where
  id := "integration.source_4_1_3_1_r41"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):41"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "A") (mul (v "B") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (pow (mul (root
    (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c")
    (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))
  result := (add (mul (mul (v "B") (pow (v "d") (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (add
    (mul (v "B") (v "c")) (mul (mul (z (-1)) (v "A")) (v "d")))) (pow (v "d") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))
    (z 2)) (z (-1))))), ("osrIntegral2", (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add
    (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v
    "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["A", "B", "a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 103548
  description := "RUBI 4.1.3.1, source rule 41 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):41"
    "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#41" "4.16.1"

/-- RUBI 4.1.4.2, source rule 32 (OSR legacy ID). -/
def rubi_4_1_4_2_r32 : CRule where
  id := "integration.source_4_1_4_2_r32"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):32"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "A") (mul (v "C") (pow (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (z 2)))) (pow
    (mul (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (add (v
    "c") (mul (v "d") (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (v "C") (pow (mul (v "b") (v "d")) (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z
    (-1)) (z 1)) (pow (mul (v "b") (v "d")) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (root (add (v "a") (mul (v "b") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2))), ("osrIntegral2", (mul (add (add (mul (mul (v "a") (v "c")) (v "C")) (mul (mul (mul (z
    (-1)) (v "A")) (v "b")) (v "d"))) (mul (add (mul (mul (v "b") (v "c")) (v "C")) (mul (mul (v "a") (v "C"))
    (v "d"))) (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (pow (mul (root (add (v "a") (mul (v "b")
    (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (add (v "c") (mul (v "d") (.app1 .sin (add (v
    "e") (mul (v "f") (v "x"))))))) (z (-1)))))]
  independent := ["A", "C", "a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 103602
  description := "RUBI 4.1.4.2, source rule 32 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):32"
    "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#32" "4.16.1"

/-- RUBI 4.1.6, source rule 44 (OSR legacy ID). -/
def rubi_4_1_6_r44 : CRule where
  id := "integration.source_4_1_6_r44"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:44"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (add (add (v "a") (mul (v "b") (.app1 .sec (add (v "d") (mul (v "e") (v "x"))))))
    (mul (v "c") (.app1 .tan (add (v "d") (mul (v "e") (v "x")))))) (z (-1))))
  result := (v "osrIntegral1")
  integrals := [("osrIntegral1", (mul (.app1 .cos (add (v "d") (mul (v "e") (v "x")))) (pow (add (add (v "b")
    (mul (v "a") (.app1 .cos (add (v "d") (mul (v "e") (v "x")))))) (mul (v "c") (.app1 .sin (add (v "d") (mul
    (v "e") (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  priority := 103699
  description := "RUBI 4.1.6, source rule 44 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:44"
    "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#44" "4.16.1"

/-- RUBI 4.1.6, source rule 45 (OSR legacy ID). -/
def rubi_4_1_6_r45 : CRule where
  id := "integration.source_4_1_6_r45"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:45"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (add (add (v "a") (mul (v "b") (.app1 .csc (add (v "d") (mul (v "e") (v "x"))))))
    (mul (v "c") (.app1 .cot (add (v "d") (mul (v "e") (v "x")))))) (z (-1))))
  result := (v "osrIntegral1")
  integrals := [("osrIntegral1", (mul (.app1 .sin (add (v "d") (mul (v "e") (v "x")))) (pow (add (add (v "b")
    (mul (v "a") (.app1 .sin (add (v "d") (mul (v "e") (v "x")))))) (mul (v "c") (.app1 .cos (add (v "d") (mul
    (v "e") (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  priority := 103700
  description := "RUBI 4.1.6, source rule 45 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:45"
    "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#45" "4.16.1"

/-- RUBI 4.1.7, source rule 13 (OSR legacy ID). -/
def rubi_4_1_7_r13 : CRule where
  id := "integration.source_4_1_7_r13"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:13"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (root (add (v "a") (mul (v "b") (pow (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))) (z 2)))) (z 2)) (z (-1))))
  result := (mul (mul (root (add (z 1) (mul (mul (v "b") (pow (.app1 .sin (add (v "e") (mul (v "f") (v "x"))))
    (z 2))) (pow (v "a") (z (-1))))) (z 2)) (pow (root (add (v "a") (mul (v "b") (pow (.app1 .sin (add (v "e")
    (mul (v "f") (v "x")))) (z 2)))) (z 2)) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (z 1) (mul (mul (v "b") (pow (.app1 .sin (add (v
    "e") (mul (v "f") (v "x")))) (z 2))) (pow (v "a") (z (-1))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "e", "f"]
  conditions := [(.ge (z 0) (v "a"))]
  priority := 103721
  description := "RUBI 4.1.7, source rule 13 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:13"
    "4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p.m#13" "4.16.1"

/-- RUBI 4.3.1.2, source rule 4 (OSR legacy ID). -/
def rubi_4_3_1_2_r4 : CRule where
  id := "integration.source_4_3_1_2_r4"
  legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n:4"
  x := "x"
  shape := .antiderivSubst
  body := (mul (.app1 .sec (add (v "e") (mul (v "f") (v "x")))) (pow (root (add (v "a") (mul (v "b") (.app1
    .tan (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (mul (mul (mul (z (-2)) (v "a")) (pow (mul (v "b") (v "f")) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (z 2) (mul (mul (z (-1)) (v "a")) (pow (v "x") (z 2))))
    (z (-1)))))]
  substs := [("osrIntegral1", (mul (.app1 .sec (add (v "e") (mul (v "f") (v "x")))) (pow (root (add (v "a")
    (mul (v "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "e", "f"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (pow (v "b") (z 2))) (z 0))]
  priority := 103964
  description := "RUBI 4.3.1.2, source rule 4 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n:4"
    "4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n.m#4" "4.16.1"

/-- RUBI 4.3.2.1, source rule 11 (OSR legacy ID). -/
def rubi_4_3_2_1_r11 : CRule where
  id := "integration.source_4_3_2_1_r11"
  legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:11"
  x := "x"
  shape := .antiderivSubst
  body := (mul (add (v "c") (mul (v "d") (.app1 .tan (add (v "e") (mul (v "f") (v "x")))))) (pow (root (mul (v
    "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1))))
  result := (mul (mul (mul (z (-2)) (pow (v "d") (z 2))) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (mul (mul (z 2) (v "c")) (v "d")) (mul (v "b") (pow (v
    "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (add (v "c") (mul (mul (z (-1)) (v "d")) (.app1 .tan (add (v "e") (mul (v
    "f") (v "x")))))) (pow (root (mul (v "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z
    (-1)))))]
  independent := ["b", "c", "d", "e", "f"]
  conditions := [(.eq (add (pow (v "c") (z 2)) (mul (z (-1)) (pow (v "d") (z 2)))) (z 0))]
  priority := 104007
  description := "RUBI 4.3.2.1, source rule 11 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:11"
    "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#11" "4.16.1"

/-- RUBI 4.3.2.1, source rule 12 (OSR legacy ID). -/
def rubi_4_3_2_1_r12 : CRule where
  id := "integration.source_4_3_2_1_r12"
  legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:12"
  x := "x"
  shape := .antiderivSubst
  body := (mul (add (v "c") (mul (v "d") (.app1 .tan (add (v "e") (mul (v "f") (v "x")))))) (pow (root (mul (v
    "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1))))
  result := (mul (mul (mul (z 2) (pow (v "c") (z 2))) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "d")) (pow
    (v "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (root (mul (v "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x"))))) (z 2)))]
  independent := ["b", "c", "d", "e", "f"]
  conditions := [(.eq (add (pow (v "c") (z 2)) (pow (v "d") (z 2))) (z 0))]
  priority := 104008
  description := "RUBI 4.3.2.1, source rule 12 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:12"
    "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#12" "4.16.1"

/-- RUBI 4.3.2.1, source rule 13 (OSR legacy ID). -/
def rubi_4_3_2_1_r13 : CRule where
  id := "integration.source_4_3_2_1_r13"
  legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:13"
  x := "x"
  shape := .antiderivSubst
  body := (mul (add (v "c") (mul (v "d") (.app1 .tan (add (v "e") (mul (v "f") (v "x")))))) (pow (root (mul (v
    "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1))))
  result := (mul (mul (z 2) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (add (mul (v "b") (v "c")) (mul (v "d") (pow (v "x") (z 2)))) (pow (add
    (pow (v "b") (z 2)) (pow (v "x") (z 4))) (z (-1)))))]
  substs := [("osrIntegral1", (root (mul (v "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x"))))) (z 2)))]
  independent := ["b", "c", "d", "e", "f"]
  conditions := [(.ne (add (pow (v "c") (z 2)) (mul (z (-1)) (pow (v "d") (z 2)))) (z 0)), (.ne (add (pow (v
    "c") (z 2)) (pow (v "d") (z 2))) (z 0))]
  priority := 104009
  description := "RUBI 4.3.2.1, source rule 13 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:13"
    "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#13" "4.16.1"

/-- RUBI 4.3.2.1, source rule 22 (OSR legacy ID). -/
def rubi_4_3_2_1_r22 : CRule where
  id := "integration.source_4_3_2_1_r22"
  legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:22"
  x := "x"
  shape := .antiderivSubst
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (root (add (v "c") (mul (v "d") (.app1 .tan (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (mul (mul (mul (mul (z (-2)) (v "a")) (v "b")) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (add (mul (v "a") (v "c")) (mul (mul (z (-1)) (v "b"))
    (v "d"))) (mul (mul (mul (z (-1)) (z 2)) (pow (v "a") (z 2))) (pow (v "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (root (add (v "c") (mul (v "d") (.app1 .tan (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (root (add (v "a") (mul (v "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x"))))))
    (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (pow (v "b") (z 2))) (z 0)), (.ne (add (pow (v "c") (z 2)) (pow (v "d") (z 2))) (z 0))]
  priority := 104019
  description := "RUBI 4.3.2.1, source rule 22 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:22"
    "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#22" "4.16.1"

/-- RUBI 4.3.2.1, source rule 41 (OSR legacy ID). -/
def rubi_4_3_2_1_r41 : CRule where
  id := "integration.source_4_3_2_1_r41"
  legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:41"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root
    (add (v "c") (mul (v "d") (.app1 .tan (add (v "e") (mul (v "f") (v "x")))))) (z 2)))
  result := (add (mul (mul (add (mul (v "a") (v "c")) (mul (mul (z (-1)) (v "b")) (v "d"))) (pow (v "a") (z
    (-1)))) (v "osrIntegral1")) (mul (mul (v "d") (pow (v "a") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "a") (mul (v "b") (.app1 .tan (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (root (add (v "c") (mul (v "d") (.app1 .tan (add (v "e") (mul (v "f") (v "x"))))))
    (z 2)) (z (-1))))), ("osrIntegral2", (mul (mul (root (add (v "a") (mul (v "b") (.app1 .tan (add (v "e")
    (mul (v "f") (v "x")))))) (z 2)) (add (v "b") (mul (v "a") (.app1 .tan (add (v "e") (mul (v "f") (v
    "x"))))))) (pow (root (add (v "c") (mul (v "d") (.app1 .tan (add (v "e") (mul (v "f") (v "x")))))) (z 2))
    (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (pow (v "b") (z 2))) (z 0)), (.ne (add (pow (v "c") (z 2)) (pow (v "d") (z 2))) (z 0))]
  priority := 104038
  description := "RUBI 4.3.2.1, source rule 41 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:41"
    "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#41" "4.16.1"

/-- RUBI 4.3.7, source rule 3 (OSR legacy ID). -/
def rubi_4_3_7_r3 : CRule where
  id := "integration.source_4_3_7_r3"
  legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.7 (d trig)^m (a+b (c tan)^n)^p:3"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (add (v "a") (mul (v "b") (pow (.app1 .tan (add (v "e") (mul (v "f") (v "x")))) (z
    2)))) (z (-1))))
  result := (add (mul (v "x") (pow (add (v "a") (mul (z (-1)) (v "b"))) (z (-1)))) (mul (mul (mul (z (-1)) (v
    "b")) (pow (add (v "a") (mul (z (-1)) (v "b"))) (z (-1)))) (v "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (pow (.app1 .sec (add (v "e") (mul (v "f") (v "x")))) (z 2)) (pow (add
    (v "a") (mul (v "b") (pow (.app1 .tan (add (v "e") (mul (v "f") (v "x")))) (z 2)))) (z (-1)))))]
  independent := ["a", "b", "e", "f"]
  conditions := [(.ne (v "a") (v "b"))]
  priority := 104135
  description := "RUBI 4.3.7, source rule 3 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.3 Tangent/4.3.7 (d trig)^m (a+b (c tan)^n)^p:3"
    "4 Trig functions/4.3 Tangent/4.3.7 (d trig)^m (a+b (c tan)^n)^p.m#3" "4.16.1"

/-- RUBI 4.3.10, source rule 9 (OSR legacy ID). -/
def rubi_4_3_10_r9 : CRule where
  id := "integration.source_4_3_10_r9"
  legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n:9"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (pow (add (v "c") (mul (v "d") (v "x"))) (z 2)) (add (v "a") (mul (v "b")
    (.app1 .tan (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (add (mul (z (-1)) (pow (mul (mul (v "d") (add (v "c") (mul (v "d") (v "x")))) (add (v "a")
    (mul (v "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x"))))))) (z (-1)))) (mul (mul (v "f") (pow (mul (v
    "b") (v "d")) (z (-1)))) (v "osrIntegral1"))) (mul (mul (mul (z (-1)) (v "f")) (pow (mul (v "a") (v "d"))
    (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (.app1 .cos (add (mul (z 2) (v "e")) (mul (mul (z 2) (v "f")) (v "x"))))
    (pow (add (v "c") (mul (v "d") (v "x"))) (z (-1))))), ("osrIntegral2", (mul (.app1 .sin (add (mul (z 2) (v
    "e")) (mul (mul (z 2) (v "f")) (v "x")))) (pow (add (v "c") (mul (v "d") (v "x"))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (pow (v "b") (z 2))) (z 0))]
  priority := 104189
  description := "RUBI 4.3.10, source rule 9 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n:9"
    "4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n.m#9" "4.16.1"

/-- RUBI 4.3.10, source rule 11 (OSR legacy ID). -/
def rubi_4_3_10_r11 : CRule where
  id := "integration.source_4_3_10_r11"
  legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n:11"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (add (v "c") (mul (v "d") (v "x"))) (add (v "a") (mul (v "b") (.app1 .tan (add
    (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (add (mul (.app1 .ln (add (v "c") (mul (v "d") (v "x")))) (pow (mul (mul (z 2) (v "a")) (v
    "d")) (z (-1)))) (mul (mul (z 1) (pow (mul (z 2) (v "a")) (z (-1)))) (v "osrIntegral1"))) (mul (mul (z 1)
    (pow (mul (z 2) (v "b")) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (.app1 .cos (add (mul (z 2) (v "e")) (mul (mul (z 2) (v "f")) (v "x"))))
    (pow (add (v "c") (mul (v "d") (v "x"))) (z (-1))))), ("osrIntegral2", (mul (.app1 .sin (add (mul (z 2) (v
    "e")) (mul (mul (z 2) (v "f")) (v "x")))) (pow (add (v "c") (mul (v "d") (v "x"))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (pow (v "b") (z 2))) (z 0))]
  priority := 104191
  description := "RUBI 4.3.10, source rule 11 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n:11"
    "4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n.m#11" "4.16.1"

/-- RUBI 4.3.12, source rule 6 (OSR legacy ID). -/
def rubi_4_3_12_r6 : CRule where
  id := "integration.source_4_3_12_r6"
  legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.12 (d+e x)^m tan(a+b x+c x^2)^n:6"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "d") (mul (v "e") (v "x"))) (.app1 .cot (add (add (v "a") (mul (v "b") (v "x"))) (mul
    (v "c") (pow (v "x") (z 2))))))
  result := (add (mul (mul (v "e") (.app1 .ln (.app1 .sin (add (add (v "a") (mul (v "b") (v "x"))) (mul (v
    "c") (pow (v "x") (z 2))))))) (pow (mul (z 2) (v "c")) (z (-1)))) (mul (mul (add (mul (mul (z 2) (v "c"))
    (v "d")) (mul (mul (z (-1)) (v "b")) (v "e"))) (pow (mul (z 2) (v "c")) (z (-1)))) (v "osrIntegral1")))
  integrals := [("osrIntegral1", (.app1 .cot (add (add (v "a") (mul (v "b") (v "x"))) (mul (v "c") (pow (v
    "x") (z 2))))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [(.ne (add (mul (mul (z 2) (v "c")) (v "d")) (mul (mul (z (-1)) (v "b")) (v "e"))) (z 0))]
  priority := 104233
  description := "RUBI 4.3.12, source rule 6 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.3 Tangent/4.3.12 (d+e x)^m tan(a+b x+c x^2)^n:6"
    "4 Trig functions/4.3 Tangent/4.3.12 (d+e x)^m tan(a+b x+c x^2)^n.m#6" "4.16.1"

/-- RUBI 4.5.1.1, source rule 10 (OSR legacy ID). -/
def rubi_4_5_1_1_r10 : CRule where
  id := "integration.source_4_5_1_1_r10"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.1 (a+b sec)^n:10"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "c") (mul (v "d") (v "x"))))))
    (z 2)) (z (-1))))
  result := (add (mul (mul (z 1) (pow (v "a") (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (v "b"))
    (pow (v "a") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "c") (mul (v "d") (v
    "x")))))) (z 2))), ("osrIntegral2", (mul (.app1 .csc (add (v "c") (mul (v "d") (v "x")))) (pow (root (add
    (v "a") (mul (v "b") (.app1 .csc (add (v "c") (mul (v "d") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104245
  description := "RUBI 4.5.1.1, source rule 10 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.1 (a+b sec)^n:10"
    "4 Trig functions/4.5 Secant/4.5.1.1 (a+b sec)^n.m#10" "4.16.1"

/-- RUBI 4.5.1.2, source rule 8 (OSR legacy ID). -/
def rubi_4_5_1_2_r8 : CRule where
  id := "integration.source_4_5_1_2_r8"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:8"
  x := "x"
  shape := .antideriv
  body := (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (add (v "a") (mul (v "b") (.app1 .csc
    (add (v "e") (mul (v "f") (v "x")))))) (z (-1))))
  result := (mul (mul (z (-1)) (.app1 .cot (add (v "e") (mul (v "f") (v "x"))))) (pow (mul (v "f") (add (v
    "b") (mul (v "a") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  independent := ["a", "b", "e", "f"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104263
  description := "RUBI 4.5.1.2, source rule 8 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:8"
    "4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.m#8" "4.16.1"

/-- RUBI 4.5.1.2, source rule 9 (OSR legacy ID). -/
def rubi_4_5_1_2_r9 : CRule where
  id := "integration.source_4_5_1_2_r9"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:9"
  x := "x"
  shape := .antiderivSubst
  body := (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (root (add (v "a") (mul (v "b") (.app1
    .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (mul (mul (z (-2)) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (mul (z 2) (v "a")) (pow (v "x") (z 2))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (mul (v "b") (.app1 .cot (add (v "e") (mul (v "f") (v "x"))))) (pow (root
    (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "e", "f"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104264
  description := "RUBI 4.5.1.2, source rule 9 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:9"
    "4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.m#9" "4.16.1"

/-- RUBI 4.5.1.2, source rule 15 (OSR legacy ID). -/
def rubi_4_5_1_2_r15 : CRule where
  id := "integration.source_4_5_1_2_r15"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:15"
  x := "x"
  shape := .antiderivSubst
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root
    (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)))
  result := (mul (mul (mul (mul (z (-2)) (v "a")) (pow (mul (v "b") (v "f")) (z (-1)))) (root (mul (mul (v
    "a") (v "d")) (pow (v "b") (z (-1)))) (z 2))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (z 1) (mul (pow (v "x") (z 2)) (pow (v "a") (z
    (-1))))) (z 2)) (z (-1)))))]
  substs := [("osrIntegral1", (mul (mul (v "b") (.app1 .cot (add (v "e") (mul (v "f") (v "x"))))) (pow (root
    (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "d", "e", "f"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.gt (mul (mul (v
    "a") (v "d")) (pow (v "b") (z (-1)))) (z 0))]
  priority := 104270
  description := "RUBI 4.5.1.2, source rule 15 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:15"
    "4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.m#15" "4.16.1"

/-- RUBI 4.5.1.2, source rule 16 (OSR legacy ID). -/
def rubi_4_5_1_2_r16 : CRule where
  id := "integration.source_4_5_1_2_r16"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:16"
  x := "x"
  shape := .antiderivSubst
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root
    (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)))
  result := (mul (mul (mul (mul (z (-2)) (v "b")) (v "d")) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (v "b") (mul (mul (z (-1)) (v "d")) (pow (v "x") (z
    2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (mul (v "b") (.app1 .cot (add (v "e") (mul (v "f") (v "x"))))) (pow (mul
    (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (mul (v
    "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "d", "e", "f"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ge (z 0) (mul
    (mul (v "a") (v "d")) (pow (v "b") (z (-1)))))]
  priority := 104271
  description := "RUBI 4.5.1.2, source rule 16 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:16"
    "4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.m#16" "4.16.1"

/-- RUBI 4.5.1.2, source rule 18 (OSR legacy ID). -/
def rubi_4_5_1_2_r18 : CRule where
  id := "integration.source_4_5_1_2_r18"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:18"
  x := "x"
  shape := .antideriv
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1))))
  result := (mul (mul (mul (z (-2)) (v "a")) (.app1 .cot (add (v "e") (mul (v "f") (v "x"))))) (pow (mul (mul
    (v "f") (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (root
    (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2))) (z (-1))))
  independent := ["a", "b", "d", "e", "f"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104273
  description := "RUBI 4.5.1.2, source rule 18 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:18"
    "4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.m#18" "4.16.1"

/-- RUBI 4.5.1.2, source rule 21 (OSR legacy ID). -/
def rubi_4_5_1_2_r21 : CRule where
  id := "integration.source_4_5_1_2_r21"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:21"
  x := "x"
  shape := .antiderivSubst
  body := (mul (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (pow (root (add (v
    "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (mul (mul (mul (mul (z (-1)) (root (z 2) (z 2))) (root (v "a") (z 2))) (pow (mul (v "b") (v "f"))
    (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (z 1) (pow (v "x") (z 2))) (z 2)) (z (-1)))))]
  substs := [("osrIntegral1", (mul (mul (v "b") (.app1 .cot (add (v "e") (mul (v "f") (v "x"))))) (pow (add (v
    "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "d", "e", "f"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.eq (add (v "d")
    (mul (mul (z (-1)) (v "a")) (pow (v "b") (z (-1))))) (z 0)), (.gt (v "a") (z 0))]
  priority := 104276
  description := "RUBI 4.5.1.2, source rule 21 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:21"
    "4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.m#21" "4.16.1"

/-- RUBI 4.5.1.2, source rule 22 (OSR legacy ID). -/
def rubi_4_5_1_2_r22 : CRule where
  id := "integration.source_4_5_1_2_r22"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:22"
  x := "x"
  shape := .antiderivSubst
  body := (mul (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (pow (root (add (v
    "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (mul (mul (mul (mul (z (-2)) (v "b")) (v "d")) (pow (mul (v "a") (v "f")) (z (-1)))) (v
    "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (mul (z 2) (v "b")) (mul (mul (z (-1)) (v "d")) (pow (v
    "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (mul (v "b") (.app1 .cot (add (v "e") (mul (v "f") (v "x"))))) (pow (mul
    (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (mul (v
    "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "d", "e", "f"]
  conditions := [(.eq (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104277
  description := "RUBI 4.5.1.2, source rule 22 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:22"
    "4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.m#22" "4.16.1"

/-- RUBI 4.5.1.2, source rule 43 (OSR legacy ID). -/
def rubi_4_5_1_2_r43 : CRule where
  id := "integration.source_4_5_1_2_r43"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:43"
  x := "x"
  shape := .antiderivRec
  body := (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul (v "b") (.app1 .csc
    (add (v "e") (mul (v "f") (v "x")))))) (z 2)))
  result := (add (mul (add (v "a") (mul (z (-1)) (v "b"))) (v "osrIntegral1")) (mul (v "b") (v
    "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (root (add (v "a")
    (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))), ("osrIntegral2", (mul
    (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (add (z 1) (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (pow (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))
    (z (-1)))))]
  independent := ["a", "b", "e", "f"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104298
  description := "RUBI 4.5.1.2, source rule 43 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:43"
    "4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.m#43" "4.16.1"

/-- RUBI 4.5.1.2, source rule 70 (OSR legacy ID). -/
def rubi_4_5_1_2_r70 : CRule where
  id := "integration.source_4_5_1_2_r70"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:70"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1))))
  result := (mul (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z
    2)) (pow (mul (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (root (add (v
    "b") (mul (v "a") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))) (v
    "osrIntegral1"))
  integrals := [("osrIntegral1", (root (add (v "b") (mul (v "a") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)))]
  independent := ["a", "b", "d", "e", "f"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104325
  description := "RUBI 4.5.1.2, source rule 70 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:70"
    "4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.m#70" "4.16.1"

/-- RUBI 4.5.1.2, source rule 72 (OSR legacy ID). -/
def rubi_4_5_1_2_r72 : CRule where
  id := "integration.source_4_5_1_2_r72"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:72"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (pow (root (add (v
    "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (mul (mul (mul (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (root
    (add (v "b") (mul (v "a") (.app1 .sin (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow (root (add (v
    "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (v "b") (mul (v "a") (.app1 .sin (add (v "e") (mul
    (v "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "d", "e", "f"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104327
  description := "RUBI 4.5.1.2, source rule 72 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:72"
    "4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.m#72" "4.16.1"

/-- RUBI 4.5.1.2, source rule 76 (OSR legacy ID). -/
def rubi_4_5_1_2_r76 : CRule where
  id := "integration.source_4_5_1_2_r76"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:76"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2))) (z (-1))))
  result := (add (mul (mul (z 1) (pow (v "a") (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (v "b"))
    (pow (mul (v "a") (v "d")) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z
    (-1))))), ("osrIntegral2", (mul (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z
    2)) (pow (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z
    (-1)))))]
  independent := ["a", "b", "d", "e", "f"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104331
  description := "RUBI 4.5.1.2, source rule 76 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m:76"
    "4 Trig functions/4.5 Secant/4.5.1.2 (d sec)^n (a+b sec)^m.m#76" "4.16.1"

/-- RUBI 4.5.1.4, source rule 5 (OSR legacy ID). -/
def rubi_4_5_1_4_r5 : CRule where
  id := "integration.source_4_5_1_4_r5"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.4 (d tan)^n (a+b sec)^m:5"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "a") (mul (v "b") (.app1 .csc (add (v "c") (mul (v "d") (v "x")))))) (pow (.app1 .cot
    (add (v "c") (mul (v "d") (v "x")))) (z (-1))))
  result := (v "osrIntegral1")
  integrals := [("osrIntegral1", (mul (add (v "b") (mul (v "a") (.app1 .sin (add (v "c") (mul (v "d") (v
    "x")))))) (pow (.app1 .cos (add (v "c") (mul (v "d") (v "x")))) (z (-1)))))]
  independent := ["a", "b", "c", "d"]
  priority := 104352
  description := "RUBI 4.5.1.4, source rule 5 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.4 (d tan)^n (a+b sec)^m:5"
    "4 Trig functions/4.5 Secant/4.5.1.4 (d tan)^n (a+b sec)^m.m#5" "4.16.1"

/-- RUBI 4.5.1.4, source rule 14 (OSR legacy ID). -/
def rubi_4_5_1_4_r14 : CRule where
  id := "integration.source_4_5_1_4_r14"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.4 (d tan)^n (a+b sec)^m:14"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (root (mul (v "e") (.app1 .cot (add (v "c") (mul (v "d") (v "x"))))) (z 2))
    (add (v "a") (mul (v "b") (.app1 .csc (add (v "c") (mul (v "d") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (z 1) (pow (v "a") (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (v "b"))
    (pow (v "a") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (mul (v "e") (.app1 .cot (add (v "c") (mul (v "d") (v
    "x"))))) (z 2)) (z (-1))))), ("osrIntegral2", (mul (z 1) (pow (mul (root (mul (v "e") (.app1 .cot (add (v
    "c") (mul (v "d") (v "x"))))) (z 2)) (add (v "b") (mul (v "a") (.app1 .sin (add (v "c") (mul (v "d") (v
    "x"))))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104361
  description := "RUBI 4.5.1.4, source rule 14 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.4 (d tan)^n (a+b sec)^m:14"
    "4 Trig functions/4.5 Secant/4.5.1.4 (d tan)^n (a+b sec)^m.m#14" "4.16.1"

/-- RUBI 4.5.2.1, source rule 14 (OSR legacy ID). -/
def rubi_4_5_2_1_r14 : CRule where
  id := "integration.source_4_5_2_1_r14"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:14"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (add
    (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))))
  result := (add (mul (mul (v "a") (v "c")) (v "osrIntegral1")) (v "osrIntegral2"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul
    (v "f") (v "x")))))) (z 2)) (z (-1))))), ("osrIntegral2", (mul (mul (.app1 .csc (add (v "e") (mul (v "f")
    (v "x")))) (add (add (mul (v "b") (v "c")) (mul (v "a") (v "d"))) (mul (mul (v "b") (v "d")) (.app1 .csc
    (add (v "e") (mul (v "f") (v "x"))))))) (pow (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul
    (v "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104385
  description := "RUBI 4.5.2.1, source rule 14 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:14"
    "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#14" "4.16.1"

/-- RUBI 4.5.2.1, source rule 18 (OSR legacy ID). -/
def rubi_4_5_2_1_r18 : CRule where
  id := "integration.source_4_5_2_1_r18"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:18"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (pow (root (add (v
    "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (add (mul (mul (v "c") (pow (v "a") (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (add
    (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d")))) (pow (v "a") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2))), ("osrIntegral2", (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (root (add
    (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104389
  description := "RUBI 4.5.2.1, source rule 18 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:18"
    "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#18" "4.16.1"

/-- RUBI 4.5.2.1, source rule 23 (OSR legacy ID). -/
def rubi_4_5_2_1_r23 : CRule where
  id := "integration.source_4_5_2_1_r23"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:23"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z (-1))))
  result := (add (mul (mul (z 1) (pow (v "c") (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (v "d"))
    (pow (v "c") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2))), ("osrIntegral2", (mul (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add
    (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow (add (v "c") (mul (v
    "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.or (.eq (add
    (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)) (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0)))]
  priority := 104394
  description := "RUBI 4.5.2.1, source rule 23 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:23"
    "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#23" "4.16.1"

/-- RUBI 4.5.2.1, source rule 27 (OSR legacy ID). -/
def rubi_4_5_2_1_r27 : CRule where
  id := "integration.source_4_5_2_1_r27"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:27"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (z 1) (pow (mul (v "c") (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v
    "d")))) (z (-1)))) (v "osrIntegral1")) (mul (mul (pow (v "d") (z 2)) (pow (mul (v "c") (add (mul (v "b")
    (v "c")) (mul (mul (z (-1)) (v "a")) (v "d")))) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (add (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d")))
    (mul (mul (mul (z (-1)) (v "b")) (v "d")) (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (pow (root
    (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))),
    ("osrIntegral2", (mul (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul (v
    "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow (add (v "c") (mul (v "d") (.app1 .csc
    (add (v "e") (mul (v "f") (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.or (.eq (add
    (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)) (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0)))]
  priority := 104398
  description := "RUBI 4.5.2.1, source rule 27 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:27"
    "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#27" "4.16.1"

/-- RUBI 4.5.2.1, source rule 29 (OSR legacy ID). -/
def rubi_4_5_2_1_r29 : CRule where
  id := "integration.source_4_5_2_1_r29"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:29"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root
    (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)))
  result := (mul (mul (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))))
    (z 2)) (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow
    (.app1 .cot (add (v "e") (mul (v "f") (v "x")))) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (.app1 .cot (add (v "e") (mul (v "f") (v "x")))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 104400
  description := "RUBI 4.5.2.1, source rule 29 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:29"
    "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#29" "4.16.1"

/-- RUBI 4.5.2.1, source rule 30 (OSR legacy ID). -/
def rubi_4_5_2_1_r30 : CRule where
  id := "integration.source_4_5_2_1_r30"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:30"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root
    (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)))
  result := (add (mul (v "c") (v "osrIntegral1")) (mul (v "d") (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))))
    (z 2)) (z (-1))))), ("osrIntegral2", (mul (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add
    (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow (root (add (v "c")
    (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0))]
  priority := 104401
  description := "RUBI 4.5.2.1, source rule 30 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:30"
    "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#30" "4.16.1"

/-- RUBI 4.5.2.1, source rule 31 (OSR legacy ID). -/
def rubi_4_5_2_1_r31 : CRule where
  id := "integration.source_4_5_2_1_r31"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:31"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (add (mul (mul (z 1) (pow (v "c") (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (v "d"))
    (pow (v "c") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z
    2)))), ("osrIntegral2", (mul (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul
    (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow (root (add (v "c") (mul (v "d")
    (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 104402
  description := "RUBI 4.5.2.1, source rule 31 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:31"
    "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#31" "4.16.1"

/-- RUBI 4.5.2.1, source rule 32 (OSR legacy ID). -/
def rubi_4_5_2_1_r32 : CRule where
  id := "integration.source_4_5_2_1_r32"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:32"
  x := "x"
  shape := .antiderivSubst
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (mul (mul (mul (z (-2)) (v "a")) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (z 1) (mul (mul (v "a") (v "c")) (pow (v "x") (z 2))))
    (z (-1)))))]
  substs := [("osrIntegral1", (mul (.app1 .cot (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root (add (v
    "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v
    "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 104403
  description := "RUBI 4.5.2.1, source rule 32 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:32"
    "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#32" "4.16.1"

/-- RUBI 4.5.2.1, source rule 33 (OSR legacy ID). -/
def rubi_4_5_2_1_r33 : CRule where
  id := "integration.source_4_5_2_1_r33"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:33"
  x := "x"
  shape := .antiderivRec
  body := (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (pow
    (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (add (mul (mul (v "a") (pow (v "c") (z (-1)))) (v "osrIntegral1")) (mul (mul (add (mul (v "b") (v
    "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (pow (v "c") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))))
    (z 2)) (z (-1))))), ("osrIntegral2", (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root
    (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c")
    (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 104404
  description := "RUBI 4.5.2.1, source rule 33 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:33"
    "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#33" "4.16.1"

/-- RUBI 4.5.2.1, source rule 35 (OSR legacy ID). -/
def rubi_4_5_2_1_r35 : CRule where
  id := "integration.source_4_5_2_1_r35"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:35"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z
    2))) (z (-1))))
  result := (mul (mul (.app1 .cot (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root (add (v "a") (mul (v
    "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .csc
    (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (.app1 .cot (add (v "e") (mul (v "f") (v "x")))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 104406
  description := "RUBI 4.5.2.1, source rule 35 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:35"
    "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#35" "4.16.1"

/-- RUBI 4.5.2.1, source rule 36 (OSR legacy ID). -/
def rubi_4_5_2_1_r36 : CRule where
  id := "integration.source_4_5_2_1_r36"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:36"
  x := "x"
  shape := .antiderivRec
  body := (mul (z 1) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z
    2))) (z (-1))))
  result := (add (mul (mul (z 1) (pow (v "a") (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (v "b"))
    (pow (v "a") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))))
    (z 2)) (z (-1))))), ("osrIntegral2", (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root
    (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c")
    (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0))]
  priority := 104407
  description := "RUBI 4.5.2.1, source rule 36 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:36"
    "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#36" "4.16.1"

/-- RUBI 4.5.2.1, source rule 39 (OSR legacy ID). -/
def rubi_4_5_2_1_r39 : CRule where
  id := "integration.source_4_5_2_1_r39"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:39"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (v "m")) (pow
    (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (v "n")))
  result := (v "osrIntegral1")
  integrals := [("osrIntegral1", (mul (mul (pow (add (v "b") (mul (v "a") (.app1 .sin (add (v "e") (mul (v
    "f") (v "x")))))) (v "m")) (pow (add (v "d") (mul (v "c") (.app1 .sin (add (v "e") (mul (v "f") (v
    "x")))))) (v "n"))) (pow (pow (.app1 .sin (add (v "e") (mul (v "f") (v "x")))) (add (v "m") (v "n"))) (z
    (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (Cond.int (v
    "m")), (Cond.int (v "n")), (.ge (add (v "m") (v "n")) (z (-2)))]
  priority := 104410
  description := "RUBI 4.5.2.1, source rule 39 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:39"
    "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#39" "4.16.1"

/-- RUBI 4.5.2.2, source rule 3 (OSR legacy ID). -/
def rubi_4_5_2_2_r3 : CRule where
  id := "integration.source_4_5_2_2_r3"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:3"
  x := "x"
  shape := .antideriv
  body := (mul (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add (v "c") (mul (v "d") (.app1
    .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow (root (add (v "a") (mul (v "b") (.app1 .csc (add
    (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (mul (mul (mul (mul (v "a") (v "c")) (.app1 .ln (add (z 1) (mul (mul (v "b") (pow (v "a") (z
    (-1)))) (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))))) (.app1 .cot (add (v "e") (mul (v "f") (v
    "x"))))) (pow (mul (mul (mul (v "b") (v "f")) (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e")
    (mul (v "f") (v "x")))))) (z 2))) (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2))) (z (-1))))
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.eq (add (mul (v "b") (v "c")) (mul (v "a") (v "d"))) (z 0)), (.eq (add (pow (v "a") (z 2))
    (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104421
  description := "RUBI 4.5.2.2, source rule 3 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:3"
    "4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n.m#3" "4.16.1"

/-- RUBI 4.5.2.2, source rule 16 (OSR legacy ID). -/
def rubi_4_5_2_2_r16 : CRule where
  id := "integration.source_4_5_2_2_r16"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:16"
  x := "x"
  shape := .antiderivSubst
  body := (mul (mul (root (mul (v "g") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (root (add (v
    "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow (add (v "c") (mul (v
    "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z (-1))))
  result := (mul (mul (mul (mul (z (-2)) (v "b")) (v "g")) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (add (mul (v "b") (v "c")) (mul (v "a") (v "d"))) (mul
    (mul (mul (z (-1)) (v "c")) (v "g")) (pow (v "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (mul (v "b") (.app1 .cot (add (v "e") (mul (v "f") (v "x"))))) (pow (mul
    (root (mul (v "g") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (root (add (v "a") (mul (v
    "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104434
  description := "RUBI 4.5.2.2, source rule 16 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:16"
    "4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n.m#16" "4.16.1"

/-- RUBI 4.5.2.2, source rule 18 (OSR legacy ID). -/
def rubi_4_5_2_2_r18 : CRule where
  id := "integration.source_4_5_2_2_r18"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:18"
  x := "x"
  shape := .antiderivSubst
  body := (mul (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul (v "b") (.app1
    .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow (add (v "c") (mul (v "d") (.app1 .csc (add (v
    "e") (mul (v "f") (v "x")))))) (z (-1))))
  result := (mul (mul (mul (z (-2)) (v "b")) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (add (mul (v "b") (v "c")) (mul (v "a") (v "d"))) (mul
    (v "d") (pow (v "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (mul (v "b") (.app1 .cot (add (v "e") (mul (v "f") (v "x"))))) (pow (root
    (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104436
  description := "RUBI 4.5.2.2, source rule 18 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:18"
    "4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n.m#18" "4.16.1"

/-- RUBI 4.5.2.2, source rule 23 (OSR legacy ID). -/
def rubi_4_5_2_2_r23 : CRule where
  id := "integration.source_4_5_2_2_r23"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:23"
  x := "x"
  shape := .antiderivRec
  body := (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root (add (v "a") (mul (v "b")
    (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (add (v "c") (mul (v "d") (.app1 .csc (add (v
    "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (v "b") (pow (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z
    (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (v "d")) (pow (add (mul (v "b") (v "c")) (mul (mul (z
    (-1)) (v "a")) (v "d"))) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (root (add (v "a")
    (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))), ("osrIntegral2", (mul
    (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul (v "b") (.app1 .csc (add (v
    "e") (mul (v "f") (v "x")))))) (z 2))) (pow (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v
    "f") (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.or (.eq (add
    (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)) (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0)))]
  priority := 104441
  description := "RUBI 4.5.2.2, source rule 23 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:23"
    "4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n.m#23" "4.16.1"

/-- RUBI 4.5.2.2, source rule 27 (OSR legacy ID). -/
def rubi_4_5_2_2_r27 : CRule where
  id := "integration.source_4_5_2_2_r27"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:27"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (z 2)) (pow (mul (root (add (v "a") (mul
    (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (add (v "c") (mul (v "d") (.app1 .csc
    (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (mul (z (-1)) (v "a")) (pow (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a"))
    (v "d"))) (z (-1)))) (v "osrIntegral1")) (mul (mul (v "c") (pow (add (mul (v "b") (v "c")) (mul (mul (z
    (-1)) (v "a")) (v "d"))) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (root (add (v "a")
    (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))), ("osrIntegral2", (mul
    (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul (v "b") (.app1 .csc (add (v
    "e") (mul (v "f") (v "x")))))) (z 2))) (pow (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v
    "f") (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.or (.eq (add
    (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)) (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0)))]
  priority := 104445
  description := "RUBI 4.5.2.2, source rule 27 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:27"
    "4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n.m#27" "4.16.1"

/-- RUBI 4.5.2.2, source rule 28 (OSR legacy ID). -/
def rubi_4_5_2_2_r28 : CRule where
  id := "integration.source_4_5_2_2_r28"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:28"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (z 2)) (pow (mul (root (add (v "a") (mul
    (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (add (v "c") (mul (v "d") (.app1 .csc
    (add (v "e") (mul (v "f") (v "x"))))))) (z (-1))))
  result := (add (mul (mul (z 1) (pow (v "d") (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (v "c"))
    (pow (v "d") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (root (add (v "a")
    (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))), ("osrIntegral2", (mul
    (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root (add (v "a") (mul (v "b") (.app1 .csc
    (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v
    "f") (v "x"))))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 104446
  description := "RUBI 4.5.2.2, source rule 28 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:28"
    "4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n.m#28" "4.16.1"

/-- RUBI 4.5.2.2, source rule 31 (OSR legacy ID). -/
def rubi_4_5_2_2_r31 : CRule where
  id := "integration.source_4_5_2_2_r31"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:31"
  x := "x"
  shape := .antiderivSubst
  body := (mul (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul (v "b") (.app1
    .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow (root (add (v "c") (mul (v "d") (.app1 .csc (add
    (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (mul (mul (mul (z (-2)) (v "b")) (pow (v "f") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (z 1) (mul (mul (mul (z (-1)) (v "b")) (v "d")) (pow (v
    "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (.app1 .cot (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root (add (v
    "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v
    "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 104449
  description := "RUBI 4.5.2.2, source rule 31 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:31"
    "4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n.m#31" "4.16.1"

/-- RUBI 4.5.2.2, source rule 32 (OSR legacy ID). -/
def rubi_4_5_2_2_r32 : CRule where
  id := "integration.source_4_5_2_2_r32"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:32"
  x := "x"
  shape := .antiderivRec
  body := (mul (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul (v "b") (.app1
    .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (pow (root (add (v "c") (mul (v "d") (.app1 .csc (add
    (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (add (mul (mul (mul (z (-1)) (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))))
    (pow (v "d") (z (-1)))) (v "osrIntegral1")) (mul (mul (v "b") (pow (v "d") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root (add (v
    "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v
    "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))), ("osrIntegral2", (mul (mul
    (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e")
    (mul (v "f") (v "x")))))) (z 2))) (pow (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v
    "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.eq (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 104450
  description := "RUBI 4.5.2.2, source rule 32 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:32"
    "4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n.m#32" "4.16.1"

/-- RUBI 4.5.2.2, source rule 34 (OSR legacy ID). -/
def rubi_4_5_2_2_r34 : CRule where
  id := "integration.source_4_5_2_2_r34"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:34"
  x := "x"
  shape := .antiderivSubst
  body := (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root (add (v "a") (mul (v "b")
    (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1 .csc (add
    (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))
  result := (mul (mul (mul (z (-2)) (v "a")) (pow (mul (v "b") (v "f")) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (z 1) (pow (add (z 2) (mul (add (mul (v "a") (v "c")) (mul (mul (z (-1))
    (v "b")) (v "d"))) (pow (v "x") (z 2)))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (.app1 .cot (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root (add (v
    "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v
    "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0))]
  priority := 104452
  description := "RUBI 4.5.2.2, source rule 34 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:34"
    "4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n.m#34" "4.16.1"

/-- RUBI 4.5.2.2, source rule 36 (OSR legacy ID). -/
def rubi_4_5_2_2_r36 : CRule where
  id := "integration.source_4_5_2_2_r36"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:36"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (z 2)) (pow (mul (root (add (v "a") (mul
    (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v "d") (.app1
    .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))
  result := (add (mul (mul (mul (z (-1)) (v "a")) (pow (v "b") (z (-1)))) (v "osrIntegral1")) (mul (mul (z 1)
    (pow (v "b") (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (mul (root (add (v
    "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (root (add (v "c") (mul (v
    "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))), ("osrIntegral2", (mul (mul
    (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e")
    (mul (v "f") (v "x")))))) (z 2))) (pow (root (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v
    "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0))]
  priority := 104454
  description := "RUBI 4.5.2.2, source rule 36 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:36"
    "4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n.m#36" "4.16.1"

/-- RUBI 4.5.3.1, source rule 40 (OSR legacy ID). -/
def rubi_4_5_3_1_r40 : CRule where
  id := "integration.source_4_5_3_1_r40"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec):40"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "A") (mul (v "B") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (pow (mul (root
    (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (root (add (v "a") (mul (v "b")
    (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1))))
  result := (add (mul (mul (v "A") (pow (v "a") (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (add
    (mul (v "A") (v "b")) (mul (mul (z (-1)) (v "a")) (v "B")))) (pow (mul (v "a") (v "d")) (z (-1)))) (v
    "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (pow (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z
    (-1))))), ("osrIntegral2", (mul (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z
    2)) (pow (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z
    (-1)))))]
  independent := ["A", "B", "a", "b", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "A") (v "b")) (mul (mul (z (-1)) (v "a")) (v "B"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104504
  description := "RUBI 4.5.3.1, source rule 40 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec):40"
    "4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec).m#40" "4.16.1"

/-- RUBI 4.5.3.1, source rule 42 (OSR legacy ID). -/
def rubi_4_5_3_1_r42 : CRule where
  id := "integration.source_4_5_3_1_r42"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec):42"
  x := "x"
  shape := .antiderivRec
  body := (mul (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))
    (add (v "A") (mul (v "B") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))))) (pow (root (mul (v "d")
    (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1))))
  result := (add (mul (mul (v "B") (pow (v "d") (z (-1)))) (v "osrIntegral1")) (mul (v "A") (v
    "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (z 2)) (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)))),
    ("osrIntegral2", (mul (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))))
    (z 2)) (pow (root (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))) (z 2)) (z (-1)))))]
  independent := ["A", "B", "a", "b", "d", "e", "f"]
  conditions := [(.ne (add (mul (v "A") (v "b")) (mul (mul (z (-1)) (v "a")) (v "B"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0))]
  priority := 104506
  description := "RUBI 4.5.3.1, source rule 42 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec):42"
    "4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec).m#42" "4.16.1"

/-- RUBI 4.5.4.1, source rule 11 (OSR legacy ID). -/
def rubi_4_5_4_1_r11 : CRule where
  id := "integration.source_4_5_4_1_r11"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.4.1 (a+b sec)^m (A+B sec+C sec^2):11"
  x := "x"
  shape := .antiderivRec
  body := (mul (add (v "A") (mul (v "C") (pow (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (z 2)))) (pow
    (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z (-1))))
  result := (add (mul (mul (v "C") (pow (v "b") (z (-1)))) (v "osrIntegral1")) (mul (mul (z 1) (pow (v "b") (z
    (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (.app1 .csc (add (v "e") (mul (v "f") (v "x"))))), ("osrIntegral2", (mul (add
    (mul (v "A") (v "b")) (mul (mul (mul (z (-1)) (v "a")) (v "C")) (.app1 .csc (add (v "e") (mul (v "f") (v
    "x")))))) (pow (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z (-1)))))]
  independent := ["A", "C", "a", "b", "e", "f"]
  priority := 104520
  description := "RUBI 4.5.4.1, source rule 11 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.4.1 (a+b sec)^m (A+B sec+C sec^2):11"
    "4 Trig functions/4.5 Secant/4.5.4.1 (a+b sec)^m (A+B sec+C sec^2).m#11" "4.16.1"

/-- RUBI 4.7.4, source rule 1 (OSR legacy ID). -/
def rubi_4_7_4_r1 : CRule where
  id := "integration.source_4_7_4_r1"
  legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:1"
  x := "x"
  shape := .antideriv
  body := (mul (.app1 .sin (add (v "a") (mul (v "b") (v "x")))) (.app1 .sin (add (v "c") (mul (v "d") (v
    "x")))))
  result := (add (mul (.app1 .sin (add (add (v "a") (mul (z (-1)) (v "c"))) (mul (add (v "b") (mul (z (-1)) (v
    "d"))) (v "x")))) (pow (mul (z 2) (add (v "b") (mul (z (-1)) (v "d")))) (z (-1)))) (mul (mul (z (-1))
    (.app1 .sin (add (add (v "a") (v "c")) (mul (add (v "b") (v "d")) (v "x"))))) (pow (mul (z 2) (add (v "b")
    (v "d"))) (z (-1)))))
  independent := ["a", "b", "c", "d"]
  conditions := [(.ne (add (pow (v "b") (z 2)) (mul (z (-1)) (pow (v "d") (z 2)))) (z 0))]
  priority := 104739
  description := "RUBI 4.7.4, source rule 1 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:1"
    "4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n.m#1" "4.16.1"

/-- RUBI 4.7.4, source rule 2 (OSR legacy ID). -/
def rubi_4_7_4_r2 : CRule where
  id := "integration.source_4_7_4_r2"
  legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:2"
  x := "x"
  shape := .antideriv
  body := (mul (.app1 .cos (add (v "a") (mul (v "b") (v "x")))) (.app1 .cos (add (v "c") (mul (v "d") (v
    "x")))))
  result := (add (mul (.app1 .sin (add (add (v "a") (mul (z (-1)) (v "c"))) (mul (add (v "b") (mul (z (-1)) (v
    "d"))) (v "x")))) (pow (mul (z 2) (add (v "b") (mul (z (-1)) (v "d")))) (z (-1)))) (mul (.app1 .sin (add
    (add (v "a") (v "c")) (mul (add (v "b") (v "d")) (v "x")))) (pow (mul (z 2) (add (v "b") (v "d"))) (z
    (-1)))))
  independent := ["a", "b", "c", "d"]
  conditions := [(.ne (add (pow (v "b") (z 2)) (mul (z (-1)) (pow (v "d") (z 2)))) (z 0))]
  priority := 104740
  description := "RUBI 4.7.4, source rule 2 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:2"
    "4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n.m#2" "4.16.1"

/-- RUBI 4.7.4, source rule 3 (OSR legacy ID). -/
def rubi_4_7_4_r3 : CRule where
  id := "integration.source_4_7_4_r3"
  legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:3"
  x := "x"
  shape := .antideriv
  body := (mul (.app1 .sin (add (v "a") (mul (v "b") (v "x")))) (.app1 .cos (add (v "c") (mul (v "d") (v
    "x")))))
  result := (add (mul (mul (z (-1)) (.app1 .cos (add (add (v "a") (mul (z (-1)) (v "c"))) (mul (add (v "b")
    (mul (z (-1)) (v "d"))) (v "x"))))) (pow (mul (z 2) (add (v "b") (mul (z (-1)) (v "d")))) (z (-1)))) (mul
    (mul (z (-1)) (.app1 .cos (add (add (v "a") (v "c")) (mul (add (v "b") (v "d")) (v "x"))))) (pow (mul (z
    2) (add (v "b") (v "d"))) (z (-1)))))
  independent := ["a", "b", "c", "d"]
  conditions := [(.ne (add (pow (v "b") (z 2)) (mul (z (-1)) (pow (v "d") (z 2)))) (z 0))]
  priority := 104741
  description := "RUBI 4.7.4, source rule 3 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:3"
    "4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n.m#3" "4.16.1"

/-- RUBI 4.7.4, source rule 24 (OSR legacy ID). -/
def rubi_4_7_4_r24 : CRule where
  id := "integration.source_4_7_4_r24"
  legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:24"
  x := "x"
  shape := .antideriv
  body := (mul (.app1 .cos (add (v "a") (mul (v "b") (v "x")))) (pow (root (.app1 .sin (add (v "c") (mul (v
    "d") (v "x")))) (z 2)) (z (-1))))
  result := (add (mul (mul (z (-1)) (.app1 .arcsin (add (.app1 .cos (add (v "a") (mul (v "b") (v "x")))) (mul
    (z (-1)) (.app1 .sin (add (v "a") (mul (v "b") (v "x")))))))) (pow (v "d") (z (-1)))) (mul (.app1 .ln (add
    (add (.app1 .cos (add (v "a") (mul (v "b") (v "x")))) (.app1 .sin (add (v "a") (mul (v "b") (v "x")))))
    (root (.app1 .sin (add (v "c") (mul (v "d") (v "x")))) (z 2)))) (pow (v "d") (z (-1)))))
  independent := ["a", "b", "c", "d"]
  conditions := [(.eq (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (mul (v
    "d") (pow (v "b") (z (-1)))) (z 2))]
  priority := 104762
  description := "RUBI 4.7.4, source rule 24 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:24"
    "4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n.m#24" "4.16.1"

/-- RUBI 4.7.4, source rule 25 (OSR legacy ID). -/
def rubi_4_7_4_r25 : CRule where
  id := "integration.source_4_7_4_r25"
  legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:25"
  x := "x"
  shape := .antideriv
  body := (mul (.app1 .sin (add (v "a") (mul (v "b") (v "x")))) (pow (root (.app1 .sin (add (v "c") (mul (v
    "d") (v "x")))) (z 2)) (z (-1))))
  result := (add (mul (mul (z (-1)) (.app1 .arcsin (add (.app1 .cos (add (v "a") (mul (v "b") (v "x")))) (mul
    (z (-1)) (.app1 .sin (add (v "a") (mul (v "b") (v "x")))))))) (pow (v "d") (z (-1)))) (mul (mul (z (-1))
    (.app1 .ln (add (add (.app1 .cos (add (v "a") (mul (v "b") (v "x")))) (.app1 .sin (add (v "a") (mul (v
    "b") (v "x"))))) (root (.app1 .sin (add (v "c") (mul (v "d") (v "x")))) (z 2))))) (pow (v "d") (z (-1)))))
  independent := ["a", "b", "c", "d"]
  conditions := [(.eq (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.eq (mul (v
    "d") (pow (v "b") (z (-1)))) (z 2))]
  priority := 104763
  description := "RUBI 4.7.4, source rule 25 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:25"
    "4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n.m#25" "4.16.1"

/-- RUBI 5.3.7, source rule 51 (OSR legacy ID). -/
def rubi_5_3_7_r51 : CRule where
  id := "integration.source_5_3_7_r51"
  legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:51"
  x := "x"
  shape := .antiderivRec
  body := (.app1 .arctan (add (v "c") (mul (v "d") (.app1 .tanh (add (v "a") (mul (v "b") (v "x")))))))
  result := (add (mul (v "x") (.app1 .arctan (add (v "c") (mul (v "d") (.app1 .tanh (add (v "a") (mul (v "b")
    (v "x")))))))) (mul (mul (z (-1)) (v "b")) (v "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (v "x") (pow (add (add (v "c") (mul (z (-1)) (v "d"))) (mul (v "c")
    (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul (z 2) (v "b")) (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.eq (pow (add (v "c") (mul (z (-1)) (v "d"))) (z 2)) (z (-1)))]
  priority := 105659
  description := "RUBI 5.3.7, source rule 51 (OSR legacy ID)"
  provenance := source "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:51"
    "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#51" "4.16.1"

/-- RUBI 5.3.7, source rule 53 (OSR legacy ID). -/
def rubi_5_3_7_r53 : CRule where
  id := "integration.source_5_3_7_r53"
  legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:53"
  x := "x"
  shape := .antiderivRec
  body := (.app1 .arctan (add (v "c") (mul (v "d") (.app1 .coth (add (v "a") (mul (v "b") (v "x")))))))
  result := (add (mul (v "x") (.app1 .arctan (add (v "c") (mul (v "d") (.app1 .coth (add (v "a") (mul (v "b")
    (v "x")))))))) (mul (mul (z (-1)) (v "b")) (v "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (v "x") (pow (add (add (v "c") (mul (z (-1)) (v "d"))) (mul (mul (z
    (-1)) (v "c")) (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul (z 2) (v "b")) (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.eq (pow (add (v "c") (mul (z (-1)) (v "d"))) (z 2)) (z (-1)))]
  priority := 105661
  description := "RUBI 5.3.7, source rule 53 (OSR legacy ID)"
  provenance := source "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:53"
    "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#53" "4.16.1"

/-- RUBI 6.7.9, source rule 46 (OSR legacy ID). -/
def rubi_6_7_9_r46 : CRule where
  id := "integration.source_6_7_9_r46"
  legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:46"
  x := "x"
  shape := .antiderivRec
  body := (mul (.app1 .cosh (add (v "a") (mul (v "b") (v "x")))) (.app1 .coth (add (v "c") (mul (v "d") (v
    "x")))))
  result := (v "osrIntegral1")
  integrals := [("osrIntegral1", (add (add (add (mul (.app1 .exp (mul (z (-1)) (add (v "a") (mul (v "b") (v
    "x"))))) (pow (z 2) (z (-1)))) (mul (.app1 .exp (add (v "a") (mul (v "b") (v "x")))) (pow (z 2) (z
    (-1))))) (mul (mul (z (-1)) (.app1 .exp (mul (z (-1)) (add (v "a") (mul (v "b") (v "x")))))) (pow (add (z
    1) (mul (z (-1)) (.app1 .exp (mul (z 2) (add (v "c") (mul (v "d") (v "x"))))))) (z (-1))))) (mul (mul (z
    (-1)) (.app1 .exp (add (v "a") (mul (v "b") (v "x"))))) (pow (add (z 1) (mul (z (-1)) (.app1 .exp (mul (z
    2) (add (v "c") (mul (v "d") (v "x"))))))) (z (-1))))))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.ne (add (pow (v "b") (z 2)) (mul (z (-1)) (pow (v "d") (z 2)))) (z 0))]
  priority := 106079
  description := "RUBI 6.7.9, source rule 46 (OSR legacy ID)"
  provenance := source "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:46"
    "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#46" "4.16.1"

/-- RUBI 6.7.9, source rule 47 (OSR legacy ID). -/
def rubi_6_7_9_r47 : CRule where
  id := "integration.source_6_7_9_r47"
  legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:47"
  x := "x"
  shape := .antiderivRec
  body := (mul (.app1 .sinh (add (v "a") (mul (v "b") (v "x")))) (.app1 .coth (add (v "c") (mul (v "d") (v
    "x")))))
  result := (v "osrIntegral1")
  integrals := [("osrIntegral1", (add (add (add (mul (mul (z (-1)) (.app1 .exp (mul (z (-1)) (add (v "a") (mul
    (v "b") (v "x")))))) (pow (z 2) (z (-1)))) (mul (.app1 .exp (add (v "a") (mul (v "b") (v "x")))) (pow (z
    2) (z (-1))))) (mul (.app1 .exp (mul (z (-1)) (add (v "a") (mul (v "b") (v "x"))))) (pow (add (z 1) (mul
    (z (-1)) (.app1 .exp (mul (z 2) (add (v "c") (mul (v "d") (v "x"))))))) (z (-1))))) (mul (mul (z (-1))
    (.app1 .exp (add (v "a") (mul (v "b") (v "x"))))) (pow (add (z 1) (mul (z (-1)) (.app1 .exp (mul (z 2)
    (add (v "c") (mul (v "d") (v "x"))))))) (z (-1))))))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.ne (add (pow (v "b") (z 2)) (mul (z (-1)) (pow (v "d") (z 2)))) (z 0))]
  priority := 106080
  description := "RUBI 6.7.9, source rule 47 (OSR legacy ID)"
  provenance := source "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:47"
    "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#47" "4.16.1"

/-- RUBI 7.2.3, source rule 3 (OSR legacy ID). -/
def rubi_7_2_3_r3 : CRule where
  id := "integration.source_7_2_3_r3"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n:3"
  x := "x"
  shape := .antideriv
  body := (mul (z 1) (pow (mul (mul (root (add (v "d1") (mul (v "e1") (v "x"))) (z 2)) (root (add (v "d2")
    (mul (v "e2") (v "x"))) (z 2))) (add (v "a") (mul (v "b") (.app1 .arccosh (mul (v "c") (v "x")))))) (z
    (-1))))
  result := (mul (mul (mul (mul (z 1) (pow (mul (v "b") (v "c")) (z (-1)))) (mul (root (add (z 1) (mul (v "c")
    (v "x"))) (z 2)) (pow (root (add (v "d1") (mul (v "e1") (v "x"))) (z 2)) (z (-1))))) (mul (root (add (z
    (-1)) (mul (v "c") (v "x"))) (z 2)) (pow (root (add (v "d2") (mul (v "e2") (v "x"))) (z 2)) (z (-1)))))
    (.app1 .ln (add (v "a") (mul (v "b") (.app1 .arccosh (mul (v "c") (v "x")))))))
  independent := ["a", "b", "c", "d1", "d2", "e1", "e2"]
  conditions := [(.eq (v "e1") (mul (v "c") (v "d1"))), (.eq (v "e2") (mul (mul (z (-1)) (v "c")) (v "d2")))]
  priority := 106249
  description := "RUBI 7.2.3, source rule 3 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n:3"
    "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n.m#3" "4.16.1"

/-- RUBI 7.3.7, source rule 25 (OSR legacy ID). -/
def rubi_7_3_7_r25 : CRule where
  id := "integration.source_7_3_7_r25"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:25"
  x := "x"
  shape := .antiderivRec
  body := (.app1 .arctanh (add (v "c") (mul (v "d") (.app1 .tanh (add (v "a") (mul (v "b") (v "x")))))))
  result := (add (mul (v "x") (.app1 .arctanh (add (v "c") (mul (v "d") (.app1 .tanh (add (v "a") (mul (v "b")
    (v "x")))))))) (mul (v "b") (v "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (v "x") (pow (add (add (v "c") (mul (z (-1)) (v "d"))) (mul (v "c")
    (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul (z 2) (v "b")) (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.eq (pow (add (v "c") (mul (z (-1)) (v "d"))) (z 2)) (z 1))]
  priority := 106724
  description := "RUBI 7.3.7, source rule 25 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:25"
    "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#25" "4.16.1"

/-- RUBI 7.3.7, source rule 27 (OSR legacy ID). -/
def rubi_7_3_7_r27 : CRule where
  id := "integration.source_7_3_7_r27"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:27"
  x := "x"
  shape := .antiderivRec
  body := (.app1 .arctanh (add (v "c") (mul (v "d") (.app1 .coth (add (v "a") (mul (v "b") (v "x")))))))
  result := (add (mul (v "x") (.app1 .arctanh (add (v "c") (mul (v "d") (.app1 .coth (add (v "a") (mul (v "b")
    (v "x")))))))) (mul (v "b") (v "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (v "x") (pow (add (add (v "c") (mul (z (-1)) (v "d"))) (mul (mul (z
    (-1)) (v "c")) (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul (z 2) (v "b")) (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.eq (pow (add (v "c") (mul (z (-1)) (v "d"))) (z 2)) (z 1))]
  priority := 106726
  description := "RUBI 7.3.7, source rule 27 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:27"
    "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#27" "4.16.1"

/-- RUBI 7.3.7, source rule 29 (OSR legacy ID). -/
def rubi_7_3_7_r29 : CRule where
  id := "integration.source_7_3_7_r29"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:29"
  x := "x"
  shape := .antiderivRec
  body := (.app1 .arctanh (add (v "c") (mul (v "d") (.app1 .tanh (add (v "a") (mul (v "b") (v "x")))))))
  result := (add (add (mul (v "x") (.app1 .arctanh (add (v "c") (mul (v "d") (.app1 .tanh (add (v "a") (mul (v
    "b") (v "x")))))))) (mul (mul (v "b") (add (add (z 1) (mul (z (-1)) (v "c"))) (mul (z (-1)) (v "d")))) (v
    "osrIntegral1"))) (mul (mul (mul (z (-1)) (v "b")) (add (add (z 1) (v "c")) (v "d"))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (mul (v "x") (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul (z 2) (v
    "b")) (v "x"))))) (pow (add (add (add (z 1) (mul (z (-1)) (v "c"))) (v "d")) (mul (add (add (z 1) (mul (z
    (-1)) (v "c"))) (mul (z (-1)) (v "d"))) (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul (z 2) (v "b")) (v
    "x")))))) (z (-1))))), ("osrIntegral2", (mul (mul (v "x") (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul
    (z 2) (v "b")) (v "x"))))) (pow (add (add (add (z 1) (v "c")) (mul (z (-1)) (v "d"))) (mul (add (add (z 1)
    (v "c")) (v "d")) (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul (z 2) (v "b")) (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.ne (pow (add (v "c") (mul (z (-1)) (v "d"))) (z 2)) (z 1))]
  priority := 106728
  description := "RUBI 7.3.7, source rule 29 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:29"
    "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#29" "4.16.1"

/-- RUBI 7.3.7, source rule 31 (OSR legacy ID). -/
def rubi_7_3_7_r31 : CRule where
  id := "integration.source_7_3_7_r31"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:31"
  x := "x"
  shape := .antiderivRec
  body := (.app1 .arctanh (add (v "c") (mul (v "d") (.app1 .coth (add (v "a") (mul (v "b") (v "x")))))))
  result := (add (add (mul (v "x") (.app1 .arctanh (add (v "c") (mul (v "d") (.app1 .coth (add (v "a") (mul (v
    "b") (v "x")))))))) (mul (mul (v "b") (add (add (z 1) (v "c")) (v "d"))) (v "osrIntegral1"))) (mul (mul
    (mul (z (-1)) (v "b")) (add (add (z 1) (mul (z (-1)) (v "c"))) (mul (z (-1)) (v "d")))) (v
    "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (mul (v "x") (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul (z 2) (v
    "b")) (v "x"))))) (pow (add (add (add (z 1) (v "c")) (mul (z (-1)) (v "d"))) (mul (mul (z (-1)) (add (add
    (z 1) (v "c")) (v "d"))) (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul (z 2) (v "b")) (v "x")))))) (z
    (-1))))), ("osrIntegral2", (mul (mul (v "x") (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul (z 2) (v "b"))
    (v "x"))))) (pow (add (add (add (z 1) (mul (z (-1)) (v "c"))) (v "d")) (mul (mul (z (-1)) (add (add (z 1)
    (mul (z (-1)) (v "c"))) (mul (z (-1)) (v "d")))) (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul (z 2) (v
    "b")) (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [(.ne (pow (add (v "c") (mul (z (-1)) (v "d"))) (z 2)) (z 1))]
  priority := 106730
  description := "RUBI 7.3.7, source rule 31 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:31"
    "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#31" "4.16.1"

/-- RUBI 7.3.7, source rule 43 (OSR legacy ID). -/
def rubi_7_3_7_r43 : CRule where
  id := "integration.source_7_3_7_r43"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:43"
  x := "x"
  shape := .antiderivRec
  body := (.app1 .arctanh (.app1 .cot (add (v "a") (mul (v "b") (v "x")))))
  result := (add (mul (v "x") (.app1 .arctanh (.app1 .cot (add (v "a") (mul (v "b") (v "x")))))) (mul (mul (z
    (-1)) (v "b")) (v "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (v "x") (.app1 .sec (add (mul (z 2) (v "a")) (mul (mul (z 2) (v "b")) (v
    "x"))))))]
  independent := ["a", "b"]
  priority := 106742
  description := "RUBI 7.3.7, source rule 43 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:43"
    "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#43" "4.16.1"

private def part1 : List CEntry := [
  { rule := rubi_1_1_1_2_r22, ruleDecl := ``rubi_1_1_1_2_r22,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_1_1_2_r23, ruleDecl := ``rubi_1_1_1_2_r23,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_1_1_4_r28, ruleDecl := ``rubi_1_1_1_4_r28,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_1_2_1_r19, ruleDecl := ``rubi_1_1_2_1_r19,
    proofs := [], unproved := [],
    counterexamples := [(.real, ``rubi_1_1_2_1_r19_counterexample_real)], findings := ["Same pattern, guards and result as integration.rubi_1_1_3_1_r21.", "counterexample: at b = 3 and the other metavariables 0 the conditions hold and the integrand is defined near x = 3, but the integrand of the first integral in the result is not defined where it is evaluated for x = 3 (Lean theorem rubi1131r21_counterexample_real). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.", "residual integrals: the result contains Int[…], exported as int(λx. H)(x) (the calculus1#int FMP form); the statement holds for every choice of antiderivatives of the residual integrands. The reference rewriter does not apply this rule.", "conditions: RUBI's Not[GtQ[a, 0]] become OSR v1 conditions (relation1#neq, relation1#eq, relation1#gt, set1#in with setname1#Z), read semantically on defined values.", "matching: the optional wildcard b. of the v0.1 pattern is an ordinary metavariable; the v1 rule does not match the instances with RUBI's default value.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#geq.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_1_2_3_r29, ruleDecl := ``rubi_1_1_2_3_r29,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_1_2_7_r47, ruleDecl := ``rubi_1_1_2_7_r47,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_1_2_9_r36, ruleDecl := ``rubi_1_1_2_9_r36,
    proofs := [], unproved := [],
    counterexamples := [(.real, ``rubi_1_1_2_9_r36_counterexample_real), (.complex, ``rubi_1_1_2_9_r36_counterexample_complex)], findings := ["Same pattern, guards and result as integration.rubi_1_2_1_3_r14.", "counterexample: at e = 1, f = 1, g = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r14_counterexample_real and rubi1213r14_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.", "residual integrals: the result contains Int[…], exported as int(λx. H)(x) (the calculus1#int FMP form); the statement holds for every choice of antiderivatives of the residual integrands. The reference rewriter does not apply this rule.", "conditions: RUBI's EqQ[Add[Multiply[a, e, g], Multiply[-1, c, d, f, Add[Multiply[2, p], 3]]], 0]; NeQ[p, -1] become OSR v1 conditions (relation1#neq, relation1#eq, relation1#gt, set1#in with setname1#Z), read semantically on defined values.", "matching: the optional wildcards d., e., f., g. and c. of the v0.1 pattern are ordinary metavariables; the v1 rule does not match the instances with RUBI's default values.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_2_1_1_r12, ruleDecl := ``rubi_1_2_1_1_r12,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_2_1_2_r97, ruleDecl := ``rubi_1_2_1_2_r97,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_2_1_3_r5, ruleDecl := ``rubi_1_2_1_3_r5,
    proofs := [], unproved := [],
    counterexamples := [(.real, ``rubi_1_2_1_3_r5_counterexample_real), (.complex, ``rubi_1_2_1_3_r5_counterexample_complex)], findings := ["Same pattern, guards and result as integration.rubi_1_2_1_3_r5.", "counterexample: at a = 1, e = 1, f = 1, g = 1, m = 1, p = -2 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1213r5_counterexample_real and rubi1213r5_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.", "residual integrals: the result contains Int[…], exported as int(λx. H)(x) (the calculus1#int FMP form); the statement holds for every choice of antiderivatives of the residual integrands. The reference rewriter does not apply this rule.", "conditions: RUBI's EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; EqQ[Add[m, Multiply[2, p], 3], 0]; EqQ[Add[Multiply[2, c, f], Multiply[-1, b, g]], 0] become OSR v1 conditions (relation1#neq, relation1#eq, relation1#gt, set1#in with setname1#Z), read semantically on defined values.", "matching: the optional wildcards d., e., m., g., b., c. and p. of the v0.1 pattern are ordinary metavariables; the v1 rule does not match the instances with RUBI's default values.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part2 : List CEntry := [
  { rule := rubi_1_2_2_3_r34, ruleDecl := ``rubi_1_2_2_3_r34,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_2_2_3_r35, ruleDecl := ``rubi_1_2_2_3_r35,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_4_1_r26, ruleDecl := ``rubi_1_4_1_r26,
    proofs := [], unproved := [],
    counterexamples := [(.real, ``rubi_1_4_1_r26_counterexample_real), (.complex, ``rubi_1_4_1_r26_counterexample_complex)], findings := ["Same pattern, guards and result as integration.rubi_1_1_1_7_r6.", "counterexample: at b2 = 1, m = 1, n = 1, p = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorems rubi1117r6_counterexample_real and rubi1117r6_counterexample_complex). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.", "residual integrals: the result contains Int[…], exported as int(λx. H)(x) (the calculus1#int FMP form); the statement holds for every choice of antiderivatives of the residual integrands. The reference rewriter does not apply this rule.", "conditions: RUBI's EqQ[Add[Multiply[a2, b1], Multiply[a1, b2]], 0]; EqQ[Add[m, Multiply[-1, 2, n], 1], 0]; NeQ[p, -1] become OSR v1 conditions (relation1#neq, relation1#eq, relation1#gt, set1#in with setname1#Z), read semantically on defined values.", "matching: the optional wildcards m., b1., n. and b2. of the v0.1 pattern are ordinary metavariables; the v1 rule does not match the instances with RUBI's default values.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_2_2_7_r10, ruleDecl := ``rubi_1_2_2_7_r10,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_2_2_7_r11, ruleDecl := ``rubi_1_2_2_7_r11,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_2_2_7_r12, ruleDecl := ``rubi_1_2_2_7_r12,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_4_3_r12, ruleDecl := ``rubi_1_4_3_r12,
    proofs := [], unproved := [],
    counterexamples := [(.real, ``rubi_1_4_3_r12_counterexample_real)], findings := ["Same pattern, guards and result as integration.rubi_1_3_3_r7.", "counterexample: at a = 1, d = 1, f = 1, g = 1, h = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorem rubi133r7_counterexample_real). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.", "conditions: RUBI's EqQ[Add[Power[Add[Multiply[e, g], Multiply[-1, d, h]], 2], Multiply[-1, Power[f, 2], Add[Multiply[c, Power[g, 2]], Multiply[-1, b, g, h], Multiply[a, Power[h, 2]]]]], 0]; EqQ[Add[Multiply[2, Power[e, 2], g], Multiply[-1, 2, d, e, h], Multiply[-1, Power[f, 2], Add[Multiply[2, c, g], Multiply[-1, b, h]]]], 0] become OSR v1 conditions (relation1#neq, relation1#eq, relation1#gt, set1#in with setname1#Z), read semantically on defined values.", "matching: the optional wildcards g., h., d., e., f., a., b. and c. of the v0.1 pattern are ordinary metavariables; the v1 rule does not match the instances with RUBI's default values.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_4_3_r29, ruleDecl := ``rubi_1_4_3_r29,
    proofs := [], unproved := [],
    counterexamples := [(.real, ``rubi_1_4_3_r29_counterexample_real)], findings := ["Same pattern, guards and result as integration.rubi_1_3_3_r22.", "counterexample: at c = 1 and the other metavariables 0 the conditions hold and the integrand is defined everywhere, but the result is not defined at x = 1 (Lean theorem rubi133r22_counterexample_real). RUBI excludes this case by its rule order or by evaluation; the v1 rule, stated on its own, needs a condition that this migration does not add.", "conditions: RUBI's EqQ[Add[Power[a, 2], Multiply[-1, Power[b, 2], c]], 0] become OSR v1 conditions (relation1#neq, relation1#eq, relation1#gt, set1#in with setname1#Z), read semantically on defined values.", "matching: the optional wildcards b. and d. of the v0.1 pattern are ordinary metavariables; the v1 rule does not match the instances with RUBI's default values.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_4_3_r31, ruleDecl := ``rubi_1_4_3_r31,
    proofs := [(.real, ``rubi_1_4_3_r31_real)], unproved := [],
    counterexamples := [], findings := ["Same pattern, guards and result as integration.rubi_1_3_3_r24.", "residual integrals: the result contains Int[…], exported as int(λx. H)(x) (the calculus1#int FMP form); the statement holds for every choice of antiderivatives of the residual integrands. The reference rewriter does not apply this rule.", "conditions: RUBI's EqQ[Add[Power[a, 2], Multiply[-1, Power[b, 2], d]], 0]; EqQ[Add[Multiply[Power[b, 2], c, e], a], 0] become OSR v1 conditions (relation1#neq, relation1#eq, relation1#gt, set1#in with setname1#Z), read semantically on defined values.", "matching: the optional wildcards e., a., b. and d. of the v0.1 pattern are ordinary metavariables; the v1 rule does not match the instances with RUBI's default values.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_3_3_r5, ruleDecl := ``rubi_3_3_r5,
    proofs := [], unproved := [.real, .complex],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part3 : List CEntry := [
  { rule := rubi_4_1_0_1_r11, ruleDecl := ``rubi_4_1_0_1_r11,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_0_2_r24, ruleDecl := ``rubi_4_1_0_2_r24,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#sec.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_1_1_r26, ruleDecl := ``rubi_4_1_1_1_r26,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#geq.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_1_3_r25, ruleDecl := ``rubi_4_1_1_3_r25,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_1_r8, ruleDecl := ``rubi_4_1_2_1_r8,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_1_r41, ruleDecl := ``rubi_4_1_2_1_r41,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_1_r47, ruleDecl := ``rubi_4_1_2_1_r47,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_1_r48, ruleDecl := ``rubi_4_1_2_1_r48,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_1_r74, ruleDecl := ``rubi_4_1_2_1_r74,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#geq.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_2_r73, ruleDecl := ``rubi_4_1_2_2_r73,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part4 : List CEntry := [
  { rule := rubi_4_1_2_2_r74, ruleDecl := ``rubi_4_1_2_2_r74,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_2_r75, ruleDecl := ``rubi_4_1_2_2_r75,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_3_r3, ruleDecl := ``rubi_4_1_2_3_r3,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_3_r6, ruleDecl := ``rubi_4_1_2_3_r6,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_3_r7, ruleDecl := ``rubi_4_1_2_3_r7,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_3_r11, ruleDecl := ``rubi_4_1_2_3_r11,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_3_r12, ruleDecl := ``rubi_4_1_2_3_r12,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_3_r13, ruleDecl := ``rubi_4_1_2_3_r13,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_3_r15, ruleDecl := ``rubi_4_1_2_3_r15,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_3_r16, ruleDecl := ``rubi_4_1_2_3_r16,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part5 : List CEntry := [
  { rule := rubi_4_1_2_3_r17, ruleDecl := ``rubi_4_1_2_3_r17,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_3_r19, ruleDecl := ``rubi_4_1_2_3_r19,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_3_r20, ruleDecl := ``rubi_4_1_2_3_r20,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_3_r21, ruleDecl := ``rubi_4_1_2_3_r21,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_2_3_r22, ruleDecl := ``rubi_4_1_2_3_r22,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_3_1_r4, ruleDecl := ``rubi_4_1_3_1_r4,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_3_1_r17, ruleDecl := ``rubi_4_1_3_1_r17,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_3_1_r20, ruleDecl := ``rubi_4_1_3_1_r20,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_3_1_r40, ruleDecl := ``rubi_4_1_3_1_r40,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_3_1_r41, ruleDecl := ``rubi_4_1_3_1_r41,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part6 : List CEntry := [
  { rule := rubi_4_1_4_2_r32, ruleDecl := ``rubi_4_1_4_2_r32,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_6_r44, ruleDecl := ``rubi_4_1_6_r44,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#sec.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_6_r45, ruleDecl := ``rubi_4_1_6_r45,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_7_r13, ruleDecl := ``rubi_4_1_7_r13,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#geq.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_3_1_2_r4, ruleDecl := ``rubi_4_3_1_2_r4,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#sec.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_3_2_1_r11, ruleDecl := ``rubi_4_3_2_1_r11,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_3_2_1_r12, ruleDecl := ``rubi_4_3_2_1_r12,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_3_2_1_r13, ruleDecl := ``rubi_4_3_2_1_r13,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_3_2_1_r22, ruleDecl := ``rubi_4_3_2_1_r22,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_3_2_1_r41, ruleDecl := ``rubi_4_3_2_1_r41,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part7 : List CEntry := [
  { rule := rubi_4_3_7_r3, ruleDecl := ``rubi_4_3_7_r3,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#sec.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_3_10_r9, ruleDecl := ``rubi_4_3_10_r9,
    proofs := [], unproved := [.real, .complex],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_3_10_r11, ruleDecl := ``rubi_4_3_10_r11,
    proofs := [], unproved := [.real, .complex],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_3_12_r6, ruleDecl := ``rubi_4_3_12_r6,
    proofs := [], unproved := [.real, .complex],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_1_r10, ruleDecl := ``rubi_4_5_1_1_r10,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_2_r8, ruleDecl := ``rubi_4_5_1_2_r8,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_2_r9, ruleDecl := ``rubi_4_5_1_2_r9,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_2_r15, ruleDecl := ``rubi_4_5_1_2_r15,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#gt, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_2_r16, ruleDecl := ``rubi_4_5_1_2_r16,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#geq, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_2_r18, ruleDecl := ``rubi_4_5_1_2_r18,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part8 : List CEntry := [
  { rule := rubi_4_5_1_2_r21, ruleDecl := ``rubi_4_5_1_2_r21,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#gt, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_2_r22, ruleDecl := ``rubi_4_5_1_2_r22,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_2_r43, ruleDecl := ``rubi_4_5_1_2_r43,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_2_r70, ruleDecl := ``rubi_4_5_1_2_r70,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_2_r72, ruleDecl := ``rubi_4_5_1_2_r72,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_2_r76, ruleDecl := ``rubi_4_5_1_2_r76,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_4_r5, ruleDecl := ``rubi_4_5_1_4_r5,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_4_r14, ruleDecl := ``rubi_4_5_1_4_r14,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_1_r14, ruleDecl := ``rubi_4_5_2_1_r14,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_1_r18, ruleDecl := ``rubi_4_5_2_1_r18,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part9 : List CEntry := [
  { rule := rubi_4_5_2_1_r23, ruleDecl := ``rubi_4_5_2_1_r23,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_1_r27, ruleDecl := ``rubi_4_5_2_1_r27,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_1_r29, ruleDecl := ``rubi_4_5_2_1_r29,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_1_r30, ruleDecl := ``rubi_4_5_2_1_r30,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_1_r31, ruleDecl := ``rubi_4_5_2_1_r31,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_1_r32, ruleDecl := ``rubi_4_5_2_1_r32,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_1_r33, ruleDecl := ``rubi_4_5_2_1_r33,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_1_r35, ruleDecl := ``rubi_4_5_2_1_r35,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_1_r36, ruleDecl := ``rubi_4_5_2_1_r36,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_1_r39, ruleDecl := ``rubi_4_5_2_1_r39,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#geq, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part10 : List CEntry := [
  { rule := rubi_4_5_2_2_r3, ruleDecl := ``rubi_4_5_2_2_r3,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_2_r16, ruleDecl := ``rubi_4_5_2_2_r16,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_2_r18, ruleDecl := ``rubi_4_5_2_2_r18,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_2_r23, ruleDecl := ``rubi_4_5_2_2_r23,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_2_r27, ruleDecl := ``rubi_4_5_2_2_r27,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_2_r28, ruleDecl := ``rubi_4_5_2_2_r28,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_2_r31, ruleDecl := ``rubi_4_5_2_2_r31,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_2_r32, ruleDecl := ``rubi_4_5_2_2_r32,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_2_r34, ruleDecl := ``rubi_4_5_2_2_r34,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_2_2_r36, ruleDecl := ``rubi_4_5_2_2_r36,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part11 : List CEntry := [
  { rule := rubi_4_5_3_1_r40, ruleDecl := ``rubi_4_5_3_1_r40,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_3_1_r42, ruleDecl := ``rubi_4_5_3_1_r42,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_4_1_r11, ruleDecl := ``rubi_4_5_4_1_r11,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_7_4_r1, ruleDecl := ``rubi_4_7_4_r1,
    proofs := [], unproved := [.real, .complex],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_7_4_r2, ruleDecl := ``rubi_4_7_4_r2,
    proofs := [], unproved := [.real, .complex],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_7_4_r3, ruleDecl := ``rubi_4_7_4_r3,
    proofs := [], unproved := [.real, .complex],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_7_4_r24, ruleDecl := ``rubi_4_7_4_r24,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#arcsin.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_7_4_r25, ruleDecl := ``rubi_4_7_4_r25,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#arcsin.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_5_3_7_r51, ruleDecl := ``rubi_5_3_7_r51,
    proofs := [], unproved := [.real, .complex],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_5_3_7_r53, ruleDecl := ``rubi_5_3_7_r53,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#coth.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part12 : List CEntry := [
  { rule := rubi_6_7_9_r46, ruleDecl := ``rubi_6_7_9_r46,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#coth.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_6_7_9_r47, ruleDecl := ``rubi_6_7_9_r47,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#coth.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_2_3_r3, ruleDecl := ``rubi_7_2_3_r3,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, transc1#arccosh.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_3_7_r25, ruleDecl := ``rubi_7_3_7_r25,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#arctanh.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_3_7_r27, ruleDecl := ``rubi_7_3_7_r27,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#arctanh, transc1#coth.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_3_7_r29, ruleDecl := ``rubi_7_3_7_r29,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#arctanh.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_3_7_r31, ruleDecl := ``rubi_7_3_7_r31,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#arctanh, transc1#coth.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_3_7_r43, ruleDecl := ``rubi_7_3_7_r43,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#arctanh, transc1#sec.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

def entries : List CEntry :=
  part1 ++ part2 ++ part3 ++ part4 ++ part5 ++ part6 ++ part7 ++ part8 ++ part9 ++ part10 ++ part11 ++ part12

theorem entries_wellFormed : ∀ e ∈ entries,
    (if e.rule.shape == .antiderivRec || e.rule.shape == .antiderivSubst then e.rule.recOk else e.rule.wellFormed) = true := by
  intro e he
  apply List.all_eq_true.mp _ e he
  decide +kernel

end OSR.IntegrationRecovered
