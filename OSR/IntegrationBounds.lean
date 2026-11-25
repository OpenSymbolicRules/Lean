import OSR.IntegrationRec120
import OSR.IntegrationRec122
import OSR.IntegrationRec193
import OSR.IntegrationRec194
import OSR.IntegrationRec195
import OSR.IntegrationRec196
import OSR.IntegrationRec3
import OSR.IntegrationRecovered

/-! RUBI entries from the default source profile. The original mathematical
conditions are retained. Catalogue membership and proof status are independent. -/

namespace OSR.IntegrationBounds
open Calculus

private def source (legacy locator revision : String) : Provenance :=
  { method := .derived, sources := [
    { name := "OpenSymbolicRules/Integration", locator := legacy,
      revision := some "f44efdaaed1da9f7200fc19564070cc7a1e490b5", license := some "MIT" },
    { name := "Rubi", locator, revision := some revision, license := some "MIT" }] }

private abbrev v (s : String) : Expr := .var s
private abbrev z (n : Int) : Expr := .int n
private abbrev add (a b : Expr) : Expr := .app2 .add a b
private abbrev mul (a b : Expr) : Expr := .app2 .mul a b
private abbrev pow (a b : Expr) : Expr := .pow a b
private abbrev root (a b : Expr) : Expr := .app2 .root a b

/-- RUBI 1.2.2.8, source rule 3 (OSR legacy ID). -/
def rubi_1_2_2_8_r3 : CRule where
  id := "integration.source_1_2_2_8_r3"
  legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p:3"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (add (v "d") (mul (v "e") (v "x"))) (v "q")) (pow (root (add (add (v "a") (mul (v "b")
    (pow (v "x") (z 2)))) (mul (v "c") (pow (v "x") (z 4)))) (z 2)) (z (-1))))
  result := (add (mul (mul (mul (pow (v "e") (z 3)) (pow (add (v "d") (mul (v "e") (v "x"))) (add (v "q") (z
    1)))) (root (add (add (v "a") (mul (v "b") (pow (v "x") (z 2)))) (mul (v "c") (pow (v "x") (z 4)))) (z
    2))) (pow (mul (add (v "q") (z 1)) (add (add (mul (v "c") (pow (v "d") (z 4))) (mul (mul (v "b") (pow (v
    "d") (z 2))) (pow (v "e") (z 2)))) (mul (v "a") (pow (v "e") (z 4))))) (z (-1)))) (mul (mul (z 1) (pow
    (mul (add (v "q") (z 1)) (add (add (mul (v "c") (pow (v "d") (z 4))) (mul (mul (v "b") (pow (v "d") (z
    2))) (pow (v "e") (z 2)))) (mul (v "a") (pow (v "e") (z 4))))) (z (-1)))) (v "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (mul (pow (add (v "d") (mul (v "e") (v "x"))) (add (v "q") (z 1))) (pow
    (root (add (add (v "a") (mul (v "b") (pow (v "x") (z 2)))) (mul (v "c") (pow (v "x") (z 4)))) (z 2)) (z
    (-1)))) (add (add (add (mul (mul (v "d") (add (v "q") (z 1))) (add (mul (v "c") (pow (v "d") (z 2))) (mul
    (v "b") (pow (v "e") (z 2))))) (mul (mul (mul (z (-1)) (v "e")) (add (mul (mul (v "c") (pow (v "d") (z
    2))) (add (v "q") (z 1))) (mul (mul (v "b") (pow (v "e") (z 2))) (add (v "q") (z 2))))) (v "x"))) (mul
    (mul (mul (mul (v "c") (v "d")) (pow (v "e") (z 2))) (add (v "q") (z 1))) (pow (v "x") (z 2)))) (mul (mul
    (mul (mul (z (-1)) (v "c")) (pow (v "e") (z 3))) (add (v "q") (z 3))) (pow (v "x") (z 3))))))]
  independent := ["a", "b", "c", "d", "e", "q"]
  conditions := [(.ne (add (add (mul (v "c") (pow (v "d") (z 4))) (mul (mul (v "b") (pow (v "d") (z 2))) (pow
    (v "e") (z 2)))) (mul (v "a") (pow (v "e") (z 4)))) (z 0)), (Cond.int (v "q")), (.gt (z (-1)) (v "q"))]
  priority := 102296
  description := "RUBI 1.2.2.8, source rule 3 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p:3"
    "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p.m#3" "4.16.1"

/-- RUBI 1.2.2.8, source rule 4 (OSR legacy ID). -/
def rubi_1_2_2_8_r4 : CRule where
  id := "integration.source_1_2_2_8_r4"
  legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p:4"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (add (v "d") (mul (v "e") (v "x"))) (v "q")) (pow (root (add (v "a") (mul (v "c") (pow (v
    "x") (z 4)))) (z 2)) (z (-1))))
  result := (add (mul (mul (mul (pow (v "e") (z 3)) (pow (add (v "d") (mul (v "e") (v "x"))) (add (v "q") (z
    1)))) (root (add (v "a") (mul (v "c") (pow (v "x") (z 4)))) (z 2))) (pow (mul (add (v "q") (z 1)) (add
    (mul (v "c") (pow (v "d") (z 4))) (mul (v "a") (pow (v "e") (z 4))))) (z (-1)))) (mul (mul (v "c") (pow
    (mul (add (v "q") (z 1)) (add (mul (v "c") (pow (v "d") (z 4))) (mul (v "a") (pow (v "e") (z 4))))) (z
    (-1)))) (v "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (mul (pow (add (v "d") (mul (v "e") (v "x"))) (add (v "q") (z 1))) (pow
    (root (add (v "a") (mul (v "c") (pow (v "x") (z 4)))) (z 2)) (z (-1)))) (add (add (add (mul (pow (v "d")
    (z 3)) (add (v "q") (z 1))) (mul (mul (mul (mul (z (-1)) (pow (v "d") (z 2))) (v "e")) (add (v "q") (z
    1))) (v "x"))) (mul (mul (mul (v "d") (pow (v "e") (z 2))) (add (v "q") (z 1))) (pow (v "x") (z 2)))) (mul
    (mul (mul (z (-1)) (pow (v "e") (z 3))) (add (v "q") (z 3))) (pow (v "x") (z 3))))))]
  independent := ["a", "c", "d", "e", "q"]
  conditions := [(.ne (add (mul (v "c") (pow (v "d") (z 4))) (mul (v "a") (pow (v "e") (z 4)))) (z 0)),
    (Cond.int (v "q")), (.gt (z (-1)) (v "q"))]
  priority := 102297
  description := "RUBI 1.2.2.8, source rule 4 (OSR legacy ID)"
  provenance := source "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p:4"
    "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p.m#4" "4.16.1"

/-- RUBI 4.1.5, source rule 41 (OSR legacy ID). -/
def rubi_4_1_5_r41 : CRule where
  id := "integration.source_4_1_5_r41"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:41"
  x := "x"
  shape := .antiderivRec
  body := (mul (mul (pow (.app1 .cos (add (v "c") (mul (v "d") (v "x")))) (v "m")) (pow (.app1 .sin (add (v
    "c") (mul (v "d") (v "x")))) (v "n"))) (pow (add (mul (v "a") (.app1 .cos (add (v "c") (mul (v "d") (v
    "x"))))) (mul (v "b") (.app1 .sin (add (v "c") (mul (v "d") (v "x")))))) (z (-1))))
  result := (add (add (mul (mul (v "b") (pow (add (pow (v "a") (z 2)) (pow (v "b") (z 2))) (z (-1)))) (v
    "osrIntegral1")) (mul (mul (v "a") (pow (add (pow (v "a") (z 2)) (pow (v "b") (z 2))) (z (-1)))) (v
    "osrIntegral2"))) (mul (mul (mul (mul (z (-1)) (v "a")) (v "b")) (pow (add (pow (v "a") (z 2)) (pow (v
    "b") (z 2))) (z (-1)))) (v "osrIntegral3")))
  integrals := [("osrIntegral1", (mul (pow (.app1 .cos (add (v "c") (mul (v "d") (v "x")))) (v "m")) (pow
    (.app1 .sin (add (v "c") (mul (v "d") (v "x")))) (add (v "n") (mul (z (-1)) (z 1)))))), ("osrIntegral2",
    (mul (pow (.app1 .cos (add (v "c") (mul (v "d") (v "x")))) (add (v "m") (mul (z (-1)) (z 1)))) (pow (.app1
    .sin (add (v "c") (mul (v "d") (v "x")))) (v "n")))), ("osrIntegral3", (mul (mul (pow (.app1 .cos (add (v
    "c") (mul (v "d") (v "x")))) (add (v "m") (mul (z (-1)) (z 1)))) (pow (.app1 .sin (add (v "c") (mul (v
    "d") (v "x")))) (add (v "n") (mul (z (-1)) (z 1))))) (pow (add (mul (v "a") (.app1 .cos (add (v "c") (mul
    (v "d") (v "x"))))) (mul (v "b") (.app1 .sin (add (v "c") (mul (v "d") (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (pow (v "b") (z 2))) (z 0)), (Cond.int (v "m")), (.gt (v "m")
    (z 0)), (Cond.int (v "n")), (.gt (v "n") (z 0))]
  priority := 103653
  description := "RUBI 4.1.5, source rule 41 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:41"
    "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#41" "4.16.1"

/-- RUBI 4.1.5, source rule 43 (OSR legacy ID). -/
def rubi_4_1_5_r43 : CRule where
  id := "integration.source_4_1_5_r43"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:43"
  x := "x"
  shape := .antiderivRec
  body := (mul (mul (pow (.app1 .cos (add (v "c") (mul (v "d") (v "x")))) (v "m")) (pow (.app1 .sin (add (v
    "c") (mul (v "d") (v "x")))) (v "n"))) (pow (add (mul (v "a") (.app1 .cos (add (v "c") (mul (v "d") (v
    "x"))))) (mul (v "b") (.app1 .sin (add (v "c") (mul (v "d") (v "x")))))) (v "p")))
  result := (add (add (mul (mul (v "b") (pow (add (pow (v "a") (z 2)) (pow (v "b") (z 2))) (z (-1)))) (v
    "osrIntegral1")) (mul (mul (v "a") (pow (add (pow (v "a") (z 2)) (pow (v "b") (z 2))) (z (-1)))) (v
    "osrIntegral2"))) (mul (mul (mul (mul (z (-1)) (v "a")) (v "b")) (pow (add (pow (v "a") (z 2)) (pow (v
    "b") (z 2))) (z (-1)))) (v "osrIntegral3")))
  integrals := [("osrIntegral1", (mul (mul (pow (.app1 .cos (add (v "c") (mul (v "d") (v "x")))) (v "m")) (pow
    (.app1 .sin (add (v "c") (mul (v "d") (v "x")))) (add (v "n") (mul (z (-1)) (z 1))))) (pow (add (mul (v
    "a") (.app1 .cos (add (v "c") (mul (v "d") (v "x"))))) (mul (v "b") (.app1 .sin (add (v "c") (mul (v "d")
    (v "x")))))) (add (v "p") (z 1))))), ("osrIntegral2", (mul (mul (pow (.app1 .cos (add (v "c") (mul (v "d")
    (v "x")))) (add (v "m") (mul (z (-1)) (z 1)))) (pow (.app1 .sin (add (v "c") (mul (v "d") (v "x")))) (v
    "n"))) (pow (add (mul (v "a") (.app1 .cos (add (v "c") (mul (v "d") (v "x"))))) (mul (v "b") (.app1 .sin
    (add (v "c") (mul (v "d") (v "x")))))) (add (v "p") (z 1))))), ("osrIntegral3", (mul (mul (pow (.app1 .cos
    (add (v "c") (mul (v "d") (v "x")))) (add (v "m") (mul (z (-1)) (z 1)))) (pow (.app1 .sin (add (v "c")
    (mul (v "d") (v "x")))) (add (v "n") (mul (z (-1)) (z 1))))) (pow (add (mul (v "a") (.app1 .cos (add (v
    "c") (mul (v "d") (v "x"))))) (mul (v "b") (.app1 .sin (add (v "c") (mul (v "d") (v "x")))))) (v "p"))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (pow (v "b") (z 2))) (z 0)), (Cond.int (v "m")), (.gt (v "m")
    (z 0)), (Cond.int (v "n")), (.gt (v "n") (z 0)), (Cond.int (v "p")), (.gt (z 0) (v "p"))]
  priority := 103655
  description := "RUBI 4.1.5, source rule 43 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:43"
    "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#43" "4.16.1"

/-- RUBI 4.1.6, source rule 46 (OSR legacy ID). -/
def rubi_4_1_6_r46 : CRule where
  id := "integration.source_4_1_6_r46"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:46"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (.app1 .cos (add (v "d") (mul (v "e") (v "x")))) (v "n")) (pow (add (add (v "a") (mul (v
    "b") (.app1 .sec (add (v "d") (mul (v "e") (v "x")))))) (mul (v "c") (.app1 .tan (add (v "d") (mul (v "e")
    (v "x")))))) (v "n")))
  result := (v "osrIntegral1")
  integrals := [("osrIntegral1", (pow (add (add (v "b") (mul (v "a") (.app1 .cos (add (v "d") (mul (v "e") (v
    "x")))))) (mul (v "c") (.app1 .sin (add (v "d") (mul (v "e") (v "x")))))) (v "n")))]
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [(Cond.int (v "n"))]
  priority := 103701
  description := "RUBI 4.1.6, source rule 46 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:46"
    "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#46" "4.16.1"

/-- RUBI 4.1.6, source rule 47 (OSR legacy ID). -/
def rubi_4_1_6_r47 : CRule where
  id := "integration.source_4_1_6_r47"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:47"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (.app1 .sin (add (v "d") (mul (v "e") (v "x")))) (v "n")) (pow (add (add (v "a") (mul (v
    "b") (.app1 .csc (add (v "d") (mul (v "e") (v "x")))))) (mul (v "c") (.app1 .cot (add (v "d") (mul (v "e")
    (v "x")))))) (v "n")))
  result := (v "osrIntegral1")
  integrals := [("osrIntegral1", (pow (add (add (v "b") (mul (v "a") (.app1 .sin (add (v "d") (mul (v "e") (v
    "x")))))) (mul (v "c") (.app1 .cos (add (v "d") (mul (v "e") (v "x")))))) (v "n")))]
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [(Cond.int (v "n"))]
  priority := 103702
  description := "RUBI 4.1.6, source rule 47 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:47"
    "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#47" "4.16.1"

/-- RUBI 4.1.12, source rule 55 (OSR legacy ID). -/
def rubi_4_1_12_r55 : CRule where
  id := "integration.source_4_1_12_r55"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:55"
  x := "x"
  shape := .antiderivSubst
  body := (mul (pow (v "x") (v "m")) (pow (add (v "a") (mul (v "b") (.app1 .sin (add (v "c") (mul (v "d") (pow
    (v "x") (v "n"))))))) (v "p")))
  result := (mul (z (-1)) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (.app1 .sin (add (v "c") (mul (v "d")
    (pow (v "x") (mul (z (-1)) (v "n")))))))) (v "p")) (pow (pow (v "x") (add (v "m") (z 2))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (z 1) (pow (v "x") (z (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [(Cond.int (v "p")), (.gt (v "p") (z 0)), (Cond.int (v "n")), (.gt (z 0) (v "n")), (Cond.int
    (v "m")), (.eq (v "n") (z (-2)))]
  priority := 103888
  description := "RUBI 4.1.12, source rule 55 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:55"
    "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#55" "4.16.1"

/-- RUBI 4.1.12, source rule 56 (OSR legacy ID). -/
def rubi_4_1_12_r56 : CRule where
  id := "integration.source_4_1_12_r56"
  legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:56"
  x := "x"
  shape := .antiderivSubst
  body := (mul (pow (v "x") (v "m")) (pow (add (v "a") (mul (v "b") (.app1 .cos (add (v "c") (mul (v "d") (pow
    (v "x") (v "n"))))))) (v "p")))
  result := (mul (z (-1)) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (.app1 .cos (add (v "c") (mul (v "d")
    (pow (v "x") (mul (z (-1)) (v "n")))))))) (v "p")) (pow (pow (v "x") (add (v "m") (z 2))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (z 1) (pow (v "x") (z (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [(Cond.int (v "p")), (.gt (v "p") (z 0)), (Cond.int (v "n")), (.gt (z 0) (v "n")), (Cond.int
    (v "m")), (.eq (v "n") (z (-2)))]
  priority := 103889
  description := "RUBI 4.1.12, source rule 56 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:56"
    "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#56" "4.16.1"

/-- RUBI 4.3.1.2, source rule 26 (OSR legacy ID). -/
def rubi_4_3_1_2_r26 : CRule where
  id := "integration.source_4_3_1_2_r26"
  legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n:26"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (mul (v "d") (.app1 .sec (add (v "e") (mul (v "f") (v "x"))))) (v "m")) (pow (add (v "a")
    (mul (v "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x")))))) (z (-1))))
  result := (add (mul (mul (z 1) (pow (add (pow (v "a") (z 2)) (pow (v "b") (z 2))) (z (-1)))) (v
    "osrIntegral1")) (mul (mul (pow (v "b") (z 2)) (pow (mul (pow (v "d") (z 2)) (add (pow (v "a") (z 2)) (pow
    (v "b") (z 2)))) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (pow (mul (v "d") (.app1 .sec (add (v "e") (mul (v "f") (v "x"))))) (v
    "m")) (add (v "a") (mul (mul (z (-1)) (v "b")) (.app1 .tan (add (v "e") (mul (v "f") (v "x")))))))),
    ("osrIntegral2", (mul (pow (mul (v "d") (.app1 .sec (add (v "e") (mul (v "f") (v "x"))))) (add (v "m") (z
    2))) (pow (add (v "a") (mul (v "b") (.app1 .tan (add (v "e") (mul (v "f") (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "d", "e", "f", "m"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (pow (v "b") (z 2))) (z 0)), (Cond.int (v "m")), (.gt (z 0) (v
    "m"))]
  priority := 103986
  description := "RUBI 4.3.1.2, source rule 26 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n:26"
    "4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n.m#26" "4.16.1"

/-- RUBI 4.5.1.4, source rule 20 (OSR legacy ID). -/
def rubi_4_5_1_4_r20 : CRule where
  id := "integration.source_4_5_1_4_r20"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.1.4 (d tan)^n (a+b sec)^m:20"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (.app1 .cot (add (v "c") (mul (v "d") (v "x")))) (v "m")) (pow (add (v "a") (mul (v "b")
    (.app1 .csc (add (v "c") (mul (v "d") (v "x")))))) (v "n")))
  result := (v "osrIntegral1")
  integrals := [("osrIntegral1", (mul (mul (pow (.app1 .cos (add (v "c") (mul (v "d") (v "x")))) (v "m")) (pow
    (add (v "b") (mul (v "a") (.app1 .sin (add (v "c") (mul (v "d") (v "x")))))) (v "n"))) (pow (pow (.app1
    .sin (add (v "c") (mul (v "d") (v "x")))) (add (v "m") (v "n"))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (Cond.int (v "n")),
    (Cond.int (v "m")), (.or (Cond.int (mul (v "m") (pow (z 2) (z (-1))))) (.ge (z 1) (v "m")))]
  priority := 104367
  description := "RUBI 4.5.1.4, source rule 20 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.1.4 (d tan)^n (a+b sec)^m:20"
    "4 Trig functions/4.5 Secant/4.5.1.4 (d tan)^n (a+b sec)^m.m#20" "4.16.1"

/-- RUBI 4.5.2.2, source rule 7 (OSR legacy ID). -/
def rubi_4_5_2_2_r7 : CRule where
  id := "integration.source_4_5_2_2_r7"
  legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:7"
  x := "x"
  shape := .antiderivRec
  body := (mul (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (add (v "c") (mul (v "d") (.app1
    .csc (add (v "e") (mul (v "f") (v "x")))))) (v "n"))) (pow (root (add (v "a") (mul (v "b") (.app1 .csc
    (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1))))
  result := (add (mul (mul (mul (mul (z (-2)) (v "d")) (.app1 .cot (add (v "e") (mul (v "f") (v "x"))))) (pow
    (add (v "c") (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (add (v "n") (mul (z (-1)) (z
    1))))) (pow (mul (mul (v "f") (add (mul (z 2) (v "n")) (mul (z (-1)) (z 1)))) (root (add (v "a") (mul (v
    "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2))) (z (-1)))) (mul (mul (mul (mul (z 2) (v
    "c")) (add (mul (z 2) (v "n")) (mul (z (-1)) (z 1)))) (pow (add (mul (z 2) (v "n")) (mul (z (-1)) (z 1)))
    (z (-1)))) (v "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (mul (.app1 .csc (add (v "e") (mul (v "f") (v "x")))) (pow (add (v "c")
    (mul (v "d") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (add (v "n") (mul (z (-1)) (z 1))))) (pow
    (root (add (v "a") (mul (v "b") (.app1 .csc (add (v "e") (mul (v "f") (v "x")))))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n"]
  conditions := [(.eq (add (mul (v "b") (v "c")) (mul (v "a") (v "d"))) (z 0)), (.eq (add (pow (v "a") (z 2))
    (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (Cond.int (v "n")), (.gt (v "n") (z 0))]
  priority := 104425
  description := "RUBI 4.5.2.2, source rule 7 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n:7"
    "4 Trig functions/4.5 Secant/4.5.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n.m#7" "4.16.1"

/-- RUBI 4.7.9, source rule 69 (OSR legacy ID). -/
def rubi_4_7_9_r69 : CRule where
  id := "integration.source_4_7_9_r69"
  legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:69"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (v "x") (v "m")) (pow (add (v "a") (mul (v "b") (pow (.app1 .sin (add (v "c") (mul (v "d")
    (v "x")))) (z 2)))) (v "n")))
  result := (mul (mul (z 1) (pow (pow (z 2) (v "n")) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (v "x") (v "m")) (pow (add (add (mul (z 2) (v "a")) (v "b")) (mul
    (mul (z (-1)) (v "b")) (.app1 .cos (add (mul (z 2) (v "c")) (mul (mul (z 2) (v "d")) (v "x")))))) (v
    "n"))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [(.ne (add (v "a") (v "b")) (z 0)), (Cond.int (v "m")), (.gt (v "m") (z 0)), (Cond.int (v
    "n")), (.gt (z 0) (v "n")), (.or (.eq (v "n") (z (-1))) (.eq (v "m") (z 1))), (.or (.eq (v "n") (z (-1)))
    (.eq (v "n") (z (-2))))]
  priority := 105045
  description := "RUBI 4.7.9, source rule 69 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:69"
    "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#69" "4.16.1"

/-- RUBI 4.7.9, source rule 70 (OSR legacy ID). -/
def rubi_4_7_9_r70 : CRule where
  id := "integration.source_4_7_9_r70"
  legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:70"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (v "x") (v "m")) (pow (add (v "a") (mul (v "b") (pow (.app1 .cos (add (v "c") (mul (v "d")
    (v "x")))) (z 2)))) (v "n")))
  result := (mul (mul (z 1) (pow (pow (z 2) (v "n")) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (v "x") (v "m")) (pow (add (add (mul (z 2) (v "a")) (v "b")) (mul
    (v "b") (.app1 .cos (add (mul (z 2) (v "c")) (mul (mul (z 2) (v "d")) (v "x")))))) (v "n"))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [(.ne (add (v "a") (v "b")) (z 0)), (Cond.int (v "m")), (.gt (v "m") (z 0)), (Cond.int (v
    "n")), (.gt (z 0) (v "n")), (.or (.eq (v "n") (z (-1))) (.eq (v "m") (z 1))), (.or (.eq (v "n") (z (-1)))
    (.eq (v "n") (z (-2))))]
  priority := 105046
  description := "RUBI 4.7.9, source rule 70 (OSR legacy ID)"
  provenance := source "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:70"
    "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#70" "4.16.1"

/-- RUBI 5.1.2, source rule 2 (OSR legacy ID). -/
def rubi_5_1_2_r2 : CRule where
  id := "integration.source_5_1_2_r2"
  legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:2"
  x := "x"
  shape := .antiderivSubst
  body := (mul (pow (add (v "a") (mul (v "b") (.app1 .arccos (mul (v "c") (v "x"))))) (v "n")) (pow (v "x") (z
    (-1))))
  result := (mul (z (-1)) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (v "x"))) (v "n")) (.app1 .tan (v
    "x"))))]
  substs := [("osrIntegral1", (.app1 .arccos (mul (v "c") (v "x"))))]
  independent := ["a", "b", "c", "n"]
  conditions := [(Cond.int (v "n")), (.gt (v "n") (z 0))]
  priority := 105086
  description := "RUBI 5.1.2, source rule 2 (OSR legacy ID)"
  provenance := source "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:2"
    "5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n.m#2" "4.16.1"

/-- RUBI 5.1.4, source rule 6 (OSR legacy ID). -/
def rubi_5_1_4_r6 : CRule where
  id := "integration.source_5_1_4_r6"
  legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:6"
  x := "x"
  shape := .antiderivSubst
  body := (mul (pow (add (v "a") (mul (v "b") (.app1 .arccos (mul (v "c") (v "x"))))) (v "n")) (pow (mul (v
    "x") (add (v "d") (mul (v "e") (pow (v "x") (z 2))))) (z (-1))))
  result := (mul (mul (z (-1)) (pow (v "d") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (v "x"))) (v "n")) (pow (mul (.app1 .cos
    (v "x")) (.app1 .sin (v "x"))) (z (-1)))))]
  substs := [("osrIntegral1", (.app1 .arccos (mul (v "c") (v "x"))))]
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [(.eq (add (mul (pow (v "c") (z 2)) (v "d")) (v "e")) (z 0)), (Cond.int (v "n")), (.gt (v "n")
    (z 0))]
  priority := 105134
  description := "RUBI 5.1.4, source rule 6 (OSR legacy ID)"
  provenance := source "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:6"
    "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#6" "4.16.1"

/-- RUBI 5.3.4, source rule 21 (OSR legacy ID). -/
def rubi_5_3_4_r21 : CRule where
  id := "integration.source_5_3_4_r21"
  legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:21"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (add (v "a") (mul (v "b") (.app1 .arctan (mul (v "c") (v "x"))))) (v "p")) (pow (root (add
    (v "d") (mul (v "e") (pow (v "x") (z 2)))) (z 2)) (z (-1))))
  result := (mul (mul (root (add (z 1) (mul (pow (v "c") (z 2)) (pow (v "x") (z 2)))) (z 2)) (pow (root (add
    (v "d") (mul (v "e") (pow (v "x") (z 2)))) (z 2)) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (.app1 .arctan (mul (v "c") (v "x")))))
    (v "p")) (pow (root (add (z 1) (mul (pow (v "c") (z 2)) (pow (v "x") (z 2)))) (z 2)) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [(.eq (v "e") (mul (pow (v "c") (z 2)) (v "d"))), (Cond.int (v "p")), (.gt (v "p") (z 0)),
    (.ge (z 0) (v "d"))]
  priority := 105374
  description := "RUBI 5.3.4, source rule 21 (OSR legacy ID)"
  provenance := source "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:21"
    "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#21" "4.16.1"

/-- RUBI 5.3.4, source rule 87 (OSR legacy ID). -/
def rubi_5_3_4_r87 : CRule where
  id := "integration.source_5_3_4_r87"
  legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:87"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (add (v "a") (mul (v "b") (.app1 .arctan (mul (v "c") (v "x"))))) (v "p")) (pow (mul (v
    "x") (root (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (z 2))) (z (-1))))
  result := (mul (mul (root (add (z 1) (mul (pow (v "c") (z 2)) (pow (v "x") (z 2)))) (z 2)) (pow (root (add
    (v "d") (mul (v "e") (pow (v "x") (z 2)))) (z 2)) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (.app1 .arctan (mul (v "c") (v "x")))))
    (v "p")) (pow (mul (v "x") (root (add (z 1) (mul (pow (v "c") (z 2)) (pow (v "x") (z 2)))) (z 2))) (z
    (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [(.eq (v "e") (mul (pow (v "c") (z 2)) (v "d"))), (Cond.int (v "p")), (.gt (v "p") (z 0)),
    (.ge (z 0) (v "d"))]
  priority := 105442
  description := "RUBI 5.3.4, source rule 87 (OSR legacy ID)"
  provenance := source "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:87"
    "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#87" "4.16.1"

/-- RUBI 5.3.7, source rule 59 (OSR legacy ID). -/
def rubi_5_3_7_r59 : CRule where
  id := "integration.source_5_3_7_r59"
  legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:59"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (add (v "e") (mul (v "f") (v "x"))) (v "m")) (.app1 .arctan (add (v "c") (mul (v "d")
    (.app1 .tanh (add (v "a") (mul (v "b") (v "x"))))))))
  result := (add (mul (mul (pow (add (v "e") (mul (v "f") (v "x"))) (add (v "m") (z 1))) (.app1 .arctan (add
    (v "c") (mul (v "d") (.app1 .tanh (add (v "a") (mul (v "b") (v "x")))))))) (pow (mul (v "f") (add (v "m")
    (z 1))) (z (-1)))) (mul (mul (mul (z (-1)) (v "b")) (pow (mul (v "f") (add (v "m") (z 1))) (z (-1)))) (v
    "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (pow (add (v "e") (mul (v "f") (v "x"))) (add (v "m") (z 1))) (pow (add
    (add (v "c") (mul (z (-1)) (v "d"))) (mul (v "c") (.app1 .exp (add (mul (z 2) (v "a")) (mul (mul (z 2) (v
    "b")) (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [(Cond.int (v "m")), (.gt (v "m") (z 0)), (.eq (pow (add (v "c") (mul (z (-1)) (v "d"))) (z
    2)) (z (-1)))]
  priority := 105667
  description := "RUBI 5.3.7, source rule 59 (OSR legacy ID)"
  provenance := source "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:59"
    "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#59" "4.16.1"

/-- RUBI 5.3.7, source rule 61 (OSR legacy ID). -/
def rubi_5_3_7_r61 : CRule where
  id := "integration.source_5_3_7_r61"
  legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:61"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (add (v "e") (mul (v "f") (v "x"))) (v "m")) (.app1 .arctan (add (v "c") (mul (v "d")
    (.app1 .coth (add (v "a") (mul (v "b") (v "x"))))))))
  result := (add (mul (mul (pow (add (v "e") (mul (v "f") (v "x"))) (add (v "m") (z 1))) (.app1 .arctan (add
    (v "c") (mul (v "d") (.app1 .coth (add (v "a") (mul (v "b") (v "x")))))))) (pow (mul (v "f") (add (v "m")
    (z 1))) (z (-1)))) (mul (mul (mul (z (-1)) (v "b")) (pow (mul (v "f") (add (v "m") (z 1))) (z (-1)))) (v
    "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (pow (add (v "e") (mul (v "f") (v "x"))) (add (v "m") (z 1))) (pow (add
    (add (v "c") (mul (z (-1)) (v "d"))) (mul (mul (z (-1)) (v "c")) (.app1 .exp (add (mul (z 2) (v "a")) (mul
    (mul (z 2) (v "b")) (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [(Cond.int (v "m")), (.gt (v "m") (z 0)), (.eq (pow (add (v "c") (mul (z (-1)) (v "d"))) (z
    2)) (z (-1)))]
  priority := 105669
  description := "RUBI 5.3.7, source rule 61 (OSR legacy ID)"
  provenance := source "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:61"
    "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#61" "4.16.1"

/-- RUBI 6.1.12, source rule 5 (OSR legacy ID). -/
def rubi_6_1_12_r5 : CRule where
  id := "integration.source_6_1_12_r5"
  legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:5"
  x := "x"
  shape := .antiderivSubst
  body := (pow (add (v "a") (mul (v "b") (.app1 .sinh (add (v "c") (mul (v "d") (pow (v "x") (v "n"))))))) (v
    "p"))
  result := (mul (z (-1)) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (.app1 .sinh (add (v "c") (mul (v "d")
    (pow (v "x") (mul (z (-1)) (v "n")))))))) (v "p")) (pow (pow (v "x") (z 2)) (z (-1)))))]
  substs := [("osrIntegral1", (mul (z 1) (pow (v "x") (z (-1)))))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [(Cond.int (v "n")), (.gt (z 0) (v "n")), (Cond.int (v "p"))]
  priority := 105774
  description := "RUBI 6.1.12, source rule 5 (OSR legacy ID)"
  provenance := source "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:5"
    "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#5" "4.16.1"

/-- RUBI 6.1.12, source rule 6 (OSR legacy ID). -/
def rubi_6_1_12_r6 : CRule where
  id := "integration.source_6_1_12_r6"
  legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:6"
  x := "x"
  shape := .antiderivSubst
  body := (pow (add (v "a") (mul (v "b") (.app1 .cosh (add (v "c") (mul (v "d") (pow (v "x") (v "n"))))))) (v
    "p"))
  result := (mul (z (-1)) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (.app1 .cosh (add (v "c") (mul (v "d")
    (pow (v "x") (mul (z (-1)) (v "n")))))))) (v "p")) (pow (pow (v "x") (z 2)) (z (-1)))))]
  substs := [("osrIntegral1", (mul (z 1) (pow (v "x") (z (-1)))))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [(Cond.int (v "n")), (.gt (z 0) (v "n")), (Cond.int (v "p"))]
  priority := 105775
  description := "RUBI 6.1.12, source rule 6 (OSR legacy ID)"
  provenance := source "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:6"
    "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#6" "4.16.1"

/-- RUBI 6.1.12, source rule 45 (OSR legacy ID). -/
def rubi_6_1_12_r45 : CRule where
  id := "integration.source_6_1_12_r45"
  legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:45"
  x := "x"
  shape := .antiderivSubst
  body := (mul (pow (v "x") (v "m")) (pow (add (v "a") (mul (v "b") (.app1 .sinh (add (v "c") (mul (v "d")
    (pow (v "x") (v "n"))))))) (v "p")))
  result := (mul (z (-1)) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (.app1 .sinh (add (v "c") (mul (v "d")
    (pow (v "x") (mul (z (-1)) (v "n")))))))) (v "p")) (pow (pow (v "x") (add (v "m") (z 2))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (z 1) (pow (v "x") (z (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [(Cond.int (v "p")), (Cond.int (v "n")), (.gt (z 0) (v "n")), (Cond.int (v "m"))]
  priority := 105816
  description := "RUBI 6.1.12, source rule 45 (OSR legacy ID)"
  provenance := source "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:45"
    "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#45" "4.16.1"

/-- RUBI 6.1.12, source rule 46 (OSR legacy ID). -/
def rubi_6_1_12_r46 : CRule where
  id := "integration.source_6_1_12_r46"
  legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:46"
  x := "x"
  shape := .antiderivSubst
  body := (mul (pow (v "x") (v "m")) (pow (add (v "a") (mul (v "b") (.app1 .cosh (add (v "c") (mul (v "d")
    (pow (v "x") (v "n"))))))) (v "p")))
  result := (mul (z (-1)) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (.app1 .cosh (add (v "c") (mul (v "d")
    (pow (v "x") (mul (z (-1)) (v "n")))))))) (v "p")) (pow (pow (v "x") (add (v "m") (z 2))) (z (-1)))))]
  substs := [("osrIntegral1", (mul (z 1) (pow (v "x") (z (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [(Cond.int (v "p")), (Cond.int (v "n")), (.gt (z 0) (v "n")), (Cond.int (v "m"))]
  priority := 105817
  description := "RUBI 6.1.12, source rule 46 (OSR legacy ID)"
  provenance := source "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:46"
    "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#46" "4.16.1"

/-- RUBI 6.7.9, source rule 3 (OSR legacy ID). -/
def rubi_6_7_9_r3 : CRule where
  id := "integration.source_6_7_9_r3"
  legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:3"
  x := "x"
  shape := .antiderivRec
  body := (mul (mul (pow (add (v "e") (mul (v "f") (v "x"))) (v "m")) (.app1 .cosh (add (v "c") (mul (v "d")
    (v "x"))))) (pow (add (v "a") (mul (v "b") (.app1 .sinh (add (v "c") (mul (v "d") (v "x")))))) (z (-1))))
  result := (add (mul (mul (z (-1)) (pow (add (v "e") (mul (v "f") (v "x"))) (add (v "m") (z 1)))) (pow (mul
    (mul (v "b") (v "f")) (add (v "m") (z 1))) (z (-1)))) (mul (z 2) (v "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (mul (pow (add (v "e") (mul (v "f") (v "x"))) (v "m")) (.app1 .exp (add
    (v "c") (mul (v "d") (v "x"))))) (pow (add (v "a") (mul (v "b") (.app1 .exp (add (v "c") (mul (v "d") (v
    "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [(Cond.int (v "m")), (.gt (v "m") (z 0)), (.eq (add (pow (v "a") (z 2)) (pow (v "b") (z 2)))
    (z 0))]
  priority := 106036
  description := "RUBI 6.7.9, source rule 3 (OSR legacy ID)"
  provenance := source "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:3"
    "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#3" "4.16.1"

/-- RUBI 6.7.9, source rule 71 (OSR legacy ID). -/
def rubi_6_7_9_r71 : CRule where
  id := "integration.source_6_7_9_r71"
  legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:71"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (v "x") (v "m")) (pow (add (v "a") (mul (v "b") (pow (.app1 .sinh (add (v "c") (mul (v
    "d") (v "x")))) (z 2)))) (v "n")))
  result := (mul (mul (z 1) (pow (pow (z 2) (v "n")) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (v "x") (v "m")) (pow (add (add (mul (z 2) (v "a")) (mul (z (-1))
    (v "b"))) (mul (v "b") (.app1 .cosh (add (mul (z 2) (v "c")) (mul (mul (z 2) (v "d")) (v "x")))))) (v
    "n"))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [(.ne (add (v "a") (mul (z (-1)) (v "b"))) (z 0)), (Cond.int (v "m")), (.gt (v "m") (z 0)),
    (Cond.int (v "n")), (.gt (z 0) (v "n")), (.or (.eq (v "n") (z (-1))) (.eq (v "m") (z 1))), (.or (.eq (v
    "n") (z (-1))) (.eq (v "n") (z (-2))))]
  priority := 106106
  description := "RUBI 6.7.9, source rule 71 (OSR legacy ID)"
  provenance := source "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:71"
    "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#71" "4.16.1"

/-- RUBI 6.7.9, source rule 72 (OSR legacy ID). -/
def rubi_6_7_9_r72 : CRule where
  id := "integration.source_6_7_9_r72"
  legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:72"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (v "x") (v "m")) (pow (add (v "a") (mul (v "b") (pow (.app1 .cosh (add (v "c") (mul (v
    "d") (v "x")))) (z 2)))) (v "n")))
  result := (mul (mul (z 1) (pow (pow (z 2) (v "n")) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (v "x") (v "m")) (pow (add (add (mul (z 2) (v "a")) (v "b")) (mul
    (v "b") (.app1 .cosh (add (mul (z 2) (v "c")) (mul (mul (z 2) (v "d")) (v "x")))))) (v "n"))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [(.ne (add (v "a") (mul (z (-1)) (v "b"))) (z 0)), (Cond.int (v "m")), (.gt (v "m") (z 0)),
    (Cond.int (v "n")), (.gt (z 0) (v "n")), (.or (.eq (v "n") (z (-1))) (.eq (v "m") (z 1))), (.or (.eq (v
    "n") (z (-1))) (.eq (v "n") (z (-2))))]
  priority := 106107
  description := "RUBI 6.7.9, source rule 72 (OSR legacy ID)"
  provenance := source "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:72"
    "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#72" "4.16.1"

/-- RUBI 6.7.9, source rule 74 (OSR legacy ID). -/
def rubi_6_7_9_r74 : CRule where
  id := "integration.source_6_7_9_r74"
  legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:74"
  x := "x"
  shape := .antiderivRec
  body := (mul (mul (pow (add (v "f") (mul (v "g") (v "x"))) (v "m")) (pow (.app1 .sech (add (v "d") (mul (v
    "e") (v "x")))) (z 2))) (pow (add (v "b") (mul (v "c") (pow (.app1 .tanh (add (v "d") (mul (v "e") (v
    "x")))) (z 2)))) (z (-1))))
  result := (mul (z 2) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "f") (mul (v "g") (v "x"))) (v "m")) (pow (add (add (v "b")
    (mul (z (-1)) (v "c"))) (mul (add (v "b") (v "c")) (.app1 .cosh (add (mul (z 2) (v "d")) (mul (mul (z 2)
    (v "e")) (v "x")))))) (z (-1)))))]
  independent := ["b", "c", "d", "e", "f", "g", "m"]
  conditions := [(Cond.int (v "m")), (.gt (v "m") (z 0))]
  priority := 106109
  description := "RUBI 6.7.9, source rule 74 (OSR legacy ID)"
  provenance := source "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:74"
    "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#74" "4.16.1"

/-- RUBI 6.7.9, source rule 77 (OSR legacy ID). -/
def rubi_6_7_9_r77 : CRule where
  id := "integration.source_6_7_9_r77"
  legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:77"
  x := "x"
  shape := .antiderivRec
  body := (mul (mul (pow (add (v "f") (mul (v "g") (v "x"))) (v "m")) (pow (.app1 .csch (add (v "d") (mul (v
    "e") (v "x")))) (z 2))) (pow (add (add (v "c") (mul (v "b") (pow (.app1 .coth (add (v "d") (mul (v "e") (v
    "x")))) (z 2)))) (mul (v "a") (pow (.app1 .csch (add (v "d") (mul (v "e") (v "x")))) (z 2)))) (z (-1))))
  result := (mul (z 2) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "f") (mul (v "g") (v "x"))) (v "m")) (pow (add (add (add
    (mul (z 2) (v "a")) (v "b")) (mul (z (-1)) (v "c"))) (mul (add (v "b") (v "c")) (.app1 .cosh (add (mul (z
    2) (v "d")) (mul (mul (z 2) (v "e")) (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m"]
  conditions := [(Cond.int (v "m")), (.gt (v "m") (z 0)), (.ne (add (v "a") (v "b")) (z 0)), (.ne (add (v "a")
    (v "c")) (z 0))]
  priority := 106112
  description := "RUBI 6.7.9, source rule 77 (OSR legacy ID)"
  provenance := source "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:77"
    "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#77" "4.16.1"

/-- RUBI 7.2.3, source rule 14 (OSR legacy ID). -/
def rubi_7_2_3_r14 : CRule where
  id := "integration.source_7_2_3_r14"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n:14"
  x := "x"
  shape := .antiderivSubst
  body := (mul (pow (add (v "a") (mul (v "b") (.app1 .arccosh (mul (v "c") (v "x"))))) (v "n")) (pow (add (v
    "d") (mul (v "e") (pow (v "x") (z 2)))) (z (-1))))
  result := (mul (mul (z (-1)) (pow (mul (v "c") (v "d")) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (v "x"))) (v "n")) (.app1 .csch (v
    "x"))))]
  substs := [("osrIntegral1", (.app1 .arccosh (mul (v "c") (v "x"))))]
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [(.eq (add (mul (pow (v "c") (z 2)) (v "d")) (v "e")) (z 0)), (Cond.int (v "n")), (.gt (v "n")
    (z 0))]
  priority := 106261
  description := "RUBI 7.2.3, source rule 14 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n:14"
    "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n.m#14" "4.16.1"

/-- RUBI 7.2.4, source rule 2 (OSR legacy ID). -/
def rubi_7_2_4_r2 : CRule where
  id := "integration.source_7_2_4_r2"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:2"
  x := "x"
  shape := .antiderivSubst
  body := (mul (mul (v "x") (pow (add (v "a") (mul (v "b") (.app1 .arccosh (mul (v "c") (v "x"))))) (v "n")))
    (pow (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (z (-1))))
  result := (mul (mul (z 1) (pow (v "e") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (v "x"))) (v "n")) (.app1 .coth (v
    "x"))))]
  substs := [("osrIntegral1", (.app1 .arccosh (mul (v "c") (v "x"))))]
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [(.eq (add (mul (pow (v "c") (z 2)) (v "d")) (v "e")) (z 0)), (Cond.int (v "n")), (.gt (v "n")
    (z 0))]
  priority := 106271
  description := "RUBI 7.2.4, source rule 2 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:2"
    "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m#2" "4.16.1"

/-- RUBI 7.2.4, source rule 5 (OSR legacy ID). -/
def rubi_7_2_4_r5 : CRule where
  id := "integration.source_7_2_4_r5"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:5"
  x := "x"
  shape := .antiderivSubst
  body := (mul (pow (add (v "a") (mul (v "b") (.app1 .arccosh (mul (v "c") (v "x"))))) (v "n")) (pow (mul (v
    "x") (add (v "d") (mul (v "e") (pow (v "x") (z 2))))) (z (-1))))
  result := (mul (mul (z (-1)) (pow (v "d") (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (v "x"))) (v "n")) (pow (mul (.app1 .cosh
    (v "x")) (.app1 .sinh (v "x"))) (z (-1)))))]
  substs := [("osrIntegral1", (.app1 .arccosh (mul (v "c") (v "x"))))]
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [(.eq (add (mul (pow (v "c") (z 2)) (v "d")) (v "e")) (z 0)), (Cond.int (v "n")), (.gt (v "n")
    (z 0))]
  priority := 106274
  description := "RUBI 7.2.4, source rule 5 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:5"
    "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m#5" "4.16.1"

/-- RUBI 7.2.4, source rule 32 (OSR legacy ID). -/
def rubi_7_2_4_r32 : CRule where
  id := "integration.source_7_2_4_r32"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:32"
  x := "x"
  shape := .antiderivSubst
  body := (mul (mul (pow (v "x") (v "m")) (pow (add (v "a") (mul (v "b") (.app1 .arccosh (mul (v "c") (v
    "x"))))) (v "n"))) (pow (root (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (z 2)) (z (-1))))
  result := (mul (mul (mul (z 1) (pow (pow (v "c") (add (v "m") (z 1))) (z (-1)))) (mul (mul (root (add (z 1)
    (mul (v "c") (v "x"))) (z 2)) (root (add (z (-1)) (mul (v "c") (v "x"))) (z 2))) (pow (root (add (v "d")
    (mul (v "e") (pow (v "x") (z 2)))) (z 2)) (z (-1))))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (v "x"))) (v "n")) (pow (.app1 .cosh (v
    "x")) (v "m"))))]
  substs := [("osrIntegral1", (.app1 .arccosh (mul (v "c") (v "x"))))]
  independent := ["a", "b", "c", "d", "e", "m", "n"]
  conditions := [(.eq (add (mul (pow (v "c") (z 2)) (v "d")) (v "e")) (z 0)), (Cond.int (v "n")), (.gt (v "n")
    (z 0)), (Cond.int (v "m"))]
  priority := 106304
  description := "RUBI 7.2.4, source rule 32 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:32"
    "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m#32" "4.16.1"

/-- RUBI 7.2.4, source rule 33 (OSR legacy ID). -/
def rubi_7_2_4_r33 : CRule where
  id := "integration.source_7_2_4_r33"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:33"
  x := "x"
  shape := .antiderivSubst
  body := (mul (mul (pow (v "x") (v "m")) (pow (add (v "a") (mul (v "b") (.app1 .arccosh (mul (v "c") (v
    "x"))))) (v "n"))) (pow (mul (root (add (v "d1") (mul (v "e1") (v "x"))) (z 2)) (root (add (v "d2") (mul
    (v "e2") (v "x"))) (z 2))) (z (-1))))
  result := (mul (mul (mul (mul (z 1) (pow (pow (v "c") (add (v "m") (z 1))) (z (-1)))) (mul (root (add (z 1)
    (mul (v "c") (v "x"))) (z 2)) (pow (root (add (v "d1") (mul (v "e1") (v "x"))) (z 2)) (z (-1))))) (mul
    (root (add (z (-1)) (mul (v "c") (v "x"))) (z 2)) (pow (root (add (v "d2") (mul (v "e2") (v "x"))) (z 2))
    (z (-1))))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (v "x"))) (v "n")) (pow (.app1 .cosh (v
    "x")) (v "m"))))]
  substs := [("osrIntegral1", (.app1 .arccosh (mul (v "c") (v "x"))))]
  independent := ["a", "b", "c", "d1", "d2", "e1", "e2", "m", "n"]
  conditions := [(.eq (v "e1") (mul (v "c") (v "d1"))), (.eq (v "e2") (mul (mul (z (-1)) (v "c")) (v "d2"))),
    (Cond.int (v "n")), (.gt (v "n") (z 0)), (Cond.int (v "m"))]
  priority := 106305
  description := "RUBI 7.2.4, source rule 33 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:33"
    "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m#33" "4.16.1"

/-- RUBI 7.2.5, source rule 1 (OSR legacy ID). -/
def rubi_7_2_5_r1 : CRule where
  id := "integration.source_7_2_5_r1"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.5 u (a+b arccosh(c x))^n:1"
  x := "x"
  shape := .antiderivSubst
  body := (mul (pow (add (v "a") (mul (v "b") (.app1 .arccosh (mul (v "c") (v "x"))))) (v "n")) (pow (add (v
    "d") (mul (v "e") (v "x"))) (z (-1))))
  result := (v "osrIntegral1")
  integrals := [("osrIntegral1", (mul (mul (pow (add (v "a") (mul (v "b") (v "x"))) (v "n")) (.app1 .sinh (v
    "x"))) (pow (add (mul (v "c") (v "d")) (mul (v "e") (.app1 .cosh (v "x")))) (z (-1)))))]
  substs := [("osrIntegral1", (.app1 .arccosh (mul (v "c") (v "x"))))]
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [(Cond.int (v "n")), (.gt (v "n") (z 0))]
  priority := 106320
  description := "RUBI 7.2.5, source rule 1 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.5 u (a+b arccosh(c x))^n:1"
    "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.5 u (a+b arccosh(c x))^n.m#1" "4.16.1"

/-- RUBI 7.3.4, source rule 21 (OSR legacy ID). -/
def rubi_7_3_4_r21 : CRule where
  id := "integration.source_7_3_4_r21"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:21"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (add (v "a") (mul (v "b") (.app1 .arctanh (mul (v "c") (v "x"))))) (v "p")) (pow (root
    (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (z 2)) (z (-1))))
  result := (mul (mul (root (add (z 1) (mul (mul (z (-1)) (pow (v "c") (z 2))) (pow (v "x") (z 2)))) (z 2))
    (pow (root (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (z 2)) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (.app1 .arctanh (mul (v "c") (v "x")))))
    (v "p")) (pow (root (add (z 1) (mul (mul (z (-1)) (pow (v "c") (z 2))) (pow (v "x") (z 2)))) (z 2)) (z
    (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [(.eq (add (mul (pow (v "c") (z 2)) (v "d")) (v "e")) (z 0)), (Cond.int (v "p")), (.gt (v "p")
    (z 0)), (.ge (z 0) (v "d"))]
  priority := 106459
  description := "RUBI 7.3.4, source rule 21 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:21"
    "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#21" "4.16.1"

/-- RUBI 7.3.4, source rule 87 (OSR legacy ID). -/
def rubi_7_3_4_r87 : CRule where
  id := "integration.source_7_3_4_r87"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:87"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (add (v "a") (mul (v "b") (.app1 .arctanh (mul (v "c") (v "x"))))) (v "p")) (pow (mul (v
    "x") (root (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (z 2))) (z (-1))))
  result := (mul (mul (root (add (z 1) (mul (mul (z (-1)) (pow (v "c") (z 2))) (pow (v "x") (z 2)))) (z 2))
    (pow (root (add (v "d") (mul (v "e") (pow (v "x") (z 2)))) (z 2)) (z (-1)))) (v "osrIntegral1"))
  integrals := [("osrIntegral1", (mul (pow (add (v "a") (mul (v "b") (.app1 .arctanh (mul (v "c") (v "x")))))
    (v "p")) (pow (mul (v "x") (root (add (z 1) (mul (mul (z (-1)) (pow (v "c") (z 2))) (pow (v "x") (z 2))))
    (z 2))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [(.eq (add (mul (pow (v "c") (z 2)) (v "d")) (v "e")) (z 0)), (Cond.int (v "p")), (.gt (v "p")
    (z 0)), (.ge (z 0) (v "d"))]
  priority := 106527
  description := "RUBI 7.3.4, source rule 87 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:87"
    "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#87" "4.16.1"

/-- RUBI 7.3.4, source rule 128 (OSR legacy ID). -/
def rubi_7_3_4_r128 : CRule where
  id := "integration.source_7_3_4_r128"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:128"
  x := "x"
  shape := .antiderivRec
  body := (mul (.app1 .arctanh (mul (v "a") (v "x"))) (pow (add (v "c") (mul (v "d") (pow (v "x") (v "n"))))
    (z (-1))))
  result := (add (mul (mul (z 1) (pow (z 2) (z (-1)))) (v "osrIntegral1")) (mul (mul (mul (z (-1)) (z 1)) (pow
    (z 2) (z (-1)))) (v "osrIntegral2")))
  integrals := [("osrIntegral1", (mul (.app1 .ln (add (z 1) (mul (v "a") (v "x")))) (pow (add (v "c") (mul (v
    "d") (pow (v "x") (v "n")))) (z (-1))))), ("osrIntegral2", (mul (.app1 .ln (add (z 1) (mul (mul (z (-1))
    (v "a")) (v "x")))) (pow (add (v "c") (mul (v "d") (pow (v "x") (v "n")))) (z (-1)))))]
  independent := ["a", "c", "d", "n"]
  conditions := [(Cond.int (v "n")), (.or (.ne (v "n") (z 2)) (.ne (add (mul (pow (v "a") (z 2)) (v "c")) (v
    "d")) (z 0)))]
  priority := 106572
  description := "RUBI 7.3.4, source rule 128 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:128"
    "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#128" "4.16.1"

/-- RUBI 7.3.7, source rule 35 (OSR legacy ID). -/
def rubi_7_3_7_r35 : CRule where
  id := "integration.source_7_3_7_r35"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:35"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (add (v "e") (mul (v "f") (v "x"))) (v "m")) (.app1 .arctanh (add (v "c") (mul (v "d")
    (.app1 .coth (add (v "a") (mul (v "b") (v "x"))))))))
  result := (add (mul (mul (pow (add (v "e") (mul (v "f") (v "x"))) (add (v "m") (z 1))) (.app1 .arctanh (add
    (v "c") (mul (v "d") (.app1 .coth (add (v "a") (mul (v "b") (v "x")))))))) (pow (mul (v "f") (add (v "m")
    (z 1))) (z (-1)))) (mul (mul (v "b") (pow (mul (v "f") (add (v "m") (z 1))) (z (-1)))) (v
    "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (pow (add (v "e") (mul (v "f") (v "x"))) (add (v "m") (z 1))) (pow (add
    (add (v "c") (mul (z (-1)) (v "d"))) (mul (mul (z (-1)) (v "c")) (.app1 .exp (add (mul (z 2) (v "a")) (mul
    (mul (z 2) (v "b")) (v "x")))))) (z (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [(Cond.int (v "m")), (.gt (v "m") (z 0)), (.eq (pow (add (v "c") (mul (z (-1)) (v "d"))) (z
    2)) (z 1))]
  priority := 106734
  description := "RUBI 7.3.7, source rule 35 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:35"
    "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#35" "4.16.1"

/-- RUBI 7.3.7, source rule 47 (OSR legacy ID). -/
def rubi_7_3_7_r47 : CRule where
  id := "integration.source_7_3_7_r47"
  legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:47"
  x := "x"
  shape := .antiderivRec
  body := (mul (pow (add (v "e") (mul (v "f") (v "x"))) (v "m")) (.app1 .arctanh (.app1 .cot (add (v "a") (mul
    (v "b") (v "x"))))))
  result := (add (mul (mul (pow (add (v "e") (mul (v "f") (v "x"))) (add (v "m") (z 1))) (.app1 .arctanh
    (.app1 .cot (add (v "a") (mul (v "b") (v "x")))))) (pow (mul (v "f") (add (v "m") (z 1))) (z (-1)))) (mul
    (mul (mul (z (-1)) (v "b")) (pow (mul (v "f") (add (v "m") (z 1))) (z (-1)))) (v "osrIntegral1")))
  integrals := [("osrIntegral1", (mul (pow (add (v "e") (mul (v "f") (v "x"))) (add (v "m") (z 1))) (.app1
    .sec (add (mul (z 2) (v "a")) (mul (mul (z 2) (v "b")) (v "x"))))))]
  independent := ["a", "b", "e", "f", "m"]
  conditions := [(Cond.int (v "m")), (.gt (v "m") (z 0))]
  priority := 106746
  description := "RUBI 7.3.7, source rule 47 (OSR legacy ID)"
  provenance := source "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:47"
    "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#47" "4.16.1"

/-- Source rules whose original interval excludes every integer exponent in the pattern. -/
def outside : List (String × String) := [
  ("rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:12", "The full source interval 0 < p < 1 excludes every integer exponent for the pattern; general noninteger powers require a different interpretation."),
  ("rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:38", "The full source interval 0 < p < 1 excludes every integer exponent for the pattern; general noninteger powers require a different interpretation."),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:39", "The full source interval 0 < m < 1 excludes every integer exponent for the pattern; general noninteger powers require a different interpretation."),
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:40", "The full source interval 0 < m < 1 excludes every integer exponent for the pattern; general noninteger powers require a different interpretation."),
  ("rubi:4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m:24", "The full source interval 0 < m < 1 excludes every integer exponent for the pattern; general noninteger powers require a different interpretation."),
  ("rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):21", "The full source interval 0 < n < 1 excludes every integer exponent for the pattern; general noninteger powers require a different interpretation."),
  ("rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):23", "The full source interval 0 < m < 1 excludes every integer exponent for the pattern; general noninteger powers require a different interpretation."),
  ("rubi:4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec):32", "The full source interval 0 < n < 1 excludes every integer exponent for the pattern; general noninteger powers require a different interpretation."),
  ("rubi:4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec):36", "The full source interval 0 < m < 1 excludes every integer exponent for the pattern; general noninteger powers require a different interpretation."),
  ("rubi:4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec):37", "The full source interval 0 < m < 1 excludes every integer exponent for the pattern; general noninteger powers require a different interpretation.")
]

/-- Earlier catalogue entries replaced or withdrawn after checking the full interval. -/
def replaced : List String := [
  "integration.rubi_1_1_1_3_r12",
  "integration.rubi_1_1_1_4_r38",
  "integration.rubi_4_1_12_r83",
  "integration.rubi_4_1_12_r84",
  "integration.rubi_1_2_1_2_r39",
  "integration.rubi_1_2_1_2_r40",
  "integration.rubi_1_1_1_3_r12_nondegenerate",
  "integration.rubi_1_1_1_4_r38_nondegenerate",
  "integration.rubi_1_2_1_2_r39_nondegenerate",
  "integration.rubi_1_2_1_2_r40_nondegenerate",
  "integration.rubi_1_1_4_1_r11",
  "integration.rubi_6_1_12_r25",
  "integration.rubi_6_1_12_r26",
  "integration.rubi_6_1_12_r35",
  "integration.rubi_6_1_12_r36",
  "integration.rubi_6_1_12_r37",
  "integration.rubi_6_1_12_r38",
  "integration.rubi_6_1_12_r43",
  "integration.rubi_6_1_12_r44",
  "integration.rubi_6_1_12_r67",
  "integration.rubi_6_1_12_r68",
  "integration.rubi_4_3_3_1_r23",
  "integration.rubi_4_5_3_1_r32",
  "integration.rubi_4_5_3_1_r36",
  "integration.rubi_4_5_3_1_r37",
  "integration.rubi_4_5_1_2_r80",
  "integration.rubi_4_1_2_1_r88",
  "integration.rubi_4_1_1_2_r24",
  "integration.rubi_4_1_2_2_r3",
  "integration.rubi_4_5_1_2_r81",
  "integration.rubi_4_3_3_1_r21",
  "integration.rubi_7_3_6_r56",
  "integration.rubi_7_3_3_exp_r40",
  "integration.rubi_7_3_3_exp_r78",
  "integration.rubi_7_3_3_exp_r56",
  "integration.rubi_7_3_6_r40",
  "integration.rubi_7_3_6_r78",
  "integration.rubi_4_1_1_2_r24_nondegenerate",
  "integration.rubi_4_1_2_2_r3_nondegenerate",
  "integration.rubi_4_3_3_1_r21_nondegenerate",
  "integration.rubi_4_3_3_1_r23_nondegenerate",
  "integration.rubi_4_5_1_2_r80_nondegenerate",
  "integration.rubi_4_5_1_2_r81_nondegenerate",
  "integration.rubi_4_5_3_1_r32_nondegenerate",
  "integration.rubi_4_5_3_1_r36_nondegenerate",
  "integration.rubi_4_5_3_1_r37_nondegenerate",
  "integration.rubi_6_1_12_r37_nondegenerate",
  "integration.rubi_6_1_12_r38_nondegenerate",
  "integration.source_4_5_2_1_r39"
]

def rubi_4_1_12_r83 : CRule := { OSR.IntegrationRec3.rubi4112r83 with
  conditions := [(.gt (v "n") (z 0)), (.gt (add (v "m") (z 1)) (v "n")), (.ne (v "p") (z (-1)))] }

def rubi_4_1_12_r84 : CRule := { OSR.IntegrationRec3.rubi4112r84 with
  conditions := [(.gt (v "n") (z 0)), (.gt (add (v "m") (z 1)) (v "n")), (.ne (v "p") (z (-1)))] }

def rubi_1_1_4_1_r11 : CRule := { OSR.IntegrationRec120.rubi1141r11 with
  conditions := [(.gt (v "j") (mul (z 2) (add (v "n") (mul (z (-1)) (z 1))))), (.gt (v "n") (v "j"))] }

def rubi_6_1_12_r25 : CRule := { OSR.IntegrationRec122.rubi6112r25 with
  conditions := [(Cond.int (v "n")), (.gt (v "n") (z 0)), (.gt (v "n") (z 0)), (.gt (add (v "m") (z 1)) (v
    "n"))] }

def rubi_6_1_12_r26 : CRule := { OSR.IntegrationRec122.rubi6112r26 with
  conditions := [(Cond.int (v "n")), (.gt (v "n") (z 0)), (.gt (v "n") (z 0)), (.gt (add (v "m") (z 1)) (v
    "n"))] }

def rubi_6_1_12_r35 : CRule := { OSR.IntegrationRec122.rubi6112r35 with
  conditions := [(Cond.int (v "m")), (Cond.int (v "n")), (.gt (v "p") (z 1)), (.gt (mul (z 2) (v "n")) (z 0)),
    (.gt (add (v "m") (z 1)) (mul (z 2) (v "n")))] }

def rubi_6_1_12_r36 : CRule := { OSR.IntegrationRec122.rubi6112r36 with
  conditions := [(Cond.int (v "m")), (Cond.int (v "n")), (.gt (v "p") (z 1)), (.gt (mul (z 2) (v "n")) (z 0)),
    (.gt (add (v "m") (z 1)) (mul (z 2) (v "n")))] }

def rubi_6_1_12_r37 : CRule := { OSR.IntegrationRec122.rubi6112r37 with
  conditions := [(Cond.int (v "m")), (Cond.int (v "n")), (.gt (v "p") (z 1)), (.gt (mul (z 2) (v "n")) (z 0)),
    (.gt (add (z 1) (mul (z (-1)) (v "m"))) (mul (z 2) (v "n"))), (.ne (add (add (v "m") (v "n")) (z 1)) (z
    0))] }

def rubi_6_1_12_r38 : CRule := { OSR.IntegrationRec122.rubi6112r38 with
  conditions := [(Cond.int (v "m")), (Cond.int (v "n")), (.gt (v "p") (z 1)), (.gt (mul (z 2) (v "n")) (z 0)),
    (.gt (add (z 1) (mul (z (-1)) (v "m"))) (mul (z 2) (v "n"))), (.ne (add (add (v "m") (v "n")) (z 1)) (z
    0))] }

def rubi_6_1_12_r43 : CRule := { OSR.IntegrationRec122.rubi6112r43 with
  conditions := [(Cond.int (v "m")), (Cond.int (v "n")), (.gt (z (-1)) (v "p")), (.ne (v "p") (z (-2))), (.gt
    (mul (z 2) (v "n")) (z 0)), (.gt (add (v "m") (z 1)) (mul (z 2) (v "n")))] }

def rubi_6_1_12_r44 : CRule := { OSR.IntegrationRec122.rubi6112r44 with
  conditions := [(Cond.int (v "m")), (Cond.int (v "n")), (.gt (z (-1)) (v "p")), (.ne (v "p") (z (-2))), (.gt
    (mul (z 2) (v "n")) (z 0)), (.gt (add (v "m") (z 1)) (mul (z 2) (v "n")))] }

def rubi_6_1_12_r67 : CRule := { OSR.IntegrationRec122.rubi6112r67 with
  conditions := [(.gt (v "n") (z 0)), (.gt (add (v "m") (z 1)) (v "n")), (.ne (v "p") (z (-1)))] }

def rubi_6_1_12_r68 : CRule := { OSR.IntegrationRec122.rubi6112r68 with
  conditions := [(.gt (v "n") (z 0)), (.gt (add (v "m") (z 1)) (v "n")), (.ne (v "p") (z (-1)))] }

def rubi_4_5_1_2_r80 : CRule := { OSR.IntegrationRec193.rubi4512r80 with
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.gt (v "m") (z
    0)), (.gt (z 2) (v "m")), (.gt (v "n") (z 0)), (.gt (z 3) (v "n")), (.ne (add (add (v "m") (v "n")) (mul
    (z (-1)) (z 1))) (z 0)), (.or (Cond.int (v "m")) (Cond.int (mul (z 2) (v "m")))), (.or (Cond.int (v "m"))
    (Cond.int (mul (z 2) (v "n"))))] }

def rubi_4_1_2_1_r88 : CRule := { OSR.IntegrationRec193.rubi4121r88 with
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (.ne (add (pow
    (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.ne (add (pow (v "c") (z 2)) (mul (z (-1))
    (pow (v "d") (z 2)))) (z 0)), (.gt (v "m") (z 0)), (.gt (z 2) (v "m")), (.gt (v "n") (z (-1))), (.gt (z 2)
    (v "n")), (.ne (add (v "m") (v "n")) (z 0)), (.or (Cond.int (v "m")) (Cond.int (mul (z 2) (v "m")))), (.or
    (Cond.int (v "m")) (Cond.int (mul (z 2) (v "n"))))] }

def rubi_4_1_2_2_r3 : CRule := { OSR.IntegrationRec193.rubi4122r3 with
  conditions := [(Cond.int (mul (add (v "p") (mul (z (-1)) (z 1))) (pow (z 2) (z (-1))))), (.eq (add (pow (v
    "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (Cond.int (v "n")), (.or (.or (.gt (v "n") (z 0))
    (.ge (mul (z (-1)) (v "n")) (v "p"))) (.gt (v "n") (z 0))), (.or (.or (.gt (v "n") (z 0)) (.ge (mul (z
    (-1)) (v "n")) (v "p"))) (.ge (mul (z (-1)) (v "p")) (v "n"))), (.or (.or (.gt (v "n") (z 0)) (.gt (add
    (mul (z 2) (v "p")) (mul (z (-1)) (z 3))) (mul (z (-1)) (v "n")))) (.gt (v "n") (z 0))), (.or (.or (.gt (v
    "n") (z 0)) (.gt (add (mul (z 2) (v "p")) (mul (z (-1)) (z 3))) (mul (z (-1)) (v "n")))) (.ge (mul (z
    (-1)) (v "p")) (v "n"))), (.or (.or (.gt (mul (add (v "p") (z 1)) (pow (z 2) (z (-1)))) (v "n")) (.ge (mul
    (z (-1)) (v "n")) (v "p"))) (.gt (v "n") (z 0))), (.or (.or (.gt (mul (add (v "p") (z 1)) (pow (z 2) (z
    (-1)))) (v "n")) (.ge (mul (z (-1)) (v "n")) (v "p"))) (.ge (mul (z (-1)) (v "p")) (v "n"))), (.or (.or
    (.gt (mul (add (v "p") (z 1)) (pow (z 2) (z (-1)))) (v "n")) (.gt (add (mul (z 2) (v "p")) (mul (z (-1))
    (z 3))) (mul (z (-1)) (v "n")))) (.gt (v "n") (z 0))), (.or (.or (.gt (mul (add (v "p") (z 1)) (pow (z 2)
    (z (-1)))) (v "n")) (.gt (add (mul (z 2) (v "p")) (mul (z (-1)) (z 3))) (mul (z (-1)) (v "n")))) (.ge (mul
    (z (-1)) (v "p")) (v "n")))] }

def rubi_4_5_1_2_r81 : CRule := { OSR.IntegrationRec193.rubi4512r81 with
  conditions := [(.ne (add (pow (v "a") (z 2)) (mul (z (-1)) (pow (v "b") (z 2)))) (z 0)), (.gt (v "m") (z
    (-1))), (.gt (z 2) (v "m")), (.gt (v "n") (z 1)), (.gt (z 3) (v "n")), (.ne (add (add (v "m") (v "n"))
    (mul (z (-1)) (z 1))) (z 0)), (.or (Cond.int (v "n")) (Cond.int (mul (z 2) (v "m")))), (.or (Cond.int (v
    "n")) (Cond.int (mul (z 2) (v "n"))))] }

def rubi_7_3_6_r56 : CRule := { OSR.IntegrationRec194.rubi736r56 with
  conditions := [(.eq (add (v "c") (mul (v "a") (v "d"))) (z 0)), (Cond.int (mul (add (v "n") (mul (z (-1)) (z
    1))) (pow (z 2) (z (-1))))), (Cond.int (v "m")), (.or (.or (.or (Cond.int (v "p")) (.eq (v "p") (mul (v
    "n") (pow (z 2) (z (-1)))))) (.eq (v "p") (add (mul (v "n") (pow (z 2) (z (-1)))) (z 1)))) (.gt (v "m") (z
    (-5)))), (.or (.or (.or (Cond.int (v "p")) (.eq (v "p") (mul (v "n") (pow (z 2) (z (-1)))))) (.eq (v "p")
    (add (mul (v "n") (pow (z 2) (z (-1)))) (z 1)))) (.gt (z (-1)) (v "m"))), (Cond.int (mul (z 2) (v "p")))] }

def rubi_7_3_3_exp_r40 : CRule := { OSR.IntegrationRec195.rubi733er40 with
  conditions := [(Cond.int (v "m")), (.gt (z 0) (v "m")), (.gt (v "n") (z (-1))), (.gt (z 1) (v "n"))] }

def rubi_7_3_3_exp_r78 : CRule := { OSR.IntegrationRec195.rubi733er78 with
  conditions := [(Cond.int (v "m")), (.gt (z 0) (v "m")), (.gt (v "n") (z (-1))), (.gt (z 1) (v "n"))] }

def rubi_7_3_3_exp_r56 : CRule := { OSR.IntegrationRec196.rubi733er56 with
  conditions := [(.eq (add (v "c") (mul (v "a") (v "d"))) (z 0)), (Cond.int (mul (add (v "n") (mul (z (-1)) (z
    1))) (pow (z 2) (z (-1))))), (Cond.int (v "m")), (.or (.or (.or (Cond.int (v "p")) (.eq (v "p") (mul (v
    "n") (pow (z 2) (z (-1)))))) (.eq (v "p") (add (mul (v "n") (pow (z 2) (z (-1)))) (z 1)))) (.gt (v "m") (z
    (-5)))), (.or (.or (.or (Cond.int (v "p")) (.eq (v "p") (mul (v "n") (pow (z 2) (z (-1)))))) (.eq (v "p")
    (add (mul (v "n") (pow (z 2) (z (-1)))) (z 1)))) (.gt (z (-1)) (v "m"))), (Cond.int (mul (z 2) (v "p")))] }

def rubi_7_3_6_r40 : CRule := { OSR.IntegrationRec196.rubi736r40 with
  conditions := [(Cond.int (v "m")), (.gt (z 0) (v "m")), (.gt (v "n") (z (-1))), (.gt (z 1) (v "n"))] }

def rubi_7_3_6_r78 : CRule := { OSR.IntegrationRec196.rubi736r78 with
  conditions := [(Cond.int (v "m")), (.gt (z 0) (v "m")), (.gt (v "n") (z (-1))), (.gt (z 1) (v "n"))] }

def rubi_4_5_2_1_r39 : CRule := { OSR.IntegrationRecovered.rubi_4_5_2_1_r39 with
  conditions := [(.ne (add (mul (v "b") (v "c")) (mul (mul (z (-1)) (v "a")) (v "d"))) (z 0)), (Cond.int (v
    "m")), (Cond.int (v "n")), (.ge (add (v "m") (v "n")) (z (-2))), (.ge (z 0) (add (v "m") (v "n")))] }

section
open Filter Topology

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
section
variable {α : Type} [Field α] [CharZero α]
private theorem iv0 : intValue? (0 : α) = some 0 := by simpa using intValue?_intCast (α := α) 0
private theorem iv1 : intValue? (1 : α) = some 1 := by simpa using intValue?_intCast (α := α) 1
private theorem iv2 : intValue? (2 : α) = some 2 := by simpa using intValue?_intCast (α := α) 2
private theorem iv3 : intValue? (3 : α) = some 3 := by simpa using intValue?_intCast (α := α) 3
private theorem iv4 : intValue? (4 : α) = some 4 := by simpa using intValue?_intCast (α := α) 4
private theorem iv5 : intValue? (5 : α) = some 5 := by simpa using intValue?_intCast (α := α) 5
private theorem iv6 : intValue? (6 : α) = some 6 := by simpa using intValue?_intCast (α := α) 6
private theorem iv7 : intValue? (7 : α) = some 7 := by simpa using intValue?_intCast (α := α) 7
private theorem iv8 : intValue? (8 : α) = some 8 := by simpa using intValue?_intCast (α := α) 8
private theorem iv9 : intValue? (9 : α) = some 9 := by simpa using intValue?_intCast (α := α) 9
private theorem iv10 : intValue? (10 : α) = some 10 := by simpa using intValue?_intCast (α := α) 10
private theorem iv11 : intValue? (11 : α) = some 11 := by simpa using intValue?_intCast (α := α) 11
private theorem iv12 : intValue? (12 : α) = some 12 := by simpa using intValue?_intCast (α := α) 12
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

attribute [local simp] iv0 iv1 iv2 iv3 iv4 iv5 iv6 iv7 iv8 iv9 iv10 iv11 iv12 ivm1 ivm2 ivm3 ivm4 ivm5 ivm6 ivm7 ivm8 ivm9 ivm10 ivm11 ivm12 ivnat ivneg

theorem rubi_4_1_2_1_r88_counterexample_real : ¬ rubi_4_1_2_1_r88.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi_4_1_2_1_r88.conditions rubi_4_1_2_1_r88.body rubi_4_1_2_1_r88.result rubi_4_1_2_1_r88.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then (4 : ℝ) else if s = "d" then (-1 : ℝ) else if s = "m" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
    obtain ⟨h1, h2⟩ := hw
    try simp [rubi_4_1_2_1_r88, OSR.IntegrationRec193.rubi4121r88, Defined, eval, Interp.real]
    repeat' constructor
    all_goals first | positivity | linarith | nlinarith [h1, h2] | exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])).ne' | norm_num) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi_4_1_2_1_r88, OSR.IntegrationRec193.rubi4121r88, Cond.Holds, Defined, eval, Interp.real] <;> norm_num <;> positivity
  · simp [rubi_4_1_2_1_r88, OSR.IntegrationRec193.rubi4121r88, Defined, eval, Interp.real] <;> norm_num <;> positivity

theorem rubi_4_5_1_2_r81_counterexample_real : ¬ rubi_4_5_1_2_r81.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi_4_5_1_2_r81.conditions rubi_4_5_1_2_r81.body rubi_4_5_1_2_r81.result rubi_4_5_1_2_r81.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "f" then (-1 : ℝ) else if s = "n" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
    obtain ⟨h1, h2⟩ := hw
    try simp [rubi_4_5_1_2_r81, OSR.IntegrationRec193.rubi4512r81, Defined, eval, Interp.real]
    repeat' constructor
    all_goals first | positivity | linarith | nlinarith [h1, h2] | exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])).ne' | norm_num)
    (fun h w => w * (((rubi_4_5_1_2_r81.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "f" then (-1 : ℝ) else if s = "n" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi_4_5_1_2_r81, OSR.IntegrationRec193.rubi4512r81, Cond.Holds, Defined, eval, Interp.real] <;> norm_num <;> positivity
  · simp only [rubi_4_5_1_2_r81, OSR.IntegrationRec193.rubi4512r81, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi_4_5_1_2_r81, OSR.IntegrationRec193.rubi4512r81, Defined, eval, Interp.real, recEnv] at h

theorem rubi_6_1_12_r25_counterexample_real : ¬ rubi_6_1_12_r25.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi_6_1_12_r25.conditions rubi_6_1_12_r25.body rubi_6_1_12_r25.result rubi_6_1_12_r25.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi_6_1_12_r25, OSR.IntegrationRec122.rubi6112r25, Cond.Holds, Defined, eval, Interp.real] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi_6_1_12_r25, OSR.IntegrationRec122.rubi6112r25, Defined, eval, Interp.real] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi_6_1_12_r25.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi_6_1_12_r25, OSR.IntegrationRec122.rubi6112r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi_6_1_12_r25, OSR.IntegrationRec122.rubi6112r25, Defined, eval, Interp.real, recEnv] at h <;> norm_num at h

theorem rubi_6_1_12_r26_counterexample_real : ¬ rubi_6_1_12_r26.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi_6_1_12_r26.conditions rubi_6_1_12_r26.body rubi_6_1_12_r26.result rubi_6_1_12_r26.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi_6_1_12_r26, OSR.IntegrationRec122.rubi6112r26, Cond.Holds, Defined, eval, Interp.real] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi_6_1_12_r26, OSR.IntegrationRec122.rubi6112r26, Defined, eval, Interp.real] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi_6_1_12_r26.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi_6_1_12_r26, OSR.IntegrationRec122.rubi6112r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi_6_1_12_r26, OSR.IntegrationRec122.rubi6112r26, Defined, eval, Interp.real, recEnv] at h <;> norm_num at h

theorem rubi_7_3_3_exp_r40_counterexample_real : ¬ rubi_7_3_3_exp_r40.Holds .real := by
  show ¬ AntiderivSubstHolds Interp.real "x" rubi_7_3_3_exp_r40.conditions rubi_7_3_3_exp_r40.body rubi_7_3_3_exp_r40.result rubi_7_3_3_exp_r40.integrals rubi_7_3_3_exp_r40.substs
  refine not_antiderivSubstHolds_integrand (fun s => if s = "m" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
    obtain ⟨h1, h2⟩ := hw
    try simp [rubi_7_3_3_exp_r40, OSR.IntegrationRec195.rubi733er40, Defined, eval, Interp.real]
    repeat' constructor
    all_goals first | positivity | linarith | nlinarith [h1, h2] | exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])).ne' | norm_num) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi_7_3_3_exp_r40, OSR.IntegrationRec195.rubi733er40, Cond.Holds, Defined, eval, Interp.real] <;> norm_num <;> positivity
  · simp [rubi_7_3_3_exp_r40, OSR.IntegrationRec195.rubi733er40, Defined, eval, Interp.real, substAt, List.lookup] <;> norm_num <;> positivity

theorem rubi_7_3_3_exp_r56_counterexample_real : ¬ rubi_7_3_3_exp_r56.Holds .real := by
  show ¬ AntiderivSubstHolds Interp.real "x" rubi_7_3_3_exp_r56.conditions rubi_7_3_3_exp_r56.body rubi_7_3_3_exp_r56.result rubi_7_3_3_exp_r56.integrals rubi_7_3_3_exp_r56.substs
  refine not_antiderivSubstHolds_integrand (fun s => if s = "a" then (4 : ℝ) else if s = "n" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
    obtain ⟨h1, h2⟩ := hw
    have hwpos : 0 < w := by linarith
    have hinv := inv_pos.mpr hwpos
    have hinv_lt : w⁻¹ < 2 := by
      rw [inv_eq_one_div, div_lt_iff₀ hwpos]
      linarith
    try simp [rubi_7_3_3_exp_r56, OSR.IntegrationRec196.rubi733er56, Defined, eval, Interp.real]
    repeat' constructor
    all_goals first | positivity | linarith | nlinarith [h1, h2] | exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])).ne' | norm_num) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi_7_3_3_exp_r56, OSR.IntegrationRec196.rubi733er56, Cond.Holds, Defined, eval, Interp.real] <;> norm_num <;> positivity
  · simp [rubi_7_3_3_exp_r56, OSR.IntegrationRec196.rubi733er56, Defined, eval, Interp.real, substAt, List.lookup] <;> norm_num <;> positivity

theorem rubi_7_3_3_exp_r78_counterexample_real : ¬ rubi_7_3_3_exp_r78.Holds .real := by
  show ¬ AntiderivSubstHolds Interp.real "x" rubi_7_3_3_exp_r78.conditions rubi_7_3_3_exp_r78.body rubi_7_3_3_exp_r78.result rubi_7_3_3_exp_r78.integrals rubi_7_3_3_exp_r78.substs
  refine not_antiderivSubstHolds_integrand (fun s => if s = "b" then (-3 : ℝ) else if s = "c" then (-2 : ℝ) else if s = "m" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
    obtain ⟨h1, h2⟩ := hw
    have hwpos : 0 < w := by linarith
    have hinv := inv_pos.mpr hwpos
    have hinv_lt : w⁻¹ < 2 := by
      rw [inv_eq_one_div, div_lt_iff₀ hwpos]
      linarith
    try simp [rubi_7_3_3_exp_r78, OSR.IntegrationRec195.rubi733er78, Defined, eval, Interp.real]
    repeat' constructor
    all_goals first | positivity | linarith | nlinarith [h1, h2] | exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])).ne' | norm_num) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi_7_3_3_exp_r78, OSR.IntegrationRec195.rubi733er78, Cond.Holds, Defined, eval, Interp.real] <;> norm_num <;> positivity
  · simp [rubi_7_3_3_exp_r78, OSR.IntegrationRec195.rubi733er78, Defined, eval, Interp.real, substAt, List.lookup] <;> norm_num <;> positivity

theorem rubi_7_3_6_r40_counterexample_real : ¬ rubi_7_3_6_r40.Holds .real := by
  show ¬ AntiderivSubstHolds Interp.real "x" rubi_7_3_6_r40.conditions rubi_7_3_6_r40.body rubi_7_3_6_r40.result rubi_7_3_6_r40.integrals rubi_7_3_6_r40.substs
  refine not_antiderivSubstHolds_integrand (fun s => if s = "m" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
    obtain ⟨h1, h2⟩ := hw
    try simp [rubi_7_3_6_r40, OSR.IntegrationRec196.rubi736r40, Defined, eval, Interp.real]
    repeat' constructor
    all_goals first | positivity | linarith | nlinarith [h1, h2] | exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])).ne' | norm_num) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi_7_3_6_r40, OSR.IntegrationRec196.rubi736r40, Cond.Holds, Defined, eval, Interp.real] <;> norm_num <;> positivity
  · simp [rubi_7_3_6_r40, OSR.IntegrationRec196.rubi736r40, Defined, eval, Interp.real, substAt, List.lookup] <;> norm_num <;> positivity

theorem rubi_7_3_6_r56_counterexample_real : ¬ rubi_7_3_6_r56.Holds .real := by
  show ¬ AntiderivSubstHolds Interp.real "x" rubi_7_3_6_r56.conditions rubi_7_3_6_r56.body rubi_7_3_6_r56.result rubi_7_3_6_r56.integrals rubi_7_3_6_r56.substs
  refine not_antiderivSubstHolds_integrand (fun s => if s = "a" then (4 : ℝ) else if s = "n" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
    obtain ⟨h1, h2⟩ := hw
    have hwpos : 0 < w := by linarith
    have hinv := inv_pos.mpr hwpos
    have hinv_lt : w⁻¹ < 2 := by
      rw [inv_eq_one_div, div_lt_iff₀ hwpos]
      linarith
    try simp [rubi_7_3_6_r56, OSR.IntegrationRec194.rubi736r56, Defined, eval, Interp.real]
    repeat' constructor
    all_goals first | positivity | linarith | nlinarith [h1, h2] | exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])).ne' | norm_num) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi_7_3_6_r56, OSR.IntegrationRec194.rubi736r56, Cond.Holds, Defined, eval, Interp.real] <;> norm_num <;> positivity
  · simp [rubi_7_3_6_r56, OSR.IntegrationRec194.rubi736r56, Defined, eval, Interp.real, substAt, List.lookup] <;> norm_num <;> positivity

theorem rubi_7_3_6_r78_counterexample_real : ¬ rubi_7_3_6_r78.Holds .real := by
  show ¬ AntiderivSubstHolds Interp.real "x" rubi_7_3_6_r78.conditions rubi_7_3_6_r78.body rubi_7_3_6_r78.result rubi_7_3_6_r78.integrals rubi_7_3_6_r78.substs
  refine not_antiderivSubstHolds_integrand (fun s => if s = "b" then (-3 : ℝ) else if s = "c" then (-2 : ℝ) else if s = "m" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
    obtain ⟨h1, h2⟩ := hw
    have hwpos : 0 < w := by linarith
    have hinv := inv_pos.mpr hwpos
    have hinv_lt : w⁻¹ < 2 := by
      rw [inv_eq_one_div, div_lt_iff₀ hwpos]
      linarith
    try simp [rubi_7_3_6_r78, OSR.IntegrationRec196.rubi736r78, Defined, eval, Interp.real]
    repeat' constructor
    all_goals first | positivity | linarith | nlinarith [h1, h2] | exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])).ne' | norm_num) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi_7_3_6_r78, OSR.IntegrationRec196.rubi736r78, Cond.Holds, Defined, eval, Interp.real] <;> norm_num <;> positivity
  · simp [rubi_7_3_6_r78, OSR.IntegrationRec196.rubi736r78, Defined, eval, Interp.real, substAt, List.lookup] <;> norm_num <;> positivity
end

private def part1 : List CEntry := [
  { rule := rubi_1_2_2_8_r3, ruleDecl := ``rubi_1_2_2_8_r3,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: q must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_1_2_2_8_r4, ruleDecl := ``rubi_1_2_2_8_r4,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: q must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_5_r41, ruleDecl := ``rubi_4_1_5_r41,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_5_r43, ruleDecl := ``rubi_4_1_5_r43,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n, p must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_6_r46, ruleDecl := ``rubi_4_1_6_r46,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#sec.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_6_r47, ruleDecl := ``rubi_4_1_6_r47,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_12_r55, ruleDecl := ``rubi_4_1_12_r55,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n, p must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_12_r56, ruleDecl := ``rubi_4_1_12_r56,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n, p must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_3_1_2_r26, ruleDecl := ``rubi_4_3_1_2_r26,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt, transc1#sec.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_5_1_4_r20, ruleDecl := ``rubi_4_5_1_4_r20,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#geq, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part2 : List CEntry := [
  { rule := rubi_4_5_2_2_r7, ruleDecl := ``rubi_4_5_2_2_r7,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#gt, transc1#csc.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_7_9_r69, ruleDecl := ``rubi_4_7_9_r69,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_7_9_r70, ruleDecl := ``rubi_4_7_9_r70,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_5_1_2_r2, ruleDecl := ``rubi_5_1_2_r2,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt, transc1#arccos.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_5_1_4_r6, ruleDecl := ``rubi_5_1_4_r6,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt, transc1#arccos.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_5_3_4_r21, ruleDecl := ``rubi_5_3_4_r21,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: p must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#geq, relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_5_3_4_r87, ruleDecl := ``rubi_5_3_4_r87,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: p must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#geq, relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_5_3_7_r59, ruleDecl := ``rubi_5_3_7_r59,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_5_3_7_r61, ruleDecl := ``rubi_5_3_7_r61,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt, transc1#coth.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_6_1_12_r5, ruleDecl := ``rubi_6_1_12_r5,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: n, p must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part3 : List CEntry := [
  { rule := rubi_6_1_12_r6, ruleDecl := ``rubi_6_1_12_r6,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: n, p must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_6_1_12_r45, ruleDecl := ``rubi_6_1_12_r45,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n, p must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_6_1_12_r46, ruleDecl := ``rubi_6_1_12_r46,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n, p must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_6_7_9_r3, ruleDecl := ``rubi_6_7_9_r3,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_6_7_9_r71, ruleDecl := ``rubi_6_7_9_r71,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_6_7_9_r72, ruleDecl := ``rubi_6_7_9_r72,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_6_7_9_r74, ruleDecl := ``rubi_6_7_9_r74,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt, transc1#sech.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_6_7_9_r77, ruleDecl := ``rubi_6_7_9_r77,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt, transc1#coth, transc1#csch.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_2_3_r14, ruleDecl := ``rubi_7_2_3_r14,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt, transc1#arccosh, transc1#csch.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_2_4_r2, ruleDecl := ``rubi_7_2_4_r2,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt, transc1#arccosh, transc1#coth.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] }
]

private def part4 : List CEntry := [
  { rule := rubi_7_2_4_r5, ruleDecl := ``rubi_7_2_4_r5,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt, transc1#arccosh.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_2_4_r32, ruleDecl := ``rubi_7_2_4_r32,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#gt, transc1#arccosh.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_2_4_r33, ruleDecl := ``rubi_7_2_4_r33,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m, n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#gt, transc1#arccosh.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_2_5_r1, ruleDecl := ``rubi_7_2_5_r1,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt, transc1#arccosh.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_3_4_r21, ruleDecl := ``rubi_7_3_4_r21,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: p must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#geq, relation1#gt, transc1#arctanh.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_3_4_r87, ruleDecl := ``rubi_7_3_4_r87,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: p must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for arith1#root, relation1#geq, relation1#gt, transc1#arctanh.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_3_4_r128, ruleDecl := ``rubi_7_3_4_r128,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: n must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for transc1#arctanh.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_3_7_r35, ruleDecl := ``rubi_7_3_7_r35,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt, transc1#arctanh, transc1#coth.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_7_3_7_r47, ruleDecl := ``rubi_7_3_7_r47,
    proofs := [], unproved := [.real],
    counterexamples := [], findings := ["The source conditions are transcribed. A derivative proof or a counterexample is pending.", "independence: m must match explicit integers under the source integer guards, so their matches are independent of x.", "complex: unsupported. The pinned registry has no complex interpretation for relation1#gt, transc1#arctanh, transc1#sec.", "Optional source patterns are explicit metavariables in v1; omitted arguments are not matched."] },
  { rule := rubi_4_1_12_r83, ruleDecl := ``rubi_4_1_12_r83, proofs := [], unproved := [.real],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] }
]

private def part5 : List CEntry := [
  { rule := rubi_4_1_12_r84, ruleDecl := ``rubi_4_1_12_r84, proofs := [], unproved := [.real],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_1_1_4_1_r11, ruleDecl := ``rubi_1_1_4_1_r11, proofs := [], unproved := [.real],
    findings := ["independence: j, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_6_1_12_r25, ruleDecl := ``rubi_6_1_12_r25, proofs := [], counterexamples := [(.real, ``rubi_6_1_12_r25_counterexample_real)],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "The real witness satisfies both adjacent comparisons of the source interval.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_6_1_12_r26, ruleDecl := ``rubi_6_1_12_r26, proofs := [], counterexamples := [(.real, ``rubi_6_1_12_r26_counterexample_real)],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "The real witness satisfies both adjacent comparisons of the source interval.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_6_1_12_r35, ruleDecl := ``rubi_6_1_12_r35, proofs := [], unproved := [.real],
    findings := ["independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_6_1_12_r36, ruleDecl := ``rubi_6_1_12_r36, proofs := [], unproved := [.real],
    findings := ["independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_6_1_12_r37, ruleDecl := ``rubi_6_1_12_r37, proofs := [], unproved := [.real],
    findings := ["independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_6_1_12_r38, ruleDecl := ``rubi_6_1_12_r38, proofs := [], unproved := [.real],
    findings := ["independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_6_1_12_r43, ruleDecl := ``rubi_6_1_12_r43, proofs := [], unproved := [.real],
    findings := ["independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_6_1_12_r44, ruleDecl := ``rubi_6_1_12_r44, proofs := [], unproved := [.real],
    findings := ["independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] }
]

private def part6 : List CEntry := [
  { rule := rubi_6_1_12_r67, ruleDecl := ``rubi_6_1_12_r67, proofs := [], unproved := [.real],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_6_1_12_r68, ruleDecl := ``rubi_6_1_12_r68, proofs := [], unproved := [.real],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_4_5_1_2_r80, ruleDecl := ``rubi_4_5_1_2_r80, proofs := [], unproved := [.real],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_4_1_2_1_r88, ruleDecl := ``rubi_4_1_2_1_r88, proofs := [], counterexamples := [(.real, ``rubi_4_1_2_1_r88_counterexample_real)],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "The real witness satisfies both adjacent comparisons of the source interval.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_4_1_2_2_r3, ruleDecl := ``rubi_4_1_2_2_r3, proofs := [], unproved := [.real],
    findings := ["Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_4_5_1_2_r81, ruleDecl := ``rubi_4_5_1_2_r81, proofs := [], counterexamples := [(.real, ``rubi_4_5_1_2_r81_counterexample_real)],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "The real witness satisfies both adjacent comparisons of the source interval.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_7_3_6_r56, ruleDecl := ``rubi_7_3_6_r56, proofs := [], counterexamples := [(.real, ``rubi_7_3_6_r56_counterexample_real)],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "The real witness satisfies both adjacent comparisons of the source interval.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_7_3_3_exp_r40, ruleDecl := ``rubi_7_3_3_exp_r40, proofs := [], counterexamples := [(.real, ``rubi_7_3_3_exp_r40_counterexample_real)],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "The real witness satisfies both adjacent comparisons of the source interval.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_7_3_3_exp_r78, ruleDecl := ``rubi_7_3_3_exp_r78, proofs := [], counterexamples := [(.real, ``rubi_7_3_3_exp_r78_counterexample_real)],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "The real witness satisfies both adjacent comparisons of the source interval.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_7_3_3_exp_r56, ruleDecl := ``rubi_7_3_3_exp_r56, proofs := [], counterexamples := [(.real, ``rubi_7_3_3_exp_r56_counterexample_real)],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "The real witness satisfies both adjacent comparisons of the source interval.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] }
]

private def part7 : List CEntry := [
  { rule := rubi_7_3_6_r40, ruleDecl := ``rubi_7_3_6_r40, proofs := [], counterexamples := [(.real, ``rubi_7_3_6_r40_counterexample_real)],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "The real witness satisfies both adjacent comparisons of the source interval.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_7_3_6_r78, ruleDecl := ``rubi_7_3_6_r78, proofs := [], counterexamples := [(.real, ``rubi_7_3_6_r78_counterexample_real)],
    findings := ["independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.", "The real witness satisfies both adjacent comparisons of the source interval.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] },
  { rule := rubi_4_5_2_1_r39, ruleDecl := ``rubi_4_5_2_1_r39, proofs := [], unproved := [.real],
    findings := ["Both adjacent comparisons of the source interval are required. Earlier evidence for the incomplete condition does not establish a status here.", "complex: unsupported. The registry has no complex interpretation of the order predicate."] }
]

def entries : List CEntry :=
  part1 ++ part2 ++ part3 ++ part4 ++ part5 ++ part6 ++ part7

theorem entries_wellFormed : ∀ e ∈ entries,
    (if e.rule.shape == .antiderivRec || e.rule.shape == .antiderivSubst then e.rule.recOk else e.rule.wellFormed) = true := by
  intro e he
  apply List.all_eq_true.mp _ e he
  decide +kernel

end OSR.IntegrationBounds
