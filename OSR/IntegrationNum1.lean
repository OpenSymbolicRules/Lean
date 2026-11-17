import OSR.IntegrationFindings

/-!
# Integration (RUBI): strengthened variants checked numerically

Strengthened variants (Specification V1-R-005e) of refuted RUBI rules,
distributed before their proof: each appends the non-degeneracy conditions
that the RUBI rule leaves to rule order or evaluation, and carries a
`numerical:` finding with the evidence (an adversarial numerical check over
ℝ).  No proof is claimed; the catalogue marks both domains as unproved.
The refutations of the rules as stated are kept.  Proved variants move to
the `IntegrationRec*` modules.
-/

namespace OSR.IntegrationNum1

open OSR OSR.Calculus OSR.IntegrationFindings

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- rubi_3_1_4_r17 with NeQ[d, 0] (numerically checked) -/
def rubi314r17Nondeg : CRule where
  id := "integration.rubi_3_1_4_r17_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "p", "q"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .gt (.int (-1)) (.var "q"),
    .int (.app2 .mul (.int 2) (.var "q")),
    .ne (.var "d") (.int 0)]
  priority := 9001
  description := "rubi_3_1_4_r17 with NeQ[d, 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:17" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#17"

/-- rubi_3_1_5_r16 with NeQ[d, 0] (numerically checked) -/
def rubi315r16Nondeg : CRule where
  id := "integration.rubi_3_1_5_r16_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "p", "q"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .gt (.int (-1)) (.var "q"),
    .int (.app2 .mul (.int 2) (.var "q")),
    .ne (.var "d") (.int 0)]
  priority := 9002
  description := "rubi_3_1_5_r16 with NeQ[d, 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:16" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#16"

/-- rubi_3_3_r22 with NeQ[Multiply[g, r, Add[q, 1]], 0] (numerically checked) -/
def rubi33r22Nondeg : CRule where
  id := "integration.rubi_3_3_r22_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:22"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.var "r")))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.var "g") (.var "r")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.app2 .mul (.var "g") (.var "r")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "q", "r", "p"]
  conditions := [.eq (.var "m") (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "q") (.int (-1)),
    .int (.var "p"),
    .gt (.var "p") (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "g") (.var "r")) (.app2 .add (.var "q") (.int 1))) (.int 0)]
  priority := 9003
  description := "rubi_3_3_r22 with NeQ[Multiply[g, r, Add[q, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p:22" "3 Logarithms/3.3 u (a+b log(c (d+e x)^n))^p.m#22"

/-- rubi_1_1_1_4_r38 with NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0] (numerically checked) -/
def rubi1114r38Nondeg : CRule where
  id := "integration.rubi_1_1_1_4_r38_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:38"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "q"))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "q"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "q", "p"]
  conditions := [.gt (.var "p") (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 9005
  description := "rubi_1_1_1_4_r38 with NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:38" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#38"

/-- rubi_1_1_3_3_r15 with NeQ[Multiply[b, Add[Multiply[n, Add[p, 1]], 1]], 0] (numerically checked) -/
def rubi1133r15Nondeg : CRule where
  id := "integration.rubi_1_1_3_3_r15_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))))) (.pow (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)) (.int 0),
    .ne (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.int 0)]
  priority := 9006
  description := "rubi_1_1_3_3_r15 with NeQ[Multiply[b, Add[Multiply[n, Add[p, 1]], 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:15" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#15"

/-- rubi_1_2_1_2_r102 with NeQ[Multiply[4, a, c, Add[p, 1]], 0] (numerically checked) -/
def rubi1212r102Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r102_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:102"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.int 2)) (.var "c")) (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "m")) (.int 2)) (.var "c")) (.var "d")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9007
  description := "rubi_1_2_1_2_r102 with NeQ[Multiply[4, a, c, Add[p, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:102" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#102"

/-- rubi_1_2_1_3_r15 with NeQ[Multiply[c, Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (numerically checked) -/
def rubi1213r15Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r15_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g")))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "g"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "e")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g"))))) (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e")) (.var "g")))))) (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.var "p") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c")) (.var "e")) (.var "g"))) (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g")))))) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .ne (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)]
  priority := 9008
  description := "rubi_1_2_1_3_r15 with NeQ[Multiply[c, Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:15" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#15"

/-- rubi_1_2_1_3_r35 with NeQ[c, 0] (numerically checked) -/
def rubi1213r35Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r35_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:35"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "c") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "c") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))),
    ("I2", (.app2 .mul (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "f", "g", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "a") (.pow (.var "g") (.int 2))) (.app2 .mul (.pow (.var "f") (.int 2)) (.var "c"))) (.int 0),
    .ne (.var "c") (.int 0)]
  priority := 9009
  description := "rubi_1_2_1_3_r35 with NeQ[c, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:35" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#35"

/-- rubi_1_2_1_6_r8 with NeQ[a, 0]; NeQ[c, 0] (numerically checked) -/
def rubi1216r8Nondeg : CRule where
  id := "integration.rubi_1_2_1_6_r8_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "m")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "g")) (.pow (.var "a") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "h")) (.var "x")) (.pow (.var "c") (.int (-1))))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "m") (.var "p")))))]
  independent := ["a", "c", "d", "f", "g", "h", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.pow (.var "h") (.int 2)))) (.int 0),
    .int (.var "m"),
    .ne (.var "a") (.int 0),
    .ne (.var "c") (.int 0)]
  priority := 9010
  description := "rubi_1_2_1_6_r8 with NeQ[a, 0]; NeQ[c, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:8" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#8"

/-- rubi_1_2_2_4_r12 with NeQ[d, 0]; NeQ[e, 0] (numerically checked) -/
def rubi1224r12Nondeg : CRule where
  id := "integration.rubi_1_2_2_4_r12_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.var "p")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "f", "q", "m", "q", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p"),
    .ne (.var "d") (.int 0),
    .ne (.var "e") (.int 0)]
  priority := 9011
  description := "rubi_1_2_2_4_r12 with NeQ[d, 0]; NeQ[e, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:12" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#12"

/-- rubi_4_7_6_r16 with NeQ[Multiply[b, d, Add[n, 1]], 0] (numerically checked) -/
def rubi476r16Nondeg : CRule where
  id := "integration.rubi_4_7_6_r16_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int 0)]
  priority := 9013
  description := "rubi_4_7_6_r16 with NeQ[Multiply[b, d, Add[n, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:16" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#16"

/-- rubi_4_7_8_r47 with NeQ[Multiply[a, n], 0]; NeQ[n, 0] (numerically checked) -/
def rubi478r47Nondeg : CRule where
  id := "integration.rubi_4_7_8_r47_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:47"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .sin (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .cos (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app2 .mul (.var "a") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "n") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .sin (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))))]
  independent := ["a", "b", "m", "n"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.app2 .mul (.var "a") (.var "n")) (.int 0),
    .ne (.var "n") (.int 0)]
  priority := 9014
  description := "rubi_4_7_8_r47 with NeQ[Multiply[a, n], 0]; NeQ[n, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:47" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#47"

/-- rubi_4_7_9_r26 with NeQ[b, 0] (numerically checked) -/
def rubi479r26Nondeg : CRule where
  id := "integration.rubi_4_7_9_r26_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:26"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0),
    .ne (.var "b") (.int 0)]
  priority := 9015
  description := "rubi_4_7_9_r26 with NeQ[b, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:26" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#26"

/-- rubi_3_1_2_r3 with NeQ[Multiply[d, Add[m, 1]], 0] (numerically checked) -/
def rubi312r3Nondeg : CRule where
  id := "integration.rubi_3_1_2_r3_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:3"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.ne (.var "m") (.int (-1)),
    .eq (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n"))) (.int 0),
    .ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0)]
  priority := 9016
  description := "rubi_3_1_2_r3 with NeQ[Multiply[d, Add[m, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:3" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#3"

/-- rubi_3_1_3_r7 with NeQ[Multiply[b, n, Add[p, 1]], 0] (numerically checked) -/
def rubi313r7Nondeg : CRule where
  id := "integration.rubi_3_1_3_r7_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "q")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "n", "p", "q"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .gt (.var "q") (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9017
  description := "rubi_3_1_3_r7 with NeQ[Multiply[b, n, Add[p, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:7" "3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p.m#7"

/-- rubi_3_1_4_r13 with NeQ[Multiply[2, d, f, Add[q, 1]], 0]; NeQ[Multiply[2, d, Add[q, 1]], 0] (numerically checked) -/
def rubi314r13Nondeg : CRule where
  id := "integration.rubi_3_1_4_r13_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 3))) (.app2 .mul (.var "b") (.var "n"))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 3))) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q"]
  conditions := [.int (.var "q"),
    .gt (.int (-1)) (.var "q"),
    .int (.var "m"),
    .gt (.int 0) (.var "m"),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int 0)]
  priority := 9018
  description := "rubi_3_1_4_r13 with NeQ[Multiply[2, d, f, Add[q, 1]], 0]; NeQ[Multiply[2, d, Add[q, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:13" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#13"

/-- rubi_3_5_r21 with NeQ[Multiply[b, n, q, Add[p, 1]], 0]; NeQ[Multiply[b, n, q], 0] (numerically checked) -/
def rubi35r21Nondeg : CRule where
  id := "integration.rubi_3_5_r21_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:21"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "e") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "r")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.var "q")))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p", "q", "r"]
  conditions := [.eq (.var "r") (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1)),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.var "q"))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.app2 .add (.var "p") (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int 0)]
  priority := 9020
  description := "rubi_3_5_r21 with NeQ[Multiply[b, n, q, Add[p, 1]], 0]; NeQ[Multiply[b, n, q], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:21" "3 Logarithms/3.5 Miscellaneous logarithms.m#21"

/-- rubi_1_2_1_1_r5 with NeQ[Multiply[2, c, Add[Multiply[2, p], 1]], 0] (numerically checked) -/
def rubi1211r5Nondeg : CRule where
  id := "integration.rubi_1_2_1_1_r5_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:5"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "p")) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))]
  independent := ["a", "b", "c", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.var "p") (.int 0),
    .int (.app2 .mul (.int 4) (.var "p")),
    .ne (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.int 0)]
  priority := 9021
  description := "rubi_1_2_1_1_r5 with NeQ[Multiply[2, c, Add[Multiply[2, p], 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p:5" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.1 (a+b x+c x^2)^p.m#5"

/-- rubi_1_2_1_2_r39 with NeQ[Multiply[e, Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0]; NeQ[Multiply[Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (numerically checked) -/
def rubi1212r39Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r39_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:39"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.pow (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "m") (.int 0),
    .int (.app2 .mul (.int 2) (.var "p")),
    .ne (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0),
    .ne (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)]
  priority := 9022
  description := "rubi_1_2_1_2_r39 with NeQ[Multiply[e, Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0]; NeQ[Multiply[Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:39" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#39"

/-- rubi_1_2_1_3_r33 with NeQ[Multiply[c, Add[m, Multiply[2, p], 2]], 0]; NeQ[Multiply[e, Add[m, Multiply[2, p], 2]], 0] (numerically checked) -/
def rubi1213r33Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r33_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.var "e") (.var "f")))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "f")) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2)) (.int 0),
    .ne (.var "m") (.int 2),
    .ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int 0),
    .ne (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.int 0)]
  priority := 9023
  description := "rubi_1_2_1_3_r33 with NeQ[Multiply[c, Add[m, Multiply[2, p], 2]], 0]; NeQ[Multiply[e, Add[m, Multiply[2, p], 2]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:33" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#33"

/-- rubi_1_2_1_6_r7 with NeQ[a, 0]; NeQ[c, 0] (numerically checked) -/
def rubi1216r7Nondeg : CRule where
  id := "integration.rubi_1_2_1_6_r7_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "m")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "g")) (.pow (.var "a") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "h")) (.var "x")) (.pow (.var "c") (.int (-1))))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "m") (.var "p")))))]
  independent := ["a", "b", "c", "d", "f", "g", "h", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")) (.var "h"))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.pow (.var "h") (.int 2)))) (.int 0),
    .int (.var "m"),
    .ne (.var "a") (.int 0),
    .ne (.var "c") (.int 0)]
  priority := 9024
  description := "rubi_1_2_1_6_r7 with NeQ[a, 0]; NeQ[c, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:7" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#7"

/-- rubi_1_2_2_4_r11 with NeQ[d, 0]; NeQ[e, 0] (numerically checked) -/
def rubi1224r11Nondeg : CRule where
  id := "integration.rubi_1_2_2_4_r11_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.var "p")))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "q", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p"),
    .ne (.var "d") (.int 0),
    .ne (.var "e") (.int 0)]
  priority := 9025
  description := "rubi_1_2_2_4_r11 with NeQ[d, 0]; NeQ[e, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:11" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#11"

/-- rubi_4_7_6_r2 with NeQ[Multiply[b, Add[n, 1]], 0] (numerically checked) -/
def rubi476r2Nondeg : CRule where
  id := "integration.rubi_4_7_6_r2_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m"))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1)),
    .ne (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int 0)]
  priority := 9026
  description := "rubi_4_7_6_r2 with NeQ[Multiply[b, Add[n, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:2" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#2"

/-- rubi_4_7_9_r25 with NeQ[b, 0] (numerically checked) -/
def rubi479r25Nondeg : CRule where
  id := "integration.rubi_4_7_9_r25_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0),
    .ne (.var "b") (.int 0)]
  priority := 9027
  description := "rubi_4_7_9_r25 with NeQ[b, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:25" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#25"

/-- log_power_over_linear_square with NeQ[d, 0] (numerically checked) -/
def logPowOverSqNondeg : CRule where
  id := "integration.log_power_over_linear_square_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.var "d") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "n", "p"]
  conditions := [.gt (.var "p") (.int 0),
    .ne (.var "d") (.int 0)]
  priority := 9028
  description := "log_power_over_linear_square with NeQ[d, 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:5" "3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p.m#5"

/-- rubi_3_1_4_r12 with NeQ[Multiply[e, Add[q, 1]], 0] (numerically checked) -/
def rubi314r12Nondeg : CRule where
  id := "integration.rubi_3_1_4_r12_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "m")) (.app2 .mul (.var "b") (.var "n"))) (.app2 .mul (.app2 .mul (.var "b") (.var "m")) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q"]
  conditions := [.int (.var "q"),
    .gt (.int (-1)) (.var "q"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int 0)]
  priority := 9029
  description := "rubi_3_1_4_r12 with NeQ[Multiply[e, Add[q, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:12" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#12"

/-- rubi_3_1_5_r13 with NeQ[d, 0] (numerically checked) -/
def rubi315r13Nondeg : CRule where
  id := "integration.rubi_3_1_5_r13_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .ne (.var "d") (.int 0)]
  priority := 9030
  description := "rubi_3_1_5_r13 with NeQ[d, 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:13" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#13"

/-- two_linear_factors_times_powers with NeQ[Multiply[Power[b, 2], Power[d, 2], Add[m, n, 2], Add[m, n, 3]], 0] (numerically checked) -/
def linFourNondeg : CRule where
  id := "integration.two_linear_factors_times_powers_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "d") (.int 2))) (.var "f")) (.var "h")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))))) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "m") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2)) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3))) (.int 0)]
  priority := 9031
  description := "two_linear_factors_times_powers with NeQ[Multiply[Power[b, 2], Power[d, 2], Add[m, n, 2], Add[m, n, 3]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:6" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#6"

/-- rubi_1_1_3_4_r25 with NeQ[Multiply[b1, b2, e, Add[m, Multiply[n, Add[p, 1]], 1]], 0]; NeQ[Multiply[b1, b2, Add[m, Multiply[n, Add[p, 1]], 1]], 0] (numerically checked) -/
def rubi1134r25Nondeg : CRule where
  id := "integration.rubi_1_1_3_4_r25_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "non2")))) (.var "p"))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "non2")))) (.var "p"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b1") (.var "b2")) (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a1") (.var "a2")) (.var "d")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b1")) (.var "b2")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b1") (.var "b2")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.var "p"))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.var "p"))))]
  independent := ["a1", "b1", "a2", "b2", "c", "d", "e", "m", "n", "p", "non2"]
  conditions := [.eq (.var "non2") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1)))),
    .eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b1") (.var "b2")) (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "b1") (.var "b2")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int 0)]
  priority := 9032
  description := "rubi_1_1_3_4_r25 with NeQ[Multiply[b1, b2, e, Add[m, Multiply[n, Add[p, 1]], 1]], 0]; NeQ[Multiply[b1, b2, Add[m, Multiply[n, Add[p, 1]], 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:25" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#25"

/-- rubi_1_2_1_6_r6 with NeQ[a, 0]; NeQ[c, 0] (numerically checked) -/
def rubi1216r6Nondeg : CRule where
  id := "integration.rubi_1_2_1_6_r6_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "m")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "g")) (.pow (.var "a") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "h")) (.var "x")) (.pow (.var "c") (.int (-1))))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "m") (.var "p")))))]
  independent := ["a", "c", "d", "e", "f", "g", "h", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "e")) (.var "g")) (.var "h"))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.pow (.var "h") (.int 2)))) (.int 0),
    .int (.var "m"),
    .ne (.var "a") (.int 0),
    .ne (.var "c") (.int 0)]
  priority := 9033
  description := "rubi_1_2_1_6_r6 with NeQ[a, 0]; NeQ[c, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:6" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#6"

/-- rubi_1_2_2_3_r8 with NeQ[d, 0]; NeQ[e, 0] (numerically checked) -/
def rubi1223r8Nondeg : CRule where
  id := "integration.rubi_1_2_2_3_r8_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.var "q"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "q", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p"),
    .ne (.var "d") (.int 0),
    .ne (.var "e") (.int 0)]
  priority := 9034
  description := "rubi_1_2_2_3_r8 with NeQ[d, 0]; NeQ[e, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:8" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#8"

/-- rubi_1_2_3_3_r20 with NeQ[Multiply[e, Add[Multiply[n, Add[q, 2]], 1]], 0] (numerically checked) -/
def rubi1233r20Nondeg : CRule where
  id := "integration.rubi_1_2_3_3_r20_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "c", "d", "e", "n", "q", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .ne (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.int 0)]
  priority := 9035
  description := "rubi_1_2_3_3_r20 with NeQ[Multiply[e, Add[Multiply[n, Add[q, 2]], 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:20" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#20"

/-- rubi_4_1_13_r2 with NeQ[Multiply[4, c], 0] (numerically checked) -/
def rubi4113r2Nondeg : CRule where
  id := "integration.rubi_4_1_13_r2_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:2"
  shape := .antiderivRec; x := "x"
  body := (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))
  result := (.var "I1")
  integrals := [("I1", (.app1 .cos (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))))]
  independent := ["a", "b", "c"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .mul (.int 4) (.var "c")) (.int 0)]
  priority := 9036
  description := "rubi_4_1_13_r2 with NeQ[Multiply[4, c], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:2" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#2"

/-- rubi_4_1_13_r16 with NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (numerically checked) -/
def rubi4113r16Nondeg : CRule where
  id := "integration.rubi_4_1_13_r16_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .gt (.int (-1)) (.var "m"),
    .ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int 0)]
  priority := 9037
  description := "rubi_4_1_13_r16 with NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:16" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#16"

/-- rubi_4_7_6_r1 with NeQ[Multiply[b, Add[n, 1]], 0] (numerically checked) -/
def rubi476r1Nondeg : CRule where
  id := "integration.rubi_4_7_6_r1_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1)),
    .ne (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int 0)]
  priority := 9038
  description := "rubi_4_7_6_r1 with NeQ[Multiply[b, Add[n, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:1" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#1"

/-- rubi_4_7_9_r16 with NeQ[a, 0] (numerically checked) -/
def rubi479r16Nondeg : CRule where
  id := "integration.rubi_4_7_9_r16_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .ne (.var "a") (.int 0)]
  priority := 9039
  description := "rubi_4_7_9_r16 with NeQ[a, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:16" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#16"

/-- rubi_2_1_r9 with NeQ[Multiply[a, d, Add[m, 1]], 0]; NeQ[a, 0] (numerically checked) -/
def rubi21r9Nondeg : CRule where
  id := "integration.rubi_2_1_r9_nondegenerate"; legacyId := some "rubi:2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))) (.int (-1)))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.var "a") (.int 0)]
  priority := 9040
  description := "rubi_2_1_r9 with NeQ[Multiply[a, d, Add[m, 1]], 0]; NeQ[a, 0] (numerically checked)"
  provenance := migrated "rubi:2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p:9" "2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p.m#9"

/-- rubi_3_1_4_r9 with NeQ[d, 0] (numerically checked) -/
def rubi314r9Nondeg : CRule where
  id := "integration.rubi_3_1_4_r9_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "r", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .int (.var "r"),
    .gt (.var "r") (.int 0),
    .int (.var "m"),
    .gt (.int (-1)) (.var "m"),
    .ne (.var "d") (.int 0)]
  priority := 9041
  description := "rubi_3_1_4_r9 with NeQ[d, 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:9" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#9"

/-- rubi_3_1_5_r8 with NeQ[Multiply[e, Add[q, 1]], 0] (numerically checked) -/
def rubi315r8Nondeg : CRule where
  id := "integration.rubi_3_1_5_r8_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "m")) (.app2 .mul (.var "b") (.var "n"))) (.app2 .mul (.app2 .mul (.var "b") (.var "m")) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q"]
  conditions := [.int (.var "q"),
    .gt (.int (-1)) (.var "q"),
    .gt (.var "m") (.int 0),
    .ne (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int 0)]
  priority := 9042
  description := "rubi_3_1_5_r8 with NeQ[Multiply[e, Add[q, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:8" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#8"

/-- rubi_3_2_1_r1 with NeQ[b, 0] (numerically checked) -/
def rubi321r1Nondeg : CRule where
  id := "integration.rubi_3_2_1_r1_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))) (.var "p"))) (.pow (.var "b") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "n")) (.var "p")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "b") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .ln (.app2 .mul (.var "e") (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))) (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0),
    .ne (.var "b") (.int 0)]
  priority := 9043
  description := "rubi_3_2_1_r1 with NeQ[b, 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p:1" "3 Logarithms/3.2.1 (f+g x)^m (A+B log(e ((a+b x) over (c+d x))^n))^p.m#1"

/-- rubi_3_5_r16 with NeQ[Multiply[b, n, q, Add[p, 1]], 0]; NeQ[Multiply[b, n, q], 0] (numerically checked) -/
def rubi35r16Nondeg : CRule where
  id := "integration.rubi_3_5_r16_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.5 Miscellaneous logarithms:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "r")) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.var "m"))) (.app2 .mul (.var "b") (.pow (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))) (.var "q")))) (.var "p"))))]
  independent := ["a", "b", "c", "m", "n", "p", "q", "r"]
  conditions := [.eq (.var "r") (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.app2 .add (.var "p") (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "q")) (.int 0)]
  priority := 9045
  description := "rubi_3_5_r16 with NeQ[Multiply[b, n, q, Add[p, 1]], 0]; NeQ[Multiply[b, n, q], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.5 Miscellaneous logarithms:16" "3 Logarithms/3.5 Miscellaneous logarithms.m#16"

/-- rubi_1_1_3_4_r17 with NeQ[Multiply[a, b, e, Add[m, 1]], 0]; NeQ[b, 0] (numerically checked) -/
def rubi1134r17Nondeg : CRule where
  id := "integration.rubi_1_1_3_4_r17_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "e")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)) (.int 0),
    .ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "e")) (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.var "b") (.int 0)]
  priority := 9046
  description := "rubi_1_1_3_4_r17 with NeQ[Multiply[a, b, e, Add[m, 1]], 0]; NeQ[b, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:17" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#17"

/-- rubi_1_1_3_5_r30 with NeQ[b, 0] (numerically checked) -/
def rubi1135r30Nondeg : CRule where
  id := "integration.rubi_1_1_3_5_r30_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.var "q"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.var "n")))) (.var "r"))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "r", "p", "q"]
  conditions := [.int (.var "p"),
    .gt (.int 0) (.var "p"),
    .gt (.var "q") (.int 0),
    .ne (.var "b") (.int 0)]
  priority := 9047
  description := "rubi_1_1_3_5_r30 with NeQ[b, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:30" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#30"

/-- rubi_1_2_2_2_r17 with NeQ[Multiply[a, d, Add[m, 1]], 0]; NeQ[Multiply[a, Power[d, 2]], 0] (numerically checked) -/
def rubi1222r17Nondeg : CRule where
  id := "integration.rubi_1_2_2_2_r17_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.var "a") (.pow (.var "d") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.app2 .add (.var "b") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.int (-1)) (.var "m"),
    .ne (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .mul (.var "a") (.pow (.var "d") (.int 2))) (.int 0)]
  priority := 9048
  description := "rubi_1_2_2_2_r17 with NeQ[Multiply[a, d, Add[m, 1]], 0]; NeQ[Multiply[a, Power[d, 2]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p:17" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.2 (d x)^m (a+b x^2+c x^4)^p.m#17"

/-- rubi_1_2_2_4_r58 with NeQ[Multiply[d, e], 0]; NeQ[Multiply[d, e, Power[f, 2]], 0] (numerically checked) -/
def rubi1224r58Nondeg : CRule where
  id := "integration.rubi_1_2_2_4_r58_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:58"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "d") (.var "e")) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.pow (.var "f") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f", "m", "p"]
  conditions := [.gt (.var "p") (.int 0),
    .gt (.int 0) (.var "m"),
    .ne (.app2 .mul (.var "d") (.var "e")) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.pow (.var "f") (.int 2))) (.int 0)]
  priority := 9049
  description := "rubi_1_2_2_4_r58 with NeQ[Multiply[d, e], 0]; NeQ[Multiply[d, e, Power[f, 2]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:58" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#58"

/-- rubi_1_2_3_3_r12 with NeQ[d, 0]; NeQ[e, 0] (numerically checked) -/
def rubi1233r12Nondeg : CRule where
  id := "integration.rubi_1_2_3_3_r12_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.var "q"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.var "n")))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "n", "q", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p"),
    .ne (.var "d") (.int 0),
    .ne (.var "e") (.int 0)]
  priority := 9050
  description := "rubi_1_2_3_3_r12 with NeQ[d, 0]; NeQ[e, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:12" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#12"

/-- rubi_4_1_12_r43 with NeQ[Multiply[Power[b, 2], Power[n, 2], Power[p, 2]], 0]; NeQ[Multiply[b, n, p], 0]; NeQ[p, 0] (numerically checked) -/
def rubi4112r43Nondeg : CRule where
  id := "integration.rubi_4_1_12_r43_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:43"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "n") (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.var "n"))) (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))) (.pow (.var "p") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)) (.int 0),
    .gt (.var "p") (.int 1),
    .ne (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int 0),
    .ne (.var "p") (.int 0)]
  priority := 9051
  description := "rubi_4_1_12_r43 with NeQ[Multiply[Power[b, 2], Power[n, 2], Power[p, 2]], 0]; NeQ[Multiply[b, n, p], 0]; NeQ[p, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:43" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#43"

/-- rubi_4_1_13_r14 with NeQ[Multiply[2, c], 0] (numerically checked) -/
def rubi4113r14Nondeg : CRule where
  id := "integration.rubi_4_1_13_r14_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .gt (.var "m") (.int 1),
    .ne (.app2 .mul (.int 2) (.var "c")) (.int 0)]
  priority := 9052
  description := "rubi_4_1_13_r14 with NeQ[Multiply[2, c], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:14" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#14"

/-- rubi_4_1_13_r22 with NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (numerically checked) -/
def rubi4113r22Nondeg : CRule where
  id := "integration.rubi_4_1_13_r22_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:22"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0),
    .gt (.int (-1)) (.var "m"),
    .ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int 0)]
  priority := 9053
  description := "rubi_4_1_13_r22 with NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:22" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#22"

/-- rubi_4_7_8_r13 with NeQ[Add[Multiply[Power[b, 2], Power[d, 2], e, Power[n, 2], Power[p, 2]], Multiply[e, Power[Add[m, 1], 2]]], 0] (numerically checked) -/
def rubi478r13Nondeg : CRule where
  id := "integration.rubi_4_7_8_r13_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 1),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int 0)]
  priority := 9054
  description := "rubi_4_7_8_r13 with NeQ[Add[Multiply[Power[b, 2], Power[d, 2], e, Power[n, 2], Power[p, 2]], Multiply[e, Power[Add[m, 1], 2]]], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:13" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#13"

/-- rubi_4_7_9_r11 with NeQ[Power[b, 2], 0]; NeQ[b, 0] (numerically checked) -/
def rubi479r11Nondeg : CRule where
  id := "integration.rubi_4_7_9_r11_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "b") (.int (-1)))) (.var "I2"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I3")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))),
    ("I3", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 1),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.pow (.var "b") (.int 2)) (.int 0),
    .ne (.var "b") (.int 0)]
  priority := 9055
  description := "rubi_4_7_9_r11 with NeQ[Power[b, 2], 0]; NeQ[b, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:11" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#11"

/-- rubi_2_1_r10 with NeQ[a, 0] (numerically checked) -/
def rubi21r10Nondeg : CRule where
  id := "integration.rubi_2_1_r10_nondegenerate"; legacyId := some "rubi:2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))) (.app2 .add (.var "p") (.int 1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.pow (.var "F") (.app2 .mul (.var "g") (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))) (.var "p"))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "n", "m", "p"]
  conditions := [.int (.var "p"),
    .gt (.int 0) (.var "p"),
    .int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "a") (.int 0)]
  priority := 9056
  description := "rubi_2_1_r10 with NeQ[a, 0] (numerically checked)"
  provenance := migrated "rubi:2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p:10" "2 Exponentials/2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p.m#10"

/-- rubi_3_1_1_r3 with NeQ[Multiply[b, n, Add[p, 1]], 0] (numerically checked) -/
def rubi311r3Nondeg : CRule where
  id := "integration.rubi_3_1_1_r3_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.1 (a+b log(c x^n))^p:3"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "b", "c", "n", "p"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .int (.app2 .mul (.int 2) (.var "p")),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9057
  description := "rubi_3_1_1_r3 with NeQ[Multiply[b, n, Add[p, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.1 (a+b log(c x^n))^p:3" "3 Logarithms/3.1.1 (a+b log(c x^n))^p.m#3"

/-- rubi_3_1_5_r9 with NeQ[Multiply[2, d, f, Add[q, 1]], 0]; NeQ[Multiply[2, d, Add[q, 1]], 0] (numerically checked) -/
def rubi315r9Nondeg : CRule where
  id := "integration.rubi_3_1_5_r9_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 3))) (.app2 .mul (.var "b") (.var "n"))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 3))) (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q"]
  conditions := [.int (.var "q"),
    .gt (.int (-1)) (.var "q"),
    .int (.var "m"),
    .gt (.int 0) (.var "m"),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "f")) (.app2 .add (.var "q") (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int 0)]
  priority := 9058
  description := "rubi_3_1_5_r9 with NeQ[Multiply[2, d, f, Add[q, 1]], 0]; NeQ[Multiply[2, d, Add[q, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:9" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#9"

/-- rubi_3_4_r2 with NeQ[d, 0] (numerically checked) -/
def rubi34r2Nondeg : CRule where
  id := "integration.rubi_3_4_r2_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:2"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int (-1))))) (.var "p")))))) (.var "q"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.var "e") (.app2 .mul (.var "d") (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int (-1))))) (.var "p")))))) (.var "q"))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.var "p")) (.var "q")) (.pow (.var "d") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int (-1))))) (.var "p")))))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p", "q"]
  conditions := [.int (.var "q"),
    .gt (.var "q") (.int 0),
    .ne (.var "d") (.int 0)]
  priority := 9062
  description := "rubi_3_4_r2 with NeQ[d, 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p:2" "3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p.m#2"

/-- rubi_1_1_1_4_r3 with NeQ[Multiply[b, d, Power[Add[Multiply[b, c], Multiply[-1, a, d]], 2], Add[m, 1], Add[n, 1]], 0] (numerically checked) -/
def rubi1114r3Nondeg : CRule where
  id := "integration.rubi_1_1_1_4_r3_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "n"))) (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "c")) (.var "d")) (.var "e")) (.var "g")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "c")) (.var "d")) (.var "f")) (.var "h")) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2)))))) (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "d") (.int 2))) (.var "f")) (.var "h")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.pow (.var "d") (.int 2))) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "m") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2)))))) (.var "x"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "d") (.int 2))) (.var "f")) (.var "h")) (.app2 .add (.app2 .add (.int 2) (.app2 .mul (.int 3) (.var "n"))) (.pow (.var "n") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "f")) (.var "h")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))))) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "h")) (.app2 .add (.app2 .add (.int 2) (.app2 .mul (.int 3) (.var "m"))) (.pow (.var "m") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.app2 .add (.app2 .mul (.var "f") (.var "g")) (.app2 .mul (.var "e") (.var "h")))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 3)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.var "e")) (.var "g")) (.app2 .add (.app2 .add (.app2 .add (.app2 .add (.int 6) (.pow (.var "m") (.int 2))) (.app2 .mul (.int 5) (.var "n"))) (.pow (.var "n") (.int 2))) (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.int 5))))))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "n"]
  conditions := [.gt (.int (-1)) (.var "m"),
    .gt (.int (-1)) (.var "n"),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "n") (.int 1))) (.int 0)]
  priority := 9063
  description := "rubi_1_1_1_4_r3 with NeQ[Multiply[b, d, Power[Add[Multiply[b, c], Multiply[-1, a, d]], 2], Add[m, 1], Add[n, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q:3" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.m#3"

/-- power_binomial_times_linear with NeQ[Multiply[b, e, Add[m, Multiply[n, Add[p, 1]], 1]], 0]; NeQ[Multiply[b, Add[m, Multiply[n, Add[p, 1]], 1]], 0] (numerically checked) -/
def binomPowLinNondeg : CRule where
  id := "integration.power_binomial_times_linear_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))))) (.pow (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1)) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int 0),
    .ne (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1)))) (.int 1))) (.int 0)]
  priority := 9064
  description := "power_binomial_times_linear with NeQ[Multiply[b, e, Add[m, Multiply[n, Add[p, 1]], 1]], 0]; NeQ[Multiply[b, Add[m, Multiply[n, Add[p, 1]], 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q:24" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q.m#24"

/-- rubi_1_2_1_2_r54 with NeQ[Multiply[d, Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0]; NeQ[Multiply[Power[d, 2], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (numerically checked) -/
def rubi1212r54Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r54_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:54"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-4)) (.var "b")) (.var "c")) (.pow (.app2 .mul (.var "d") (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .ne (.app2 .mul (.var "d") (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0),
    .ne (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)]
  priority := 9065
  description := "rubi_1_2_1_2_r54 with NeQ[Multiply[d, Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0]; NeQ[Multiply[Power[d, 2], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:54" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#54"

/-- rubi_1_2_1_6_r5 with NeQ[a, 0]; NeQ[c, 0] (numerically checked) -/
def rubi1216r5Nondeg : CRule where
  id := "integration.rubi_1_2_1_6_r5_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "m")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "g")) (.pow (.var "a") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "h")) (.var "x")) (.pow (.var "c") (.int (-1))))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "m") (.var "p")))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "g")) (.var "h"))) (.app2 .mul (.var "a") (.pow (.var "h") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.pow (.var "g") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "e")) (.var "g")) (.var "h"))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "f")) (.pow (.var "h") (.int 2)))) (.int 0),
    .int (.var "m"),
    .ne (.var "a") (.int 0),
    .ne (.var "c") (.int 0)]
  priority := 9066
  description := "rubi_1_2_1_6_r5 with NeQ[a, 0]; NeQ[c, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:5" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#5"

/-- rubi_1_2_2_3_r7 with NeQ[d, 0]; NeQ[e, 0] (numerically checked) -/
def rubi1223r7Nondeg : CRule where
  id := "integration.rubi_1_2_2_3_r7_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.var "q"))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "e") (.int (-1)))) (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "q", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .int (.var "p"),
    .ne (.var "d") (.int 0),
    .ne (.var "e") (.int 0)]
  priority := 9067
  description := "rubi_1_2_2_3_r7 with NeQ[d, 0]; NeQ[e, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:7" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#7"

/-- rubi_1_2_3_3_r19 with NeQ[Multiply[e, Add[Multiply[n, Add[q, 2]], 1]], 0] (numerically checked) -/
def rubi1233r19Nondeg : CRule where
  id := "integration.rubi_1_2_3_3_r19_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "n")))) (.var "q")) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))))) (.pow (.var "x") (.var "n"))))))]
  independent := ["a", "b", "c", "d", "e", "n", "q", "n2"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .ne (.app2 .mul (.var "e") (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "q") (.int 2))) (.int 1))) (.int 0)]
  priority := 9068
  description := "rubi_1_2_3_3_r19 with NeQ[Multiply[e, Add[Multiply[n, Add[q, 2]], 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p:19" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p.m#19"

/-- rubi_4_1_12_r44 with NeQ[Multiply[Power[b, 2], Power[n, 2], Power[p, 2]], 0]; NeQ[Multiply[b, n, p], 0]; NeQ[p, 0] (numerically checked) -/
def rubi4112r44Nondeg : CRule where
  id := "integration.rubi_4_1_12_r44_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:44"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "n") (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "n")) (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))) (.pow (.var "p") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)) (.int 0),
    .gt (.var "p") (.int 1),
    .ne (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int 0),
    .ne (.var "p") (.int 0)]
  priority := 9069
  description := "rubi_4_1_12_r44 with NeQ[Multiply[Power[b, 2], Power[n, 2], Power[p, 2]], 0]; NeQ[Multiply[b, n, p], 0]; NeQ[p, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:44" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#44"

/-- rubi_4_1_13_r1 with NeQ[Multiply[4, c], 0] (numerically checked) -/
def rubi4113r1Nondeg : CRule where
  id := "integration.rubi_4_1_13_r1_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:1"
  shape := .antiderivRec; x := "x"
  body := (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))
  result := (.var "I1")
  integrals := [("I1", (.app1 .sin (.app2 .mul (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "x"))) (.int 2)) (.pow (.app2 .mul (.int 4) (.var "c")) (.int (-1))))))]
  independent := ["a", "b", "c"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .ne (.app2 .mul (.int 4) (.var "c")) (.int 0)]
  priority := 9070
  description := "rubi_4_1_13_r1 with NeQ[Multiply[4, c], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:1" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#1"

/-- rubi_4_1_13_r15 with NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (numerically checked) -/
def rubi4113r15Nondeg : CRule where
  id := "integration.rubi_4_1_13_r15_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .gt (.int (-1)) (.var "m"),
    .ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int 0)]
  priority := 9071
  description := "rubi_4_1_13_r15 with NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:15" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#15"

/-- rubi_4_7_8_r14 with NeQ[Add[Multiply[Power[b, 2], Power[d, 2], e, Power[n, 2], Power[p, 2]], Multiply[e, Power[Add[m, 1], 2]]], 0] (numerically checked) -/
def rubi478r14Nondeg : CRule where
  id := "integration.rubi_4_7_8_r14_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .sin (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .cos (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 1),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.var "e") (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int 0)]
  priority := 9072
  description := "rubi_4_7_8_r14 with NeQ[Add[Multiply[Power[b, 2], Power[d, 2], e, Power[n, 2], Power[p, 2]], Multiply[e, Power[Add[m, 1], 2]]], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:14" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#14"

/-- rubi_4_7_9_r12 with NeQ[Power[b, 2], 0]; NeQ[b, 0] (numerically checked) -/
def rubi479r12Nondeg : CRule where
  id := "integration.rubi_4_7_9_r12_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "b") (.int (-1)))) (.var "I2"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I3")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))),
    ("I3", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 1),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.pow (.var "b") (.int 2)) (.int 0),
    .ne (.var "b") (.int 0)]
  priority := 9073
  description := "rubi_4_7_9_r12 with NeQ[Power[b, 2], 0]; NeQ[b, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:12" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#12"

/-- rubi_2_3_r32 with NeQ[d, 0] (numerically checked) -/
def rubi23r32Nondeg : CRule where
  id := "integration.rubi_2_3_r32_nondegenerate"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:32"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.var "e") (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))))
  result := (.app2 .mul (.pow (.var "F") (.app2 .add (.var "e") (.app2 .mul (.app2 .mul (.var "f") (.var "b")) (.pow (.var "d") (.int (-1)))))) (.var "I1"))
  integrals := [("I1", (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "h", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.var "d") (.int 0)]
  priority := 9074
  description := "rubi_2_3_r32 with NeQ[d, 0] (numerically checked)"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:32" "2 Exponentials/2.3 Miscellaneous exponentials.m#32"

/-- rubi_3_1_2_r6 with NeQ[Multiply[b, d, n, Add[p, 1]], 0]; NeQ[Multiply[b, n, Add[p, 1]], 0] (numerically checked) -/
def rubi312r6Nondeg : CRule where
  id := "integration.rubi_3_1_2_r6_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.ne (.var "m") (.int (-1)),
    .gt (.int (-1)) (.var "p"),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9075
  description := "rubi_3_1_2_r6 with NeQ[Multiply[b, d, n, Add[p, 1]], 0]; NeQ[Multiply[b, n, Add[p, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:6" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#6"

/-- rubi_3_1_4_r2 with NeQ[Multiply[d, f, Add[m, 1]], 0]; NeQ[Multiply[d, Add[m, 1]], 0] (numerically checked) -/
def rubi314r2Nondeg : CRule where
  id := "integration.rubi_3_1_4_r2_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q", "r"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "r") (.app2 .add (.var "q") (.int 1)))) (.int 1)) (.int 0),
    .ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0)]
  priority := 9076
  description := "rubi_3_1_4_r2 with NeQ[Multiply[d, f, Add[m, 1]], 0]; NeQ[Multiply[d, Add[m, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:2" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#2"

/-- rubi_3_1_5_r28 with NeQ[Multiply[g, Add[m, 1]], 0]; NeQ[Add[m, 1], 0] (numerically checked) -/
def rubi315r28Nondeg : CRule where
  id := "integration.rubi_3_1_5_r28_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:28"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "r")))))) (.var "q")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "r")))))) (.var "q"))) (.pow (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.var "q")) (.var "r")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "r")))))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .mul (.var "f") (.pow (.var "x") (.var "r")))))) (.var "q"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "r", "p", "q"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .int (.var "q"),
    .gt (.var "q") (.int 0),
    .ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.var "g") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .add (.var "m") (.int 1)) (.int 0)]
  priority := 9077
  description := "rubi_3_1_5_r28 with NeQ[Multiply[g, Add[m, 1]], 0]; NeQ[Add[m, 1], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:28" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#28"

/-- rubi_1_1_1_3_r13 with NeQ[Multiply[b, d, Add[p, Multiply[-1, 1]]], 0]; NeQ[Multiply[b, d], 0] (numerically checked) -/
def rubi1113r13Nondeg : CRule where
  id := "integration.rubi_1_1_1_3_r13_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "b") (.var "d")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.var "e") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.pow (.var "f") (.int 2)))) (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "d")) (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "f"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")) (.var "f")))) (.var "x"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "p"]
  conditions := [.gt (.var "p") (.int 1),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.int 0),
    .ne (.app2 .mul (.var "b") (.var "d")) (.int 0)]
  priority := 9078
  description := "rubi_1_1_1_3_r13 with NeQ[Multiply[b, d, Add[p, Multiply[-1, 1]]], 0]; NeQ[Multiply[b, d], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:13" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#13"

/-- rubi_1_1_3_5_r25 with NeQ[b, 0] (numerically checked) -/
def rubi1135r25Nondeg : CRule where
  id := "integration.rubi_1_1_3_5_r25_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "r", "q"]
  conditions := [.gt (.var "q") (.int 1),
    .ne (.var "b") (.int 0)]
  priority := 9080
  description := "rubi_1_1_3_5_r25 with NeQ[b, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:25" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#25"

/-- rubi_1_2_1_2_r44 with NeQ[Multiply[c, Add[m, Multiply[2, p], 1]], 0] (numerically checked) -/
def rubi1212r44Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r44_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:44"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "c", "d", "e", "p", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 1),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0),
    .int (.app2 .mul (.int 2) (.var "p")),
    .ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int 0)]
  priority := 9081
  description := "rubi_1_2_1_2_r44 with NeQ[Multiply[c, Add[m, Multiply[2, p], 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:44" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#44"

/-- rubi_1_2_1_6_r10 with NeQ[e, 0]; NeQ[f, 0] (numerically checked) -/
def rubi1216r10Nondeg : CRule where
  id := "integration.rubi_1_2_1_6_r10_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "x")) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "q")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "f") (.int (-1)))) (.var "x"))) (.var "p")) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "x")) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.var "q")))))]
  independent := ["a", "c", "e", "f", "q", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "c") (.pow (.var "e") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "f") (.int 2)))) (.int 0),
    .int (.var "p"),
    .ne (.var "e") (.int 0),
    .ne (.var "f") (.int 0)]
  priority := 9082
  description := "rubi_1_2_1_6_r10 with NeQ[e, 0]; NeQ[f, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:10" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#10"

/-- rubi_1_2_2_4_r56 with NeQ[Power[d, 2], 0]; NeQ[Multiply[Power[d, 2], Power[f, 4]], 0] (numerically checked) -/
def rubi1224r56Nondeg : CRule where
  id := "integration.rubi_1_2_2_4_r56_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:56"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.pow (.pow (.var "d") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.pow (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 4))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 4))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "c", "d", "e", "f", "m", "p"]
  conditions := [.gt (.var "p") (.int 0),
    .gt (.int (-2)) (.var "m"),
    .ne (.pow (.var "d") (.int 2)) (.int 0),
    .ne (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 4))) (.int 0)]
  priority := 9083
  description := "rubi_1_2_2_4_r56 with NeQ[Power[d, 2], 0]; NeQ[Multiply[Power[d, 2], Power[f, 4]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:56" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#56"

/-- rubi_4_1_12_r33 with NeQ[Multiply[d, n], 0] (numerically checked) -/
def rubi4112r33Nondeg : CRule where
  id := "integration.rubi_4_1_12_r33_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "e") (.var "n")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.app2 .add (.var "m") (.int 1)) (.var "n"),
    .ne (.app2 .mul (.var "d") (.var "n")) (.int 0)]
  priority := 9084
  description := "rubi_4_1_12_r33 with NeQ[Multiply[d, n], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:33" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#33"

/-- rubi_4_1_13_r20 with NeQ[Multiply[2, c], 0] (numerically checked) -/
def rubi4113r20Nondeg : CRule where
  id := "integration.rubi_4_1_13_r20_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d")))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0),
    .gt (.var "m") (.int 1),
    .ne (.app2 .mul (.int 2) (.var "c")) (.int 0)]
  priority := 9085
  description := "rubi_4_1_13_r20 with NeQ[Multiply[2, c], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:20" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#20"

/-- rubi_4_7_9_r1 with NeQ[b, 0] (numerically checked) -/
def rubi479r1Nondeg : CRule where
  id := "integration.rubi_4_7_9_r1_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .ne (.var "b") (.int 0)]
  priority := 9086
  description := "rubi_4_7_9_r1 with NeQ[b, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:1" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#1"

/-- rubi_4_7_9_r30 with NeQ[a, 0] (numerically checked) -/
def rubi479r30Nondeg : CRule where
  id := "integration.rubi_4_7_9_r30_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "a") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0),
    .ne (.var "a") (.int 0)]
  priority := 9087
  description := "rubi_4_7_9_r30 with NeQ[a, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:30" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#30"

/-- rubi_2_3_r33 with NeQ[d, 0] (numerically checked) -/
def rubi23r33Nondeg : CRule where
  id := "integration.rubi_2_3_r33_nondegenerate"; legacyId := some "rubi:2 Exponentials/2.3 Miscellaneous exponentials:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.var "e") (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "g") (.app2 .mul (.var "h") (.var "x"))) (.var "m")) (.pow (.var "F") (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.var "b") (.var "f"))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "h", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "d") (.var "g")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "h"))) (.int 0),
    .ne (.var "d") (.int 0)]
  priority := 9088
  description := "rubi_2_3_r33 with NeQ[d, 0] (numerically checked)"
  provenance := migrated "rubi:2 Exponentials/2.3 Miscellaneous exponentials:33" "2 Exponentials/2.3 Miscellaneous exponentials.m#33"

/-- rubi_3_1_3_r1 with NeQ[d, 0] (numerically checked) -/
def rubi313r1Nondeg : CRule where
  id := "integration.rubi_3_1_3_r1_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.pow (.var "d") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1))))]
  independent := ["a", "b", "c", "d", "e", "n", "q", "r"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "r") (.app2 .add (.var "q") (.int 1))) (.int 1)) (.int 0),
    .ne (.var "d") (.int 0)]
  priority := 9089
  description := "rubi_3_1_3_r1 with NeQ[d, 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:1" "3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p.m#1"

/-- rubi_3_1_5_r3 with NeQ[Multiply[d, f, Add[m, 1]], 0]; NeQ[Multiply[d, Add[m, 1]], 0] (numerically checked) -/
def rubi315r3Nondeg : CRule where
  id := "integration.rubi_3_1_5_r3_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "q", "r"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.var "r") (.app2 .add (.var "q") (.int 1)))) (.int 1)) (.int 0),
    .ne (.var "m") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0)]
  priority := 9090
  description := "rubi_3_1_5_r3 with NeQ[Multiply[d, f, Add[m, 1]], 0]; NeQ[Multiply[d, Add[m, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:3" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#3"

/-- rubi_1_1_1_3_r14 with NeQ[Multiply[Add[p, 1], Add[Multiply[b, e], Multiply[-1, a, f]], Add[Multiply[d, e], Multiply[-1, c, f]]], 0]; NeQ[Multiply[Add[Multiply[b, e], Multiply[-1, a, f]], Add[Multiply[d, e], Multiply[-1, c, f]]], 0] (numerically checked) -/
def rubi1113r14Nondeg : CRule where
  id := "integration.rubi_1_1_1_3_r14_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "f"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")) (.var "f"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "f")) (.var "x"))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "p"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .ne (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.int 1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.int 0),
    .ne (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.int 0)]
  priority := 9091
  description := "rubi_1_1_1_3_r14 with NeQ[Multiply[Add[p, 1], Add[Multiply[b, e], Multiply[-1, a, f]], Add[Multiply[d, e], Multiply[-1, c, f]]], 0]; NeQ[Multiply[Add[Multiply[b, e], Multiply[-1, a, f]], Add[Multiply[d, e], Multiply[-1, c, f]]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:14" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#14"

/-- rubi_1_1_3_5_r26 with NeQ[Power[Add[Multiply[b, c], Multiply[-1, a, d]], 2], 0] (numerically checked) -/
def rubi1135r26Nondeg : CRule where
  id := "integration.rubi_1_1_3_5_r26_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:26"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 2))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r"))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "r", "q"]
  conditions := [.gt (.int (-1)) (.var "q"),
    .ne (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.int 0)]
  priority := 9092
  description := "rubi_1_1_3_5_r26 with NeQ[Power[Add[Multiply[b, c], Multiply[-1, a, d]], 2], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:26" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#26"

/-- rubi_1_2_1_2_r12 with NeQ[Multiply[2, a, c, Add[p, 1]], 0]; NeQ[Multiply[2, a, Add[p, 1]], 0] (numerically checked) -/
def rubi1212r12Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r12_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.var "x"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "c", "d", "e", "p"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .ne (.var "p") (.app2 .mul (.int (-3)) (.pow (.int 2) (.int (-1)))),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9093
  description := "rubi_1_2_1_2_r12 with NeQ[Multiply[2, a, c, Add[p, 1]], 0]; NeQ[Multiply[2, a, Add[p, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:12" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#12"

/-- rubi_1_2_1_2_r45 with NeQ[Multiply[Add[m, p, 1], Add[Multiply[2, c, d], Multiply[-1, b, e]]], 0] (numerically checked) -/
def rubi1212r45Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r45_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:45"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 2))) (.pow (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "p", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.int 0) (.var "m"),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0),
    .int (.app2 .mul (.int 2) (.var "p")),
    .ne (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.int 0)]
  priority := 9094
  description := "rubi_1_2_1_2_r45 with NeQ[Multiply[Add[m, p, 1], Add[Multiply[2, c, d], Multiply[-1, b, e]]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:45" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#45"

/-- rubi_1_2_2_1_r5 with NeQ[Multiply[2, a, Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (numerically checked) -/
def rubi1221r5Nondeg : CRule where
  id := "integration.rubi_1_2_2_1_r5_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.1 (a+b x^2+c x^4)^p:5"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.app2 .add (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c"))) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c"))) (.app2 .mul (.app2 .mul (.int 2) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.app2 .mul (.int 4) (.var "p")) (.int 7))) (.pow (.var "x") (.int 2)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .int (.app2 .mul (.int 2) (.var "p")),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)]
  priority := 9095
  description := "rubi_1_2_2_1_r5 with NeQ[Multiply[2, a, Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.1 (a+b x^2+c x^4)^p:5" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.1 (a+b x^2+c x^4)^p.m#5"

/-- rubi_1_2_2_4_r57 with NeQ[Multiply[d, e], 0]; NeQ[Multiply[d, e, Power[f, 2]], 0] (numerically checked) -/
def rubi1224r57Nondeg : CRule where
  id := "integration.rubi_1_2_2_4_r57_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:57"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "d") (.var "e")) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.pow (.var "f") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.app2 .mul (.var "a") (.var "e")) (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.var "p") (.int 0),
    .gt (.int 0) (.var "m"),
    .ne (.app2 .mul (.var "d") (.var "e")) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "d") (.var "e")) (.pow (.var "f") (.int 2))) (.int 0)]
  priority := 9096
  description := "rubi_1_2_2_4_r57 with NeQ[Multiply[d, e], 0]; NeQ[Multiply[d, e, Power[f, 2]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:57" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#57"

/-- rubi_4_1_12_r34 with NeQ[Multiply[d, n], 0] (numerically checked) -/
def rubi4112r34Nondeg : CRule where
  id := "integration.rubi_4_1_12_r34_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:34"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "e") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.var "n"))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.app2 .add (.var "m") (.int 1)) (.var "n"),
    .ne (.app2 .mul (.var "d") (.var "n")) (.int 0)]
  priority := 9097
  description := "rubi_4_1_12_r34 with NeQ[Multiply[d, n], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p:34" "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m#34"

/-- rubi_4_1_13_r13 with NeQ[Multiply[2, c], 0] (numerically checked) -/
def rubi4113r13Nondeg : CRule where
  id := "integration.rubi_4_1_13_r13_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e"))) (.int 0),
    .gt (.var "m") (.int 1),
    .ne (.app2 .mul (.int 2) (.var "c")) (.int 0)]
  priority := 9098
  description := "rubi_4_1_13_r13 with NeQ[Multiply[2, c], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:13" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#13"

/-- rubi_4_1_13_r21 with NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (numerically checked) -/
def rubi4113r21Nondeg : CRule where
  id := "integration.rubi_4_1_13_r21_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:21"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d")))) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0),
    .gt (.int (-1)) (.var "m"),
    .ne (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int 0)]
  priority := 9099
  description := "rubi_4_1_13_r21 with NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:21" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#21"

/-- rubi_4_7_9_r2 with NeQ[b, 0] (numerically checked) -/
def rubi479r2Nondeg : CRule where
  id := "integration.rubi_4_7_9_r2_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .ne (.var "b") (.int 0)]
  priority := 9100
  description := "rubi_4_7_9_r2 with NeQ[b, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:2" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#2"

/-- rubi_3_1_2_r5 with NeQ[Multiply[d, Add[m, 1]], 0]; NeQ[Add[m, 1], 0] (numerically checked) -/
def rubi312r5Nondeg : CRule where
  id := "integration.rubi_3_1_2_r5_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.ne (.var "m") (.int (-1)),
    .gt (.var "p") (.int 0),
    .ne (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int 0),
    .ne (.app2 .add (.var "m") (.int 1)) (.int 0)]
  priority := 9102
  description := "rubi_3_1_2_r5 with NeQ[Multiply[d, Add[m, 1]], 0]; NeQ[Add[m, 1], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p:5" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#5"

/-- rubi_3_1_3_r10 with NeQ[Multiply[2, d, Add[q, 1]], 0] (numerically checked) -/
def rubi313r10Nondeg : CRule where
  id := "integration.rubi_3_1_3_r10_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 3)) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))]
  independent := ["a", "b", "c", "d", "e", "n", "q"]
  conditions := [.gt (.int (-1)) (.var "q"),
    .ne (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int 0)]
  priority := 9103
  description := "rubi_3_1_3_r10 with NeQ[Multiply[2, d, Add[q, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p:10" "3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p.m#10"

/-- rubi_3_1_4_r18 with NeQ[d, 0] (numerically checked) -/
def rubi314r18Nondeg : CRule where
  id := "integration.rubi_3_1_4_r18_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "r", "p", "q"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .int (.var "q"),
    .gt (.int (-1)) (.var "q"),
    .ne (.var "d") (.int 0)]
  priority := 9104
  description := "rubi_3_1_4_r18 with NeQ[d, 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p:18" "3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m#18"

/-- rubi_3_1_5_r17 with NeQ[d, 0] (numerically checked) -/
def rubi315r17Nondeg : CRule where
  id := "integration.rubi_3_1_5_r17_nondegenerate"; legacyId := some "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.var "r")))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "r", "p", "q"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .int (.var "q"),
    .gt (.int (-1)) (.var "q"),
    .ne (.var "d") (.int 0)]
  priority := 9105
  description := "rubi_3_1_5_r17 with NeQ[d, 0] (numerically checked)"
  provenance := migrated "rubi:3 Logarithms/3.1.5 u (a+b log(c x^n))^p:17" "3 Logarithms/3.1.5 u (a+b log(c x^n))^p.m#17"

/-- rubi_1_1_1_3_r12 with NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0] (numerically checked) -/
def rubi1113r12Nondeg : CRule where
  id := "integration.rubi_1_1_1_3_r12_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "p")) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f"))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f")))) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "p"]
  conditions := [.gt (.var "p") (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 9107
  description := "rubi_1_1_1_3_r12 with NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p:12" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p.m#12"

/-- rubi_1_1_3_3_r16 with NeQ[Multiply[b1, b2, Add[Multiply[n, Add[p, 1]], 1]], 0] (numerically checked) -/
def rubi1133r16Nondeg : CRule where
  id := "integration.rubi_1_1_3_3_r16_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.var "non2")))) (.var "p")) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.var "non2")))) (.var "p"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b1") (.var "b2")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "a1") (.var "a2")) (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b1")) (.var "b2")) (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b1") (.var "b2")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a1") (.app2 .mul (.var "b1") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.var "p")) (.pow (.app2 .add (.var "a2") (.app2 .mul (.var "b2") (.pow (.var "x") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1))))))) (.var "p"))))]
  independent := ["a1", "b1", "a2", "b2", "c", "d", "n", "p", "non2"]
  conditions := [.eq (.var "non2") (.app2 .mul (.var "n") (.pow (.int 2) (.int (-1)))),
    .eq (.app2 .add (.app2 .mul (.var "a2") (.var "b1")) (.app2 .mul (.var "a1") (.var "b2"))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1)) (.int 0),
    .ne (.app2 .mul (.app2 .mul (.var "b1") (.var "b2")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.int 1))) (.int 0)]
  priority := 9108
  description := "rubi_1_1_3_3_r16 with NeQ[Multiply[b1, b2, Add[Multiply[n, Add[p, 1]], 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q:16" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.3 (a+b x^n)^p (c+d x^n)^q.m#16"

/-- rubi_1_1_3_5_r24 with NeQ[Power[Add[Multiply[b, c], Multiply[-1, a, d]], 2], 0] (numerically checked) -/
def rubi1135r24Nondeg : CRule where
  id := "integration.rubi_1_1_3_5_r24_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "r"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.pow (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 2))) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "r") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.var "d")) (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "d") (.int 2))) (.var "e"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "c") (.int 2))) (.var "f"))) (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "f")))) (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "q", "r"]
  conditions := [.gt (.int (-1)) (.var "q"),
    .gt (.var "r") (.int 1),
    .ne (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.int 0)]
  priority := 9109
  description := "rubi_1_1_3_5_r24 with NeQ[Power[Add[Multiply[b, c], Multiply[-1, a, d]], 2], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r:24" "1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r.m#24"

/-- rubi_1_2_1_2_r43 with NeQ[Multiply[c, Add[m, Multiply[2, p], 1]], 0] (numerically checked) -/
def rubi1212r43Nondeg : CRule where
  id := "integration.rubi_1_2_1_2_r43_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:43"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.var "m") (.var "p")) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")))) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "p", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 1),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0),
    .int (.app2 .mul (.int 2) (.var "p")),
    .ne (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int 0)]
  priority := 9110
  description := "rubi_1_2_1_2_r43 with NeQ[Multiply[c, Add[m, Multiply[2, p], 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:43" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#43"

/-- rubi_1_2_1_3_r16 with NeQ[Multiply[2, a, c, Add[p, 1]], 0] (numerically checked) -/
def rubi1213r16Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r16_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.var "e") (.var "f")) (.app2 .mul (.var "d") (.var "g")))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.var "f")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e")) (.var "g")))) (.var "x"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.var "g")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d")) (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))))]
  independent := ["a", "c", "d", "e", "f", "g", "p"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int 0)]
  priority := 9111
  description := "rubi_1_2_1_3_r16 with NeQ[Multiply[2, a, c, Add[p, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:16" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#16"

/-- rubi_1_2_1_3_r36 with NeQ[f, 0]; NeQ[g, 0] (numerically checked) -/
def rubi1213r36Nondeg : CRule where
  id := "integration.rubi_1_2_1_3_r36_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:36"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "f") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "g") (.int (-1)))) (.var "x"))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "f") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "g"))) (.app2 .mul (.var "a") (.pow (.var "g") (.int 2)))) (.int 0),
    .int (.var "p"),
    .ne (.var "f") (.int 0),
    .ne (.var "g") (.int 0)]
  priority := 9112
  description := "rubi_1_2_1_3_r36 with NeQ[f, 0]; NeQ[g, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p:36" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p.m#36"

/-- rubi_1_2_1_6_r9 with NeQ[e, 0]; NeQ[f, 0] (numerically checked) -/
def rubi1216r9Nondeg : CRule where
  id := "integration.rubi_1_2_1_6_r9_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "p")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "x")) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.var "q")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.var "c") (.pow (.var "f") (.int (-1)))) (.var "x"))) (.var "p")) (.pow (.app2 .add (.app2 .mul (.var "e") (.var "x")) (.app2 .mul (.var "f") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.var "q")))))]
  independent := ["a", "b", "c", "e", "f", "q", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "e") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "e")) (.var "f"))) (.app2 .mul (.var "a") (.pow (.var "f") (.int 2)))) (.int 0),
    .int (.var "p"),
    .ne (.var "e") (.int 0),
    .ne (.var "f") (.int 0)]
  priority := 9113
  description := "rubi_1_2_1_6_r9 with NeQ[e, 0]; NeQ[f, 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q:9" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q.m#9"

/-- rubi_1_2_2_4_r55 with NeQ[Power[d, 2], 0]; NeQ[Multiply[Power[d, 2], Power[f, 4]], 0] (numerically checked) -/
def rubi1224r55Nondeg : CRule where
  id := "integration.rubi_1_2_2_4_r55_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:55"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "d") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "e"))) (.app2 .mul (.var "a") (.pow (.var "e") (.int 2)))) (.pow (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 4))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.app2 .mul (.var "a") (.var "d")) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 4))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .gt (.var "p") (.int 0),
    .gt (.int (-2)) (.var "m"),
    .ne (.pow (.var "d") (.int 2)) (.int 0),
    .ne (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "f") (.int 4))) (.int 0)]
  priority := 9114
  description := "rubi_1_2_2_4_r55 with NeQ[Power[d, 2], 0]; NeQ[Multiply[Power[d, 2], Power[f, 4]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p:55" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p.m#55"

/-- rubi_1_2_3_1_r5 with NeQ[Multiply[a, n, Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (numerically checked) -/
def rubi1231r5Nondeg : CRule where
  id := "integration.rubi_1_2_3_1_r5_nondegenerate"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p:5"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.var "n2")))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.app2 .add (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c"))) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.pow (.var "x") (.var "n"))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c"))) (.app2 .mul (.app2 .mul (.var "n") (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.app2 .mul (.var "n") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3))) (.int 1))) (.pow (.var "x") (.var "n")))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .mul (.var "c") (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "p"),
    .gt (.int (-1)) (.var "p"),
    .ne (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c")))) (.int 0)]
  priority := 9115
  description := "rubi_1_2_3_1_r5 with NeQ[Multiply[a, n, Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (numerically checked)"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p:5" "1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p.m#5"

/-- rubi_4_1_13_r19 with NeQ[Multiply[2, c], 0] (numerically checked) -/
def rubi4113r19Nondeg : CRule where
  id := "integration.rubi_4_1_13_r19_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d")))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .sin (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app1 .cos (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0),
    .gt (.var "m") (.int 1),
    .ne (.app2 .mul (.int 2) (.var "c")) (.int 0)]
  priority := 9117
  description := "rubi_4_1_13_r19 with NeQ[Multiply[2, c], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n:19" "4 Trig functions/4.1 Sine/4.1.13 (d+e x)^m sin(a+b x+c x^2)^n.m#19"

/-- rubi_4_7_6_r17 with NeQ[Multiply[b, d, Add[n, 1]], 0] (numerically checked) -/
def rubi476r17Nondeg : CRule where
  id := "integration.rubi_4_7_6_r17_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1)),
    .ne (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int 0)]
  priority := 9118
  description := "rubi_4_7_6_r17 with NeQ[Multiply[b, d, Add[n, 1]], 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p:17" "4 Trig functions/4.7 Miscellaneous/4.7.6 (c+d x)^m trig(a+b x)^n trig(a+b x)^p.m#17"

/-- rubi_4_7_8_r48 with NeQ[Multiply[a, n], 0]; NeQ[n, 0] (numerically checked) -/
def rubi478r48Nondeg : CRule where
  id := "integration.rubi_4_7_8_r48_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:48"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .cos (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))
  result := (.app2 .add (.app2 .mul (.app1 .sin (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app2 .mul (.var "a") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.var "n") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.app1 .cos (.app2 .mul (.app2 .mul (.var "a") (.pow (.var "x") (.var "n"))) (.app1 .ln (.app2 .mul (.var "b") (.var "x")))))))]
  independent := ["a", "b", "m", "n"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.app2 .mul (.var "a") (.var "n")) (.int 0),
    .ne (.var "n") (.int 0)]
  priority := 9119
  description := "rubi_4_7_8_r48 with NeQ[Multiply[a, n], 0]; NeQ[n, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p:48" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#48"

/-- rubi_4_7_9_r27 with NeQ[b, 0] (numerically checked) -/
def rubi479r27Nondeg : CRule where
  id := "integration.rubi_4_7_9_r27_nondegenerate"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p"))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0),
    .ne (.var "b") (.int 0)]
  priority := 9120
  description := "rubi_4_7_9_r27 with NeQ[b, 0] (numerically checked)"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions:27" "4 Trig functions/4.7 Miscellaneous/4.7.9 Active trig functions.m#27"


/-! ## Catalogue entries -/

/-- The strengthened variants checked numerically, unproved in both domains. -/
def entries : List CEntry := [
  { rule := rubi314r17Nondeg, ruleDecl := ``rubi314r17Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_4_r17, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 78 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; LtQ[q, -1]; IntegerQ[Multiply[2, q]]",
      optionalFinding "e., a., b., c., n. and p."] },
  { rule := rubi315r16Nondeg, ruleDecl := ``rubi315r16Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r16, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 141 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; LtQ[q, -1]; IntegerQ[Multiply[2, q]]",
      optionalFinding "e., a., b., c., n. and p."] },
  { rule := rubi33r22Nondeg, ruleDecl := ``rubi33r22Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[g, r, Add[q, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_3_r22, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 52 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[m, Add[r, Multiply[-1, 1]]]; NeQ[q, -1]; IGtQ[p, 0]",
      optionalFinding "m., f., g., r., q., a., b., c., e., n. and p."] },
  { rule := rubi478r47Nondeg, ruleDecl := ``rubi478r47Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[a, n], 0]; NeQ[n, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_8_r47, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 185 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "EqQ[m, Add[n, Multiply[-1, 1]]]",
      optionalFinding "m., a., n. and b."] },
  { rule := rubi312r3Nondeg, ruleDecl := ``rubi312r3Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[d, Add[m, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_2_r3, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 553 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "NeQ[m, -1]; EqQ[Add[Multiply[a, Add[m, 1]], Multiply[-1, b, n]], 0]",
      optionalFinding "d., m., a., b., c. and n."] },
  { rule := rubi313r7Nondeg, ruleDecl := ``rubi313r7Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[b, n, Add[p, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_3_r7, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 58 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]; GtQ[q, 0]",
      optionalFinding "e., q., a., b., c. and n."] },
  { rule := rubi314r13Nondeg, ruleDecl := ``rubi314r13Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[2, d, f, Add[q, 1]], 0]; NeQ[Multiply[2, d, Add[q, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_4_r13, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 90 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "ILtQ[q, -1]; ILtQ[m, 0]",
      optionalFinding "f., m., e., q., a., b., c. and n."] },
  { rule := rubi35r21Nondeg, ruleDecl := ``rubi35r21Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[b, n, q, Add[p, 1]], 0]; NeQ[Multiply[b, n, q], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_5_r21, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 86 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "EqQ[r, Add[q, Multiply[-1, 1]]]; NeQ[p, -1]; NeQ[Add[Multiply[a, e, m], Multiply[-1, b, d, n, q]], 0]",
      optionalFinding "d., m., e., c., n., r., a., b. and p."] },
  { rule := rubi1213r33Nondeg, ruleDecl := ``rubi1213r33Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[c, Add[m, Multiply[2, p], 2]], 0]; NeQ[Multiply[e, Add[m, Multiply[2, p], 2]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_1_3_r33, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 854 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "EqQ[Add[Multiply[c, Power[d, 2]], Multiply[a, Power[e, 2]]], 0]; NeQ[Add[m, Multiply[2, p], 2], 0]; NeQ[m, 2]",
      optionalFinding "e., f., g. and c."] },
  { rule := logPowOverSqNondeg, ruleDecl := ``logPowOverSqNondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.log_power_over_linear_square, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 761 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "GtQ[p, 0]",
      optionalFinding "a., b., c., n., p. and e."] },
  { rule := rubi314r12Nondeg, ruleDecl := ``rubi314r12Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[e, Add[q, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_4_r12, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 172 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "ILtQ[q, -1]; GtQ[m, 0]",
      optionalFinding "f., m., e., q., a., b., c. and n."] },
  { rule := rubi315r13Nondeg, ruleDecl := ``rubi315r13Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r13, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 883 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]",
      optionalFinding "a., b., c., n., p. and e."] },
  { rule := linFourNondeg, ruleDecl := ``linFourNondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[Power[b, 2], Power[d, 2], Add[m, n, 2], Add[m, n, 3]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.two_linear_factors_times_powers, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 4109 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "NeQ[Add[m, n, 2], 0]; NeQ[Add[m, n, 3], 0]",
      optionalFinding "a., b., m., c., d., n., f., g. and h."] },
  { rule := rubi1134r25Nondeg, ruleDecl := ``rubi1134r25Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[b1, b2, e, Add[m, Multiply[n, Add[p, 1]], 1]], 0]; NeQ[Multiply[b1, b2, Add[m, Multiply[n, Add[p, 1]], 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_4_r25, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 98 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: non2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[non2, Multiply[n, Power[2, -1]]]; EqQ[Add[Multiply[a2, b1], Multiply[a1, b2]], 0]; NeQ[Add[m, Multiply[n, Add[p, 1]], 1], 0]",
      optionalFinding "e., m., b1., non2., p., b2. and d."] },
  { rule := rubi4113r2Nondeg, ruleDecl := ``rubi4113r2Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[4, c], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r2, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 1288 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]",
      optionalFinding "a., b. and c."] },
  { rule := rubi4113r16Nondeg, ruleDecl := ``rubi4113r16Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r16, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 469 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi479r16Nondeg, ruleDecl := ``rubi479r16Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[a, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r16, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 861 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]",
      optionalFinding "e., f., m., c., d., n. and b."] },
  { rule := rubi21r9Nondeg, ruleDecl := ``rubi21r9Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[a, d, Add[m, 1]], 0]; NeQ[a, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_2_1_r9, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 714 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]",
      optionalFinding "c., d., m., b., g., e., f. and n."] },
  { rule := rubi314r9Nondeg, ruleDecl := ``rubi314r9Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_4_r9, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 52 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; IGtQ[r, 0]; ILtQ[m, -1]",
      optionalFinding "m., a., b., c., n., p., e. and r."] },
  { rule := rubi315r8Nondeg, ruleDecl := ``rubi315r8Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[e, Add[q, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r8, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 205 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "ILtQ[q, -1]; GtQ[m, 0]",
      optionalFinding "f., m., e., q., a., b., c. and n."] },
  { rule := rubi321r1Nondeg, ruleDecl := ``rubi321r1Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[b, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_2_1_r1, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 613 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; IGtQ[p, 0]",
      optionalFinding "A., B., e., a., b., c., d., n. and p."] },
  { rule := rubi35r16Nondeg, ruleDecl := ``rubi35r16Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[b, n, q, Add[p, 1]], 0]; NeQ[Multiply[b, n, q], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_5_r16, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 82 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "EqQ[r, Add[q, Multiply[-1, 1]]]; NeQ[p, -1]",
      optionalFinding "c., n., r., a., m., b. and p."] },
  { rule := rubi4112r43Nondeg, ruleDecl := ``rubi4112r43Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[Power[b, 2], Power[n, 2], Power[p, 2]], 0]; NeQ[Multiply[b, n, p], 0]; NeQ[p, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_12_r43, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 56 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[m, Multiply[-1, 2, n], 1], 0]; GtQ[p, 1]",
      optionalFinding "m., a. and b."] },
  { rule := rubi4113r14Nondeg, ruleDecl := ``rubi4113r14Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, c], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r14, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 504 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r22Nondeg, ruleDecl := ``rubi4113r22Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r22, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 987 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi478r13Nondeg, ruleDecl := ``rubi478r13Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Add[Multiply[Power[b, 2], Power[d, 2], e, Power[n, 2], Power[p, 2]], Multiply[e, Power[Add[m, 1], 2]]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_8_r13, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 411 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 1]; NeQ[Add[Multiply[Power[b, 2], Power[d, 2], Power[n, 2], Power[p, 2]], Power[Add[m, 1], 2]], 0]",
      optionalFinding "e., m., d., a., b., c. and n."] },
  { rule := rubi479r11Nondeg, ruleDecl := ``rubi479r11Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Power[b, 2], 0]; NeQ[b, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r11, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 315 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 1]; NeQ[Add[Power[a, 2], Multiply[-1, Power[b, 2]]], 0]; IGtQ[m, 0]",
      optionalFinding "e., f., m., c., d. and b."] },
  { rule := rubi21r10Nondeg, ruleDecl := ``rubi21r10Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[a, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_2_1_r10, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 441 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "ILtQ[p, 0]; IGtQ[m, 0]",
      optionalFinding "c., d., m., b., g., e., f. and n."] },
  { rule := rubi311r3Nondeg, ruleDecl := ``rubi311r3Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[b, n, Add[p, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_1_r3, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 265 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[p, -1]; IntegerQ[Multiply[2, p]]",
      optionalFinding "a., b., c. and n."] },
  { rule := rubi315r9Nondeg, ruleDecl := ``rubi315r9Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[2, d, f, Add[q, 1]], 0]; NeQ[Multiply[2, d, Add[q, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r9, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 119 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "ILtQ[q, -1]; ILtQ[m, 0]",
      optionalFinding "f., m., e., q., a., b., c. and n."] },
  { rule := rubi34r2Nondeg, ruleDecl := ``rubi34r2Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_4_r2, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 785 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[q, 0]",
      optionalFinding "a., b., c., e. and p."] },
  { rule := rubi1114r3Nondeg, ruleDecl := ``rubi1114r3Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[b, d, Power[Add[Multiply[b, c], Multiply[-1, a, d]], 2], Add[m, 1], Add[n, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_1_4_r3, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 133 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "LtQ[m, -1]; LtQ[n, -1]",
      optionalFinding "a., b., c., d., f., g. and h."] },
  { rule := rubi4112r44Nondeg, ruleDecl := ``rubi4112r44Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[Power[b, 2], Power[n, 2], Power[p, 2]], 0]; NeQ[Multiply[b, n, p], 0]; NeQ[p, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_12_r44, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 56 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[m, Multiply[-1, 2, n], 1], 0]; GtQ[p, 1]",
      optionalFinding "m., a. and b."] },
  { rule := rubi4113r1Nondeg, ruleDecl := ``rubi4113r1Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[4, c], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r1, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 1400 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "EqQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]",
      optionalFinding "a., b. and c."] },
  { rule := rubi4113r15Nondeg, ruleDecl := ``rubi4113r15Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r15, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 511 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi478r14Nondeg, ruleDecl := ``rubi478r14Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Add[Multiply[Power[b, 2], Power[d, 2], e, Power[n, 2], Power[p, 2]], Multiply[e, Power[Add[m, 1], 2]]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_8_r14, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 478 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "IGtQ[p, 1]; NeQ[Add[Multiply[Power[b, 2], Power[d, 2], Power[n, 2], Power[p, 2]], Power[Add[m, 1], 2]], 0]",
      optionalFinding "e., m., d., a., b., c. and n."] },
  { rule := rubi479r12Nondeg, ruleDecl := ``rubi479r12Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Power[b, 2], 0]; NeQ[b, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r12, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 378 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 1]; NeQ[Add[Power[a, 2], Multiply[-1, Power[b, 2]]], 0]; IGtQ[m, 0]",
      optionalFinding "e., f., m., c., d. and b."] },
  { rule := rubi23r32Nondeg, ruleDecl := ``rubi23r32Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_2_3_r32, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 1827 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "EqQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]",
      optionalFinding "g., h., m., e., f., a., b., c. and d."] },
  { rule := rubi312r6Nondeg, ruleDecl := ``rubi312r6Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[b, d, n, Add[p, 1]], 0]; NeQ[Multiply[b, n, Add[p, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_2_r6, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 160 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[m, -1]; LtQ[p, -1]",
      optionalFinding "d., m., a., b., c. and n."] },
  { rule := rubi314r2Nondeg, ruleDecl := ``rubi314r2Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[d, f, Add[m, 1]], 0]; NeQ[Multiply[d, Add[m, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_4_r2, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 66 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "EqQ[Add[m, Multiply[r, Add[q, 1]], 1], 0]; NeQ[m, -1]",
      optionalFinding "f., m., e., r., a., b., c. and n."] },
  { rule := rubi315r28Nondeg, ruleDecl := ``rubi315r28Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[g, Add[m, 1]], 0]; NeQ[Add[m, 1], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r28, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 61 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; IGtQ[q, 0]; NeQ[m, -1]",
      optionalFinding "g., m., a., b., c., n., p., d., e., f., r. and q."] },
  { rule := rubi4112r33Nondeg, ruleDecl := ``rubi4112r33Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[d, n], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_12_r33, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 497 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 0]; LtQ[n, Add[m, 1]]",
      optionalFinding "e., m., c. and d."] },
  { rule := rubi4113r20Nondeg, ruleDecl := ``rubi4113r20Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, c], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r20, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 1365 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi479r30Nondeg, ruleDecl := ``rubi479r30Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[a, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r30, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 182 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]; IGtQ[p, 0]",
      optionalFinding "e., f., m., c., d., p., n. and b."] },
  { rule := rubi23r33Nondeg, ruleDecl := ``rubi23r33Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_2_3_r33, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 469 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, c], Multiply[-1, a, d]], 0]; EqQ[Add[Multiply[d, g], Multiply[-1, c, h]], 0]",
      optionalFinding "g., h., m., e., f., a., b., c. and d."] },
  { rule := rubi313r1Nondeg, ruleDecl := ``rubi313r1Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_3_r1, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 126 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "EqQ[Add[Multiply[r, Add[q, 1]], 1], 0]",
      optionalFinding "e., r., a., b., c. and n."] },
  { rule := rubi315r3Nondeg, ruleDecl := ``rubi315r3Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[d, f, Add[m, 1]], 0]; NeQ[Multiply[d, Add[m, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r3, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 59 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "EqQ[Add[m, Multiply[r, Add[q, 1]], 1], 0]; NeQ[m, -1]",
      optionalFinding "f., m., e., r., a., b., c. and n."] },
  { rule := rubi4112r34Nondeg, ruleDecl := ``rubi4112r34Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[d, n], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_12_r34, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 511 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m, n are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[n, 0]; LtQ[n, Add[m, 1]]",
      optionalFinding "e., m., c. and d."] },
  { rule := rubi4113r13Nondeg, ruleDecl := ``rubi4113r13Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, c], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r13, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 511 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[Add[Multiply[2, c, d], Multiply[-1, b, e]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi4113r21Nondeg, ruleDecl := ``rubi4113r21Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[e, Add[m, 1]], 0]; NeQ[Multiply[Power[e, 2], Add[m, 1]], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r21, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 1141 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; LtQ[m, -1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi312r5Nondeg, ruleDecl := ``rubi312r5Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[d, Add[m, 1]], 0]; NeQ[Add[m, 1], 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_2_r5, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 698 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[m, -1]; GtQ[p, 0]",
      optionalFinding "d., m., a., b., c., n. and p."] },
  { rule := rubi313r10Nondeg, ruleDecl := ``rubi313r10Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, d, Add[q, 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_3_r10, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 551 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: q is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "LtQ[q, -1]",
      optionalFinding "e., a., b., c. and n."] },
  { rule := rubi314r18Nondeg, ruleDecl := ``rubi314r18Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_4_r18, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 143 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; ILtQ[q, -1]",
      optionalFinding "e., r., a., b., c., n. and p."] },
  { rule := rubi315r17Nondeg, ruleDecl := ``rubi315r17Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[d, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_3_1_5_r17, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 101 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: p, q are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[p, 0]; ILtQ[q, -1]",
      optionalFinding "e., r., a., b., c., n. and p."] },
  { rule := rubi1133r16Nondeg, ruleDecl := ``rubi1133r16Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[b1, b2, Add[Multiply[n, Add[p, 1]], 1]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_1_3_3_r16, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 182 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: non2 is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "EqQ[non2, Multiply[n, Power[2, -1]]]; EqQ[Add[Multiply[a2, b1], Multiply[a1, b2]], 0]; NeQ[Add[Multiply[n, Add[p, 1]], 1], 0]",
      optionalFinding "b1., non2., p., b2. and d."] },
  { rule := rubi1231r5Nondeg, ruleDecl := ``rubi1231r5Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[a, n, Add[p, 1], Add[Power[b, 2], Multiply[-1, 4, a, c]]], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_1_2_3_1_r5, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 56 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: n2, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "EqQ[n2, Multiply[2, n]]; NeQ[Add[Power[b, 2], Multiply[-1, 4, a, c]], 0]; ILtQ[p, -1]",
      optionalFinding "b., c. and n2."] },
  { rule := rubi4113r19Nondeg, ruleDecl := ``rubi4113r19Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[Multiply[2, c], 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_1_13_r19, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 1197 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m is not in the v0.1 FreeQ list, but RUBI's numeric conditions on it only hold for numbers, so the v1 rule declares it independent of x.",
      recFinding,
      condFinding "NeQ[Add[Multiply[b, e], Multiply[-1, 2, c, d]], 0]; GtQ[m, 1]",
      optionalFinding "d., e., a., b. and c."] },
  { rule := rubi478r48Nondeg, ruleDecl := ``rubi478r48Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the conditions NeQ[Multiply[a, n], 0]; NeQ[n, 0] (relation1#neq) are appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_8_r48, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 185 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      recFinding,
      condFinding "EqQ[m, Add[n, Multiply[-1, 1]]]",
      optionalFinding "m., a., n. and b."] },
  { rule := rubi479r27Nondeg, ruleDecl := ``rubi479r27Nondeg, proofs := [],
    unproved := [.real, .complex],
    findings := [
      "strengthened: the condition NeQ[b, 0] (relation1#neq) is appended to the converted v0.1 conditions. This corrected variant is not RUBI's rule as stated: it excludes the degenerate case of the counterexample to integration.rubi_4_7_9_r27, which stays refuted.",
      "numerical: checked over ℝ only, with no failure at 217 points: assignments of the metavariables satisfying the conditions (each metavariable 0 with probability 0.4, otherwise an integer between -3 and 3) and points where the integrand is defined, comparing a central difference of the result with the integrand, each residual integral replaced by a function whose derivative there is the residual integrand. In addition, the real zeros of every base raised to a negative or non-integer power in the residual integrands and the result were searched for, and the integrand is not defined around any of them. This is not a proof, and the complex domain is not checked.",
      "independence: m, n, p are not in the v0.1 FreeQ list, but RUBI's numeric conditions on them only hold for numbers, so the v1 rule declares them independent of x.",
      recFinding,
      condFinding "IGtQ[m, 0]; IGtQ[n, 0]; IGtQ[p, 0]",
      optionalFinding "e., f., m., c., d., p., n. and b."] }
]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- Every entry is well formed: recursive rules by `recOk`, the others by `wellFormed`. -/
theorem entries_wellFormed : ∀ e ∈ entries,
    (if e.rule.shape == .antiderivRec then e.rule.recOk else e.rule.wellFormed) = true := by
  intro e he
  simp only [entries, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

end OSR.IntegrationNum1
