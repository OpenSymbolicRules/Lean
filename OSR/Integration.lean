import OSR.Calculus

/-!
# Integration (RUBI)

First migration from `OpenSymbolicRules/Integration` at commit
`f84ed2a81702836c019e647e0a586b8d576ae7c6` (RUBI 4.16.1, 6,257 rules).

The scope is the nine rules a syntactic inventory selected: their only
conditions are `FreeQ` and, once the outer `Int` is removed, they use only
heads of the registry.  A rule `Int[F, x] := G` becomes the calculus rule
`int(λx. F) ⟶ λx. G` (`calculus1#int`, shape `antideriv`), whose statement is
`OSR.Calculus.AntiderivHolds`: wherever `F` is defined on a neighbourhood of
`t`, `G` is defined on a neighbourhood of `t` and has derivative `F` at `t`.

Encoding conventions, applied to the converted v0.1 terms without
simplification:

* an n-ary `Multiply` or `Add` is a left-nested chain;
* `Power[u, -1]` stays a power with exponent `-1`, not a division;
* an optional wildcard (`c.`, `n.`, …) is an ordinary metavariable: the v1
  rule matches only the explicit form, not the instances with RUBI's default
  value;
* `FreeQ[{…}, x]` becomes the `independent` constraint of each listed
  metavariable.

Six rules are migrated: two are proved, four are refuted by a Lean
counterexample.  Three use powers with non-integer exponents, outside the
fragment, and are reported in `notMigrated`.
-/

namespace OSR.Integration

open OSR OSR.Calculus Filter Topology

private abbrev x : Expr := .var "x"
private abbrev v (n : String) : Expr := .var n
private abbrev ln (e : Expr) : Expr := .app1 .ln e
private abbrev add (a b : Expr) : Expr := .app2 .add a b
private abbrev mul (a b : Expr) : Expr := .app2 .mul a b
private abbrev inv (e : Expr) : Expr := .pow e (.int (-1))

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

/-- Provenance: the converted v0.1 rule and the RUBI source it came from. -/
private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

private def linear : String := "rubi:1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.1 (a+b x)^m"
private def logPow : String := "rubi:3 Logarithms/3.1.1 (a+b log(c x^n))^p"
private def logMono : String := "rubi:3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p"
private def logMisc : String := "rubi:3 Logarithms/3.5 Miscellaneous logarithms"
private def simplification : String := "rubi:9 Miscellaneous/9.1 Integrand simplification rules"

/-- `c ln(c x^n)` as converted: `Log[c x^n]`. -/
private abbrev logCxn (c n : String) : Expr := ln (mul (v c) (.pow x (v n)))

/-! ## Rules -/

/-- `Int[1/x, x] := Log[x]`, converted as `1 · x^(-1)`. -/
def reciprocal : CRule where
  id := "integration.reciprocal"; legacyId := some s!"{linear}:1"; shape := .antideriv
  x := "x"; body := mul (.int 1) (inv x); result := ln x; priority := 10
  description := "Antiderivative of 1/x"
  provenance := migrated s!"{linear}:1" "1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.1 (a+b x)^m.m#1"

/-- `Int[Log[c x^n], x] := x Log[c x^n] - n x`. -/
def logMonomial : CRule where
  id := "integration.log_monomial"; legacyId := some s!"{logPow}:1"; shape := .antideriv
  x := "x"; body := logCxn "c" "n"
  result := add (mul x (logCxn "c" "n")) (mul (mul (.int (-1)) (v "n")) x)
  independent := ["c", "n"]; priority := 20
  description := "Antiderivative of log(c x^n)"
  provenance := migrated s!"{logPow}:1" "3 Logarithms/3.1.1 (a+b log(c x^n))^p.m#1"

/-- `Int[(a + b Log[c x^n])/x, x] := (a + b Log[c x^n])^2/(2 b n)`. -/
def logLinearOverX : CRule where
  id := "integration.log_linear_over_x"; legacyId := some s!"{logMono}:1"; shape := .antideriv
  x := "x"; body := mul (add (v "a") (mul (v "b") (logCxn "c" "n"))) (inv x)
  result := mul (.pow (add (v "a") (mul (v "b") (logCxn "c" "n"))) (.int 2))
    (inv (mul (mul (.int 2) (v "b")) (v "n")))
  independent := ["a", "b", "c", "n"]; priority := 30
  description := "Antiderivative of (a + b log(c x^n))/x"
  provenance := migrated s!"{logMono}:1" "3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m#1"

/-- `log(d x^n)`. -/
private abbrev logDxn : Expr := logCxn "d" "n"

/-- `a + b log(c log(d x^n)^p)`. -/
private abbrev logLogLinear : Expr :=
  add (v "a") (mul (v "b") (ln (mul (v "c") (.pow logDxn (v "p")))))

/-- `Int[(a + b Log[c Log[d x^n]^p])/x, x] :=
Log[d x^n] (a + b Log[c Log[d x^n]^p])/n - b p Log[x]`. -/
def logLogOverX : CRule where
  id := "integration.log_log_over_x"; legacyId := some s!"{logMisc}:2"; shape := .antideriv
  x := "x"; body := mul logLogLinear (inv x)
  result := add (mul (mul logDxn logLogLinear) (inv (v "n")))
    (mul (mul (mul (.int (-1)) (v "b")) (v "p")) (ln x))
  independent := ["a", "b", "c", "d", "n", "p"]; priority := 40
  description := "Antiderivative of (a + b log(c log(d x^n)^p))/x"
  provenance := migrated s!"{logMisc}:2" "3 Logarithms/3.5 Miscellaneous logarithms.m#2"

/-- `Int[a, x] := a x` for `a` free of `x`. -/
def constant : CRule where
  id := "integration.constant"; legacyId := some s!"{simplification}:8"; shape := .antideriv
  x := "x"; body := v "a"; result := mul (v "a") x
  independent := ["a"]; priority := 50
  description := "Antiderivative of a constant"
  provenance := migrated s!"{simplification}:8" "9 Miscellaneous/9.1 Integrand simplification rules.m#8"

/-- `Int[a (b + c x), x] := a (b + c x)^2/(2 c)`. -/
def constTimesLinear : CRule where
  id := "integration.constant_times_linear"; legacyId := some s!"{simplification}:9"
  shape := .antideriv; x := "x"
  body := mul (v "a") (add (v "b") (mul (v "c") x))
  result := mul (mul (v "a") (.pow (add (v "b") (mul (v "c") x)) (.int 2)))
    (inv (mul (.int 2) (v "c")))
  independent := ["a", "b", "c"]; priority := 60
  description := "Antiderivative of a constant times a linear function"
  provenance := migrated s!"{simplification}:9" "9 Miscellaneous/9.1 Integrand simplification rules.m#9"

/-- v0.1 rules of the inventory outside the fragment, with the reason. -/
def notMigrated : List (String × String) := [
  ("rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p:10",
    "the integrand raises a + c x^2 to the exponent 3/2; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:2 Exponentials/2.3 Miscellaneous exponentials:1",
    "the integrand F^(c (a + b x)) is a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only"),
  ("rubi:2 Exponentials/2.3 Miscellaneous exponentials:8",
    "the integrand F^(a + b (c + d x)) is a power with a non-constant exponent; the fragment interprets arith1#power for integer exponents only")]

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem ax : ("a" : String) ≠ "x" := by decide
private theorem bx : ("b" : String) ≠ "x" := by decide
private theorem cx : ("c" : String) ≠ "x" := by decide
private theorem dx : ("d" : String) ≠ "x" := by decide
private theorem nx : ("n" : String) ≠ "x" := by decide
private theorem px : ("p" : String) ≠ "x" := by decide

private theorem toInt?_zero (I : Interp 𝕜) : I.toInt? (0 : 𝕜) = some 0 :=
  (I.toInt?_eq _ _).2 (by simp)

/-- `∫ a = a x` in any interpretation. -/
theorem constant_holds (I : Interp 𝕜) : AntiderivHolds I "x" constant.body constant.result := by
  intro env t _
  simp only [constant, Defined, eval, Function.update_self, Function.update_apply, ax, ite_false,
    and_self, Filter.eventually_true, true_and]
  exact ((hasDerivAt_id' t).const_mul (env "a")).congr_deriv (mul_one _)

theorem constant_real : constant.Holds .real := constant_holds Interp.real

theorem constant_complex : constant.Holds .complex := constant_holds Interp.complex

/-- **Counterexample.**  At `c = 0` the integrand `a (b + c x)` is defined
everywhere, but `(2 c)^(-1)` is not. -/
theorem constTimesLinear_not (I : Interp 𝕜) :
    ¬ AntiderivHolds I "x" constTimesLinear.body constTimesLinear.result := by
  refine not_antiderivHolds (fun _ => 0) 0 (Eventually.of_forall fun _ => ?_) ?_
  · simp [constTimesLinear, Defined]
  · intro h
    simp only [constTimesLinear, Defined, eval, Interp.toInt?_cast] at h
    simp at h

theorem constTimesLinear_counterexample_real : ¬ constTimesLinear.Holds .real :=
  constTimesLinear_not Interp.real

theorem constTimesLinear_counterexample_complex : ¬ constTimesLinear.Holds .complex :=
  constTimesLinear_not Interp.complex

/-- **Counterexample.**  Near `-1`, `1 · x^(-1)` is defined, but `ln(-1)` is
not (`transc1#ln` is defined on the positive reals). -/
theorem reciprocal_counterexample_real : ¬ reciprocal.Holds .real := by
  show ¬ AntiderivHolds Interp.real "x" reciprocal.body reciprocal.result
  refine not_antiderivHolds (fun _ => 0) (-1) ?_ ?_
  · filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℝ) ≠ 0)] with v hv
    simp only [reciprocal, Defined, eval, Interp.toInt?_cast]
    simp [Function.update_self, hv]
  · simp [reciprocal, Defined, eval, Interp.real]

/-- **Counterexample** to `∫ (a + b log(c x^n))/x`, for any interpretation in
which `ln` is defined at `1`: at `b = n = 0`, `c = 1`, the integrand is defined
near `1`, but `(2 b n)^(-1)` is not. -/
theorem logLinearOverX_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivHolds I "x" logLinearOverX.body logLinearOverX.result := by
  refine not_antiderivHolds (fun s => if s = "c" then 1 else 0) 1 ?_ ?_
  · filter_upwards [eventually_ne_nhds (one_ne_zero (α := 𝕜))] with v hv
    simp only [logLinearOverX, Defined, eval, Interp.toInt?_cast]
    simp [toInt?_zero, h1, hv]
  · intro h
    simp only [logLinearOverX, Defined, eval, Interp.toInt?_cast] at h
    simp at h

theorem logLinearOverX_counterexample_real : ¬ logLinearOverX.Holds .real :=
  logLinearOverX_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem logLinearOverX_counterexample_complex : ¬ logLinearOverX.Holds .complex :=
  logLinearOverX_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

/-- **Counterexample** to the `log log` rule, for any interpretation in which
`ln` is defined at `1`: at `a = b = n = p = 0`, `c = d = 1`, the integrand is
defined near `1`, but `n^(-1)` is not. -/
theorem logLogOverX_not (I : Interp 𝕜) (h1 : I.lnDefined 1) :
    ¬ AntiderivHolds I "x" logLogOverX.body logLogOverX.result := by
  refine not_antiderivHolds (fun s => if s = "c" ∨ s = "d" then 1 else 0) 1 ?_ ?_
  · filter_upwards [eventually_ne_nhds (one_ne_zero (α := 𝕜))] with v hv
    simp only [logLogOverX, Defined, eval, Interp.toInt?_cast]
    simp [toInt?_zero, h1, hv]
  · intro h
    simp only [logLogOverX, Defined, eval, Interp.toInt?_cast] at h
    simp at h

theorem logLogOverX_counterexample_real : ¬ logLogOverX.Holds .real :=
  logLogOverX_not Interp.real (show (0 : ℝ) < 1 from one_pos)

theorem logLogOverX_counterexample_complex : ¬ logLogOverX.Holds .complex :=
  logLogOverX_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero)

end Proofs

/-- The integrand of `logMonomial` is defined exactly where `c x^k > 0`, `k`
the integer value of `n`, and `x ≠ 0` if `k < 0`. -/
private theorem logMonomial_defined (env : String → ℝ) {k : ℤ}
    (hk : intValue? (env "n") = some k) (w : ℝ) :
    Defined Interp.real (Function.update env "x" w) logMonomial.body ↔
      (k < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ k := by
  simp [logMonomial, Defined, eval, Interp.real, cx, nx, hk]

theorem logMonomial_real : logMonomial.Holds .real := by
  show AntiderivHolds Interp.real "x" logMonomial.body logMonomial.result
  intro env t hF
  obtain ⟨k, hk⟩ : ∃ k, intValue? (env "n") = some k := by
    have h := hF.self_of_nhds
    simp only [logMonomial, Defined, eval, Interp.real] at h
    obtain ⟨⟨-, -, -, k, hk, -⟩, -⟩ := h
    simp only [Function.update_apply, nx, ite_false] at hk
    exact ⟨k, hk⟩
  have hn : env "n" = k := (intValue?_eq _ _).1 hk
  have hD := logMonomial_defined env hk
  have hDG : ∀ w, Defined Interp.real (Function.update env "x" w) logMonomial.result ↔
      (k < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ k := by
    intro w
    rw [← hD w]
    simp [logMonomial, Defined]
  have hE : ∀ w, eval Interp.real (Function.update env "x" w) logMonomial.result =
      w * Real.log (env "c" * w ^ k) + -1 * env "n" * w := by
    intro w
    simp [logMonomial, eval, Interp.real, cx, nx, hk]
  have hEF : eval Interp.real (Function.update env "x" t) logMonomial.body =
      Real.log (env "c" * t ^ k) := by
    simp [logMonomial, eval, Interp.real, cx, nx, hk]
  refine ⟨?_, ?_⟩
  · filter_upwards [hF] with w hw
    exact (hDG w).2 ((hD w).1 hw)
  · obtain ⟨hk0, hpos⟩ := (hD t).1 hF.self_of_nhds
    have hne : t ≠ 0 ∨ 0 ≤ k := by
      by_cases h : k < 0
      · exact Or.inl (hk0 h)
      · exact Or.inr (by omega)
    have hfun : (fun w => eval Interp.real (Function.update env "x" w) logMonomial.result) =
        fun w => w * Real.log (env "c" * w ^ k) + -1 * env "n" * w := funext hE
    rw [hEF, hfun]
    have hlog := ((hasDerivAt_zpow k t hne).const_mul (env "c")).log hpos.ne'
    have h := ((hasDerivAt_id' t).mul hlog).add ((hasDerivAt_id' t).const_mul (-1 * env "n"))
    refine h.congr_deriv ?_
    rw [hn]
    rcases eq_or_ne k 0 with rfl | hk1
    · simp
    · have ht : t ≠ 0 := by
        rcases hne with h | h
        · exact h
        · intro h0
          subst h0
          rw [zero_zpow k hk1, mul_zero] at hpos
          exact lt_irrefl 0 hpos
      have hc : env "c" ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hpos
        exact lt_irrefl 0 hpos
      rw [zpow_sub_one₀ ht]
      field_simp
      ring

private def lnComplexFinding : String :=
  "complex: not proved; ln is defined for z ≠ 0, but the principal logarithm is discontinuous across the negative real axis (its branch cut), where the integrand is defined, so the statement is not expected to hold there."

private def optionalFinding (vars : String) (plural : Bool := true) : String :=
  if plural then
    s!"matching: the optional wildcards {vars} of the v0.1 pattern are ordinary metavariables; the v1 rule does not match the instances with RUBI's default values."
  else
    s!"matching: the optional wildcard {vars} of the v0.1 pattern is an ordinary metavariable; the v1 rule does not match the instances with RUBI's default value."

/-- The Integration catalogue, in v0.1 file order. -/
def catalog : List CEntry := [
  { rule := reciprocal, ruleDecl := ``reciprocal, proofs := [], unproved := [.complex],
    counterexamples := [(.real, ``reciprocal_counterexample_real)],
    findings := [
      "counterexample: near x = -1 the integrand 1 · x^(-1) is defined, but ln(-1) is not, since transc1#ln is defined on the positive reals (Lean theorem reciprocal_counterexample_real). RUBI reads Log as the complex logarithm; a real antiderivative is ln|x|, which is outside the fragment.",
      lnComplexFinding] },
  { rule := logMonomial, ruleDecl := ``logMonomial,
    proofs := [(.real, ``logMonomial_real)], unproved := [.complex],
    findings := [
      "real: n must take an integer value, since the fragment interprets arith1#power for integer exponents only; the statement covers every point near which c x^n > 0.",
      lnComplexFinding, optionalFinding "c. and n."] },
  { rule := logLinearOverX, ruleDecl := ``logLinearOverX, proofs := [],
    counterexamples := [(.real, ``logLinearOverX_counterexample_real),
      (.complex, ``logLinearOverX_counterexample_complex)],
    findings := [
      "counterexample: at b = n = 0 and c = 1 the integrand is defined near x = 1, but (2 b n)^(-1) is not (Lean theorems logLinearOverX_counterexample_real and logLinearOverX_counterexample_complex). The v0.1 rule has only FreeQ conditions. In Mathematica an integrand with a literal b = 0 is simplified before matching, so this instance does not arise there; OSR v1 matching performs no such evaluation. The rule needs the conditions b ≠ 0 and n ≠ 0, which this migration does not add.",
      optionalFinding "a., b., c. and n."] },
  { rule := logLogOverX, ruleDecl := ``logLogOverX, proofs := [],
    counterexamples := [(.real, ``logLogOverX_counterexample_real),
      (.complex, ``logLogOverX_counterexample_complex)],
    findings := [
      "counterexample: at a = b = n = p = 0 and c = d = 1 the integrand is defined near x = 1, but n^(-1) is not (Lean theorems logLogOverX_counterexample_real and logLogOverX_counterexample_complex). The rule needs n ≠ 0, which this migration does not add.",
      "real: even with n ≠ 0, ln x in the result is undefined for x < 0, where the integrand can be defined (n even, d > 0); not proved.",
      optionalFinding "a., b., c., d., n. and p."] },
  { rule := constant, ruleDecl := ``constant,
    proofs := [(.real, ``constant_real), (.complex, ``constant_complex)] },
  { rule := constTimesLinear, ruleDecl := ``constTimesLinear, proofs := [],
    counterexamples := [(.real, ``constTimesLinear_counterexample_real),
      (.complex, ``constTimesLinear_counterexample_complex)],
    findings := [
      "counterexample: at c = 0 the integrand a (b + c x) is defined everywhere, but (2 c)^(-1) is not (Lean theorems constTimesLinear_counterexample_real and constTimesLinear_counterexample_complex). The rule needs c ≠ 0, which this migration does not add.",
      optionalFinding "c." false] }
]

/-- Every catalogue rule is well formed. -/
theorem catalog_wellFormed : ∀ e ∈ catalog, e.rule.wellFormed = true := by
  intro e he
  simp only [catalog, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end OSR.Integration
