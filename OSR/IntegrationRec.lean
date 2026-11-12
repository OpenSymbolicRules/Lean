import OSR.Calculus

/-!
# Integration (RUBI): rules with residual integrals

A RUBI rule whose result contains `Int[H, x]` becomes a recursive
antiderivative rule (`Shape.antiderivRec`): the result is an expression in
which each residual integral is a hole variable `I1`, `I2`, …, exported as
`int(λx. H)(x)` (the form of the `calculus1#int` FMP).  Its statement,
`OSR.Calculus.AntiderivRecHolds`, says that wherever the integrand is defined
near a point, the residual integrands are defined near it too, and that for
every choice of antiderivatives of the residual integrands the result is an
antiderivative of the integrand.

The reference rewriter does not apply these rules: continuing inside a
residual integral is left to the consumer.  The conventions of
`OSR.Integration` (left-nested products and sums, `Power[u, -1]` kept,
optional wildcards as plain metavariables, `FreeQ` as `independent`, `NeQ`,
`GtQ` and `IntegerQ` as conditions) apply.
-/

namespace OSR.IntegrationRec

open OSR OSR.Calculus Filter Topology

private abbrev x : Expr := .var "x"
private abbrev v (n : String) : Expr := .var n
private abbrev ln (e : Expr) : Expr := .app1 .ln e
private abbrev sin (e : Expr) : Expr := .app1 .sin e
private abbrev cos (e : Expr) : Expr := .app1 .cos e
private abbrev add (a b : Expr) : Expr := .app2 .add a b
private abbrev mul (a b : Expr) : Expr := .app2 .mul a b
private abbrev inv (e : Expr) : Expr := .pow e (.int (-1))
private abbrev sq (e : Expr) : Expr := .pow e (.int 2)
private abbrev neg (e : Expr) : Expr := mul (.int (-1)) e

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

private def sine : String := "rubi:4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p"
private def sineM : String := "4 Trig functions/4.1 Sine/4.1.12 (e x)^m (a+b sin(c+d x^n))^p.m"
private def logPow : String := "rubi:3 Logarithms/3.1.1 (a+b log(c x^n))^p"
private def logMisc : String := "rubi:3 Logarithms/3.5 Miscellaneous logarithms"
private def trigLog : String := "rubi:4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p"
private def quad : String := "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p"

/-! ## Rules -/

/-- `d (e + f x)^2`. -/
private abbrev sqArg : Expr := mul (v "d") (sq (add (v "e") (mul (v "f") x)))
/-- `d x^n`. -/
private abbrev powArg : Expr := mul (v "d") (.pow x (v "n"))

/-- `Int[Sin[c + d (e + f x)^2], x] := Sin[c] Int[Cos[d (e + f x)^2], x]
+ Cos[c] Int[Sin[d (e + f x)^2], x]`. -/
def sinAddSq : CRule where
  id := "integration.sin_add_square"; legacyId := some s!"{sine}:3"; shape := .antiderivRec
  x := "x"; body := sin (add (v "c") sqArg)
  result := add (mul (sin (v "c")) (v "I1")) (mul (cos (v "c")) (v "I2"))
  integrals := [("I1", cos sqArg), ("I2", sin sqArg)]
  independent := ["c", "d", "e", "f"]; priority := 140
  description := "sin(c + u) = sin c cos u + cos c sin u under the integral"
  provenance := migrated s!"{sine}:3" s!"{sineM}#3"

/-- `Int[Cos[c + d (e + f x)^2], x] := Cos[c] Int[Cos[…], x] - Sin[c] Int[Sin[…], x]`. -/
def cosAddSq : CRule where
  id := "integration.cos_add_square"; legacyId := some s!"{sine}:4"; shape := .antiderivRec
  x := "x"; body := cos (add (v "c") sqArg)
  result := add (mul (cos (v "c")) (v "I1")) (mul (neg (sin (v "c"))) (v "I2"))
  integrals := [("I1", cos sqArg), ("I2", sin sqArg)]
  independent := ["c", "d", "e", "f"]; priority := 150
  description := "cos(c + u) = cos c cos u - sin c sin u under the integral"
  provenance := migrated s!"{sine}:4" s!"{sineM}#4"

/-- `Int[Sin[c + d x^n]/x, x] := Sin[c] Int[Cos[d x^n]/x, x] + Cos[c] Int[Sin[d x^n]/x, x]`. -/
def sinAddPowOverX : CRule where
  id := "integration.sin_add_power_over_x"; legacyId := some s!"{sine}:25"
  shape := .antiderivRec; x := "x"
  body := mul (sin (add (v "c") powArg)) (inv x)
  result := add (mul (sin (v "c")) (v "I1")) (mul (cos (v "c")) (v "I2"))
  integrals := [("I1", mul (cos powArg) (inv x)), ("I2", mul (sin powArg) (inv x))]
  independent := ["c", "d", "n"]; priority := 160
  description := "sin(c + d x^n)/x split by the addition formula"
  provenance := migrated s!"{sine}:25" s!"{sineM}#25"

/-- `Int[Cos[c + d x^n]/x, x] := Cos[c] Int[Cos[d x^n]/x, x] - Sin[c] Int[Sin[d x^n]/x, x]`. -/
def cosAddPowOverX : CRule where
  id := "integration.cos_add_power_over_x"; legacyId := some s!"{sine}:26"
  shape := .antiderivRec; x := "x"
  body := mul (cos (add (v "c") powArg)) (inv x)
  result := add (mul (cos (v "c")) (v "I1")) (mul (neg (sin (v "c"))) (v "I2"))
  integrals := [("I1", mul (cos powArg) (inv x)), ("I2", mul (sin powArg) (inv x))]
  independent := ["c", "d", "n"]; priority := 170
  description := "cos(c + d x^n)/x split by the addition formula"
  provenance := migrated s!"{sine}:26" s!"{sineM}#26"

/-- `a + b x^n/2`. -/
private abbrev halfArg : Expr := add (v "a") (mul (mul (v "b") (.pow x (v "n"))) (inv (.int 2)))
/-- `x^m cos(2 a + b x^n)`. -/
private abbrev doubleArg : Expr :=
  mul (.pow x (v "m")) (cos (add (mul (.int 2) (v "a")) (mul (v "b") (.pow x (v "n")))))
/-- `1/2`, as converted: `1 · 2^(-1)`. -/
private abbrev half : Expr := mul (.int 1) (inv (.int 2))

/-- `Int[x^m Sin[a + b x^n/2]^2, x] := 1/2 Int[x^m, x] - 1/2 Int[x^m Cos[2 a + b x^n], x]`. -/
def powSinSq : CRule where
  id := "integration.power_sin_square"; legacyId := some s!"{sine}:39"; shape := .antiderivRec
  x := "x"; body := mul (.pow x (v "m")) (sq (sin halfArg))
  result := add (mul half (v "I1")) (mul (mul (mul (.int (-1)) (.int 1)) (inv (.int 2))) (v "I2"))
  integrals := [("I1", .pow x (v "m")), ("I2", doubleArg)]
  independent := ["a", "b", "m", "n"]; priority := 180
  description := "x^m sin(θ)^2 = x^m/2 - x^m cos(2θ)/2 under the integral"
  provenance := migrated s!"{sine}:39" s!"{sineM}#39"

/-- `Int[x^m Cos[a + b x^n/2]^2, x] := 1/2 Int[x^m, x] + 1/2 Int[x^m Cos[2 a + b x^n], x]`. -/
def powCosSq : CRule where
  id := "integration.power_cos_square"; legacyId := some s!"{sine}:40"; shape := .antiderivRec
  x := "x"; body := mul (.pow x (v "m")) (sq (cos halfArg))
  result := add (mul half (v "I1")) (mul half (v "I2"))
  integrals := [("I1", .pow x (v "m")), ("I2", doubleArg)]
  independent := ["a", "b", "m", "n"]; priority := 190
  description := "x^m cos(θ)^2 = x^m/2 + x^m cos(2θ)/2 under the integral"
  provenance := migrated s!"{sine}:40" s!"{sineM}#40"

/-- `log(d x^n)`. -/
private abbrev logDxn : Expr := ln (mul (v "d") (.pow x (v "n")))
/-- `log(c log(d x^n)^p)`. -/
private abbrev logLog : Expr := ln (mul (v "c") (.pow logDxn (v "p")))

/-- `Int[Log[c Log[d x^n]^p], x] := x Log[c Log[d x^n]^p] - n p Int[1/Log[d x^n], x]`. -/
def logPowLog : CRule where
  id := "integration.log_power_log"; legacyId := some s!"{logMisc}:1"; shape := .antiderivRec
  x := "x"; body := logLog
  result := add (mul x logLog) (mul (mul (mul (.int (-1)) (v "n")) (v "p")) (v "I1"))
  integrals := [("I1", mul (.int 1) (inv logDxn))]
  independent := ["c", "d", "n", "p"]; priority := 200
  description := "Integration by parts of log(c log(d x^n)^p)"
  provenance := migrated s!"{logMisc}:1" "3 Logarithms/3.5 Miscellaneous logarithms.m#1"

/-- `a + b log(c x^n)`. -/
private abbrev logLin : Expr := add (v "a") (mul (v "b") (ln (mul (v "c") (.pow x (v "n")))))

/-- `Int[(a + b Log[c x^n])^p, x] := x (a + b Log[c x^n])^p
- b n p Int[(a + b Log[c x^n])^(p - 1), x]` for `p > 0` and `2 p ∈ ℤ`. -/
def logLinPow : CRule where
  id := "integration.log_linear_power"; legacyId := some s!"{logPow}:2"; shape := .antiderivRec
  x := "x"; body := .pow logLin (v "p")
  result := add (mul x (.pow logLin (v "p")))
    (mul (mul (mul (mul (.int (-1)) (v "b")) (v "n")) (v "p")) (v "I1"))
  integrals := [("I1", .pow logLin (add (v "p") (mul (.int (-1)) (.int 1))))]
  independent := ["a", "b", "c", "n", "p"]
  conditions := [.gt (v "p") (.int 0), .int (mul (.int 2) (v "p"))]; priority := 210
  description := "Reduction of (a + b log(c x^n))^p"
  provenance := migrated s!"{logPow}:2" "3 Logarithms/3.1.1 (a+b log(c x^n))^p.m#2"

/-- `a x log(b x)`. -/
private abbrev xLog : Expr := mul (mul (v "a") x) (ln (mul (v "b") x))

/-- `Int[Sin[a x Log[b x]] Log[b x], x] := -Cos[a x Log[b x]]/a - Int[Sin[a x Log[b x]], x]`. -/
def sinXLog : CRule where
  id := "integration.sin_x_log_times_log"; legacyId := some s!"{trigLog}:45"
  shape := .antiderivRec; x := "x"
  body := mul (sin xLog) (ln (mul (v "b") x))
  result := add (mul (mul (.int (-1)) (cos xLog)) (inv (v "a"))) (neg (v "I1"))
  integrals := [("I1", sin xLog)]
  independent := ["a", "b"]; priority := 220
  description := "Antiderivative of sin(a x log(b x)) log(b x)"
  provenance := migrated s!"{trigLog}:45" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#45"

/-- `Int[Cos[a x Log[b x]] Log[b x], x] := Sin[a x Log[b x]]/a - Int[Cos[a x Log[b x]], x]`. -/
def cosXLog : CRule where
  id := "integration.cos_x_log_times_log"; legacyId := some s!"{trigLog}:46"
  shape := .antiderivRec; x := "x"
  body := mul (cos xLog) (ln (mul (v "b") x))
  result := add (mul (sin xLog) (inv (v "a"))) (neg (v "I1"))
  integrals := [("I1", cos xLog)]
  independent := ["a", "b"]; priority := 230
  description := "Antiderivative of cos(a x log(b x)) log(b x)"
  provenance := migrated s!"{trigLog}:46" "4 Trig functions/4.7 Miscellaneous/4.7.8 u trig(a+b log(c x^n))^p.m#46"

/-- `a + c x^2`. -/
private abbrev quadExpr : Expr := add (v "a") (mul (v "c") (sq x))

/-- `Int[(d + e x) (a + c x^2)^p, x] := e (a + c x^2)^(p+1)/(2 c (p+1))
+ d Int[(a + c x^2)^p, x]` for `p ≠ -1`. -/
def linearQuadPow : CRule where
  id := "integration.linear_times_quadratic_power"; legacyId := some s!"{quad}:14"
  shape := .antiderivRec; x := "x"
  body := mul (add (v "d") (mul (v "e") x)) (.pow quadExpr (v "p"))
  result := add
    (mul (mul (v "e") (.pow quadExpr (add (v "p") (.int 1))))
      (inv (mul (mul (.int 2) (v "c")) (add (v "p") (.int 1)))))
    (mul (v "d") (v "I1"))
  integrals := [("I1", .pow quadExpr (v "p"))]
  independent := ["a", "c", "d", "e", "p"]; conditions := [.ne (v "p") (.int (-1))]
  priority := 240
  description := "Antiderivative of (d + e x) (a + c x^2)^p"
  provenance := migrated s!"{quad}:14" "1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.2 (d+e x)^m (a+b x+c x^2)^p.m#14"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem toInt?_zero (I : Interp 𝕜) : I.toInt? (0 : 𝕜) = some 0 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_two (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some 2 :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem toInt?_neg_one (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

/-- The addition formula proves `sinAddSq` in any interpretation having it. -/
theorem sinAddSq_holds (I : Interp 𝕜)
    (hadd : ∀ a b : 𝕜, I.sin (a + b) = I.sin a * I.cos b + I.cos a * I.sin b) :
    AntiderivRecHolds I "x" sinAddSq.conditions sinAddSq.body sinAddSq.result
      sinAddSq.integrals := by
  intro env _ t _
  refine ⟨fun i hi => Eventually.of_forall fun _ => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [sinAddSq, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp [Defined, eval, toInt?_two]
  · exact Eventually.of_forall fun _ => by simp [sinAddSq, Defined]
  · simp only [sinAddSq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (sinAddSq.integrals.map (·.1)) Φ "x" w)
        sinAddSq.result) = fun w => I.sin (env "c") * Φ "I1" w + I.cos (env "c") * Φ "I2" w := by
      funext w
      simp [sinAddSq, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [sinAddSq, eval, toInt?_two, hadd]

theorem sinAddSq_real : sinAddSq.Holds .real := sinAddSq_holds Interp.real Real.sin_add

theorem sinAddSq_complex : sinAddSq.Holds .complex :=
  sinAddSq_holds Interp.complex Complex.sin_add

/-- The addition formula proves `cosAddSq`. -/
theorem cosAddSq_holds (I : Interp 𝕜)
    (hadd : ∀ a b : 𝕜, I.cos (a + b) = I.cos a * I.cos b - I.sin a * I.sin b) :
    AntiderivRecHolds I "x" cosAddSq.conditions cosAddSq.body cosAddSq.result
      cosAddSq.integrals := by
  intro env _ t _
  refine ⟨fun i hi => Eventually.of_forall fun _ => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [cosAddSq, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp [Defined, eval, toInt?_two]
  · exact Eventually.of_forall fun _ => by simp [cosAddSq, Defined]
  · simp only [cosAddSq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (cosAddSq.integrals.map (·.1)) Φ "x" w)
        cosAddSq.result) =
        fun w => I.cos (env "c") * Φ "I1" w + -1 * I.sin (env "c") * Φ "I2" w := by
      funext w
      simp [cosAddSq, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp only [cosAddSq, eval, Interp.toInt?_cast, Function.update_self, Function.update_apply]
    simp [hadd]
    ring

theorem cosAddSq_real : cosAddSq.Holds .real := cosAddSq_holds Interp.real Real.cos_add

theorem cosAddSq_complex : cosAddSq.Holds .complex :=
  cosAddSq_holds Interp.complex Complex.cos_add

/-- The addition formula proves `sinAddPowOverX`. -/
theorem sinAddPowOverX_holds (I : Interp 𝕜)
    (hadd : ∀ a b : 𝕜, I.sin (a + b) = I.sin a * I.cos b + I.cos a * I.sin b) :
    AntiderivRecHolds I "x" sinAddPowOverX.conditions sinAddPowOverX.body
      sinAddPowOverX.result sinAddPowOverX.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [sinAddPowOverX, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simpa [sinAddPowOverX, Defined, eval, toInt?_neg_one] using hw
  · exact Eventually.of_forall fun _ => by simp [sinAddPowOverX, Defined]
  · simp only [sinAddPowOverX, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (sinAddPowOverX.integrals.map (·.1)) Φ "x" w)
        sinAddPowOverX.result) =
        fun w => I.sin (env "c") * Φ "I1" w + I.cos (env "c") * Φ "I2" w := by
      funext w
      simp [sinAddPowOverX, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [sinAddPowOverX, eval, toInt?_neg_one, hadd]
    ring

theorem sinAddPowOverX_real : sinAddPowOverX.Holds .real :=
  sinAddPowOverX_holds Interp.real Real.sin_add

theorem sinAddPowOverX_complex : sinAddPowOverX.Holds .complex :=
  sinAddPowOverX_holds Interp.complex Complex.sin_add

/-- The addition formula proves `cosAddPowOverX`. -/
theorem cosAddPowOverX_holds (I : Interp 𝕜)
    (hadd : ∀ a b : 𝕜, I.cos (a + b) = I.cos a * I.cos b - I.sin a * I.sin b) :
    AntiderivRecHolds I "x" cosAddPowOverX.conditions cosAddPowOverX.body
      cosAddPowOverX.result cosAddPowOverX.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [cosAddPowOverX, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simpa [cosAddPowOverX, Defined, eval, toInt?_neg_one] using hw
  · exact Eventually.of_forall fun _ => by simp [cosAddPowOverX, Defined]
  · simp only [cosAddPowOverX, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (cosAddPowOverX.integrals.map (·.1)) Φ "x" w)
        cosAddPowOverX.result) =
        fun w => I.cos (env "c") * Φ "I1" w + -1 * I.sin (env "c") * Φ "I2" w := by
      funext w
      simp [cosAddPowOverX, eval, recEnv]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp only [cosAddPowOverX, eval, Interp.toInt?_cast, Function.update_self,
      Function.update_apply]
    simp [hadd]
    ring

theorem cosAddPowOverX_real : cosAddPowOverX.Holds .real :=
  cosAddPowOverX_holds Interp.real Real.cos_add

theorem cosAddPowOverX_complex : cosAddPowOverX.Holds .complex :=
  cosAddPowOverX_holds Interp.complex Complex.cos_add

/-- The half-angle formula proves `powSinSq`. -/
theorem powSinSq_holds (I : Interp 𝕜) (h2 : (2 : 𝕜) ≠ 0)
    (hsq : ∀ a y : 𝕜, I.sin (a + y * 2⁻¹) ^ 2 = 2⁻¹ - 2⁻¹ * I.cos (2 * a + y)) :
    AntiderivRecHolds I "x" powSinSq.conditions powSinSq.body powSinSq.result
      powSinSq.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powSinSq, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simp [powSinSq, Defined, eval, toInt?_two, toInt?_neg_one] at hw ⊢
      tauto
  · exact Eventually.of_forall fun _ => by
      simp [powSinSq, Defined, eval, toInt?_neg_one, h2]
  · simp only [powSinSq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (powSinSq.integrals.map (·.1)) Φ "x" w)
        powSinSq.result) = fun w => 1 * 2⁻¹ * Φ "I1" w + -1 * 1 * 2⁻¹ * Φ "I2" w := by
      funext w
      simp [powSinSq, eval, recEnv, toInt?_neg_one]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [powSinSq, eval, toInt?_two, toInt?_neg_one, hsq]
    ring

theorem powSinSq_real : powSinSq.Holds .real := by
  refine powSinSq_holds Interp.real two_ne_zero fun a y => ?_
  simp only [Interp.real]
  rw [Real.sin_sq, Real.cos_sq, show 2 * (a + y * 2⁻¹) = 2 * a + y by ring]
  ring

theorem powSinSq_complex : powSinSq.Holds .complex := by
  refine powSinSq_holds Interp.complex two_ne_zero fun a y => ?_
  simp only [Interp.complex]
  rw [Complex.sin_sq, Complex.cos_sq, show 2 * (a + y * 2⁻¹) = 2 * a + y by ring]
  ring

/-- The half-angle formula proves `powCosSq`. -/
theorem powCosSq_holds (I : Interp 𝕜) (h2 : (2 : 𝕜) ≠ 0)
    (hsq : ∀ a y : 𝕜, I.cos (a + y * 2⁻¹) ^ 2 = 2⁻¹ + 2⁻¹ * I.cos (2 * a + y)) :
    AntiderivRecHolds I "x" powCosSq.conditions powCosSq.body powCosSq.result
      powCosSq.integrals := by
  intro env _ t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [powCosSq, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · filter_upwards [hF] with w hw
      simp [powCosSq, Defined, eval, toInt?_two, toInt?_neg_one] at hw ⊢
      tauto
  · exact Eventually.of_forall fun _ => by
      simp [powCosSq, Defined, eval, toInt?_neg_one, h2]
  · simp only [powCosSq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (powCosSq.integrals.map (·.1)) Φ "x" w)
        powCosSq.result) = fun w => 1 * 2⁻¹ * Φ "I1" w + 1 * 2⁻¹ * Φ "I2" w := by
      funext w
      simp [powCosSq, eval, recEnv, toInt?_neg_one]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [powCosSq, eval, toInt?_two, toInt?_neg_one, hsq]
    ring

theorem powCosSq_real : powCosSq.Holds .real := by
  refine powCosSq_holds Interp.real two_ne_zero fun a y => ?_
  simp only [Interp.real]
  rw [Real.cos_sq, show 2 * (a + y * 2⁻¹) = 2 * a + y by ring]
  ring

theorem powCosSq_complex : powCosSq.Holds .complex := by
  refine powCosSq_holds Interp.complex two_ne_zero fun a y => ?_
  simp only [Interp.complex]
  rw [Complex.cos_sq, show 2 * (a + y * 2⁻¹) = 2 * a + y by ring]
  ring

/-- **Counterexample** to `logPowLog`, for an interpretation with `ln` defined
at `1` and `ln 1 = 0`: at `c = d = 1`, `n = p = 0` the integrand `log(1)` is
defined everywhere, but the residual integrand `1/log(d x^n)` is not. -/
theorem logPowLog_not (I : Interp 𝕜) (h1 : I.lnDefined 1) (h0 : I.ln 1 = 0) :
    ¬ AntiderivRecHolds I "x" logPowLog.conditions logPowLog.body logPowLog.result
      logPowLog.integrals := by
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" ∨ s = "d" then 1 else 0) 1
    (by simp [logPowLog]) (Eventually.of_forall fun _ => ?_) ?_
  · simp [logPowLog, Defined, eval, toInt?_zero, h1]
  · simp only [logPowLog, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]
    intro h
    simp only [Defined, eval, Interp.toInt?_cast] at h
    simp [toInt?_zero, h0] at h

theorem logPowLog_counterexample_real : ¬ logPowLog.Holds .real :=
  logPowLog_not Interp.real (show (0 : ℝ) < 1 from one_pos) Real.log_one

theorem logPowLog_counterexample_complex : ¬ logPowLog.Holds .complex :=
  logPowLog_not Interp.complex (show (1 : ℂ) ≠ 0 from one_ne_zero) Complex.log_one

/-- **Counterexample** to `sinXLog` (and `cosXLog` below): at `a = 0`, `b = 1`
the integrand is defined near `1`, but `a^(-1)` is not. -/
theorem sinXLog_not (I : Interp 𝕜) (hnear : ∀ᶠ w in 𝓝 (1 : 𝕜), I.lnDefined w) :
    ¬ AntiderivRecHolds I "x" sinXLog.conditions sinXLog.body sinXLog.result
      sinXLog.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" then 1 else 0) 1
    (by simp [sinXLog]) ?_ (fun _ w => w * eval I (Function.update
      (fun s => if s = "b" then 1 else 0) "x" 1) (sin xLog)) ?_ ?_
  · filter_upwards [hnear] with w hw
    simp [sinXLog, Defined, eval, hw]
  · simp only [sinXLog, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [sinXLog, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem sinXLog_counterexample_real : ¬ sinXLog.Holds .real :=
  sinXLog_not Interp.real (lt_mem_nhds one_pos)

theorem sinXLog_counterexample_complex : ¬ sinXLog.Holds .complex :=
  sinXLog_not Interp.complex (eventually_ne_nhds one_ne_zero)

theorem cosXLog_not (I : Interp 𝕜) (hnear : ∀ᶠ w in 𝓝 (1 : 𝕜), I.lnDefined w) :
    ¬ AntiderivRecHolds I "x" cosXLog.conditions cosXLog.body cosXLog.result
      cosXLog.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "b" then 1 else 0) 1
    (by simp [cosXLog]) ?_ (fun _ w => w * eval I (Function.update
      (fun s => if s = "b" then 1 else 0) "x" 1) (cos xLog)) ?_ ?_
  · filter_upwards [hnear] with w hw
    simp [cosXLog, Defined, eval, hw]
  · simp only [cosXLog, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact hasDerivAt_mul_const _
  · intro h
    simp only [cosXLog, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem cosXLog_counterexample_real : ¬ cosXLog.Holds .real :=
  cosXLog_not Interp.real (lt_mem_nhds one_pos)

theorem cosXLog_counterexample_complex : ¬ cosXLog.Holds .complex :=
  cosXLog_not Interp.complex (eventually_ne_nhds one_ne_zero)

/-- **Counterexample** to `linearQuadPow`: at `a = 1` and the other
metavariables `0` the condition `p ≠ -1` holds and the integrand is defined
everywhere, but `(2 c (p + 1))^(-1)` is not. -/
theorem linearQuadPow_not (I : Interp 𝕜) :
    ¬ AntiderivRecHolds I "x" linearQuadPow.conditions linearQuadPow.body linearQuadPow.result
      linearQuadPow.integrals := by
  refine not_antiderivRecHolds_result (fun s => if s = "a" then 1 else 0) 0
    (by simp [linearQuadPow, Cond.Holds, Defined, eval]) (Eventually.of_forall fun _ => ?_)
    (fun _ w => w * 1) ?_ ?_
  · simp [linearQuadPow, Defined, eval, toInt?_zero, toInt?_two]
  · simp only [linearQuadPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    simpa [eval, toInt?_zero, toInt?_two] using hasDerivAt_mul_const (1 : 𝕜)
  · intro h
    simp only [linearQuadPow, Defined, eval, Interp.toInt?_cast] at h
    simp [recEnv] at h

theorem linearQuadPow_counterexample_real : ¬ linearQuadPow.Holds .real :=
  linearQuadPow_not Interp.real

theorem linearQuadPow_counterexample_complex : ¬ linearQuadPow.Holds .complex :=
  linearQuadPow_not Interp.complex

end Proofs

/-- Integration by parts reduces `(a + b log(c x^n))^p` over ℝ, for every
integer `p > 0` (the fragment interprets `arith1#power` for integer exponents
only). -/
theorem logLinPow_real : logLinPow.Holds .real := by
  show AntiderivRecHolds Interp.real "x" logLinPow.conditions logLinPow.body logLinPow.result
    logLinPow.integrals
  intro env hc t hF
  have hp0 : 0 < env "p" := by
    have h := hc (.gt (v "p") (.int 0)) (by simp [logLinPow])
    simpa [Cond.Holds, Defined, eval, Interp.real] using h
  rcases hk : intValue? (env "p") with _ | p
  · exfalso
    have h := hF.self_of_nhds
    simp [logLinPow, Defined, eval, Interp.real, hk] at h
  rcases hkn : intValue? (env "n") with _ | n
  · exfalso
    have h := hF.self_of_nhds
    simp [logLinPow, Defined, eval, Interp.real, hkn] at h
  have hpk : env "p" = p := (intValue?_eq _ _).1 hk
  have hnk : env "n" = n := (intValue?_eq _ _).1 hkn
  have hp1 : 1 ≤ p := by
    have : (0 : ℝ) < p := hpk ▸ hp0
    exact_mod_cast this
  have hkm : intValue? (env "p" + -1) = some (p - 1) := by
    rw [intValue?_eq, hpk]; push_cast; ring
  have hD : ∀ w, Defined Interp.real (Function.update env "x" w) logLinPow.body ↔
      (n < 0 → w ≠ 0) ∧ 0 < env "c" * w ^ n := by
    intro w
    have : ¬ p < 0 := by omega
    simp [logLinPow, Defined, eval, Interp.real, hk, hkn, this]
  have hpos := ((hD t).1 hF.self_of_nhds).2
  have hn0 := ((hD t).1 hF.self_of_nhds).1
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [logLinPow, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have h := (hD w).1 hw
    have : ¬ p - 1 < 0 := by omega
    simp [Defined, eval, Interp.real, hkn, hkm, this]
    exact h
  · filter_upwards [hF] with w hw
    have h := (hD w).1 hw
    have : ¬ p < 0 := by omega
    simp [logLinPow, Defined, eval, Interp.real, recEnv, hk, hkn, this]
    exact h
  · simp only [logLinPow, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hne : t ≠ 0 ∨ 0 ≤ n := by
      by_cases h : n < 0
      · exact Or.inl (hn0 h)
      · exact Or.inr (by omega)
    have hA := ((((hasDerivAt_zpow n t hne).const_mul (env "c")).log hpos.ne').const_mul
      (env "b")).const_add (env "a")
    have hAp := (hasDerivAt_zpow p _ (Or.inr (by omega))).comp t hA
    have h := ((hasDerivAt_id' t).mul hAp).add (hΦ.const_mul (-1 * env "b" * env "n" * env "p"))
    have hfun : (fun w => eval Interp.real (recEnv env (logLinPow.integrals.map (·.1)) Φ "x" w)
        logLinPow.result) = fun w =>
          w * ((fun y => y ^ p) ∘ fun w => env "a" + env "b" * Real.log (env "c" * w ^ n)) w +
            -1 * env "b" * env "n" * env "p" * Φ "I1" w := by
      funext w
      simp [logLinPow, eval, Interp.real, recEnv, hk, hkn]
    have hval : eval Interp.real (Function.update env "x" t) logLinPow.body =
        (env "a" + env "b" * Real.log (env "c" * t ^ n)) ^ p := by
      simp [logLinPow, eval, Interp.real, hk, hkn]
    rw [hfun, hval]
    refine h.congr_deriv ?_
    simp only [Function.comp, eval, Interp.real, Function.update_self, Function.update_apply]
    simp [hkn, hkm]
    rw [hnk, hpk]
    rcases eq_or_ne n 0 with rfl | hn1
    · simp
    · have ht : t ≠ 0 := by
        rcases hne with h | h
        · exact h
        · intro h0
          subst h0
          rw [zero_zpow n hn1, mul_zero] at hpos
          exact lt_irrefl 0 hpos
      have hc : env "c" ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hpos
        exact lt_irrefl 0 hpos
      have hz : t ^ n ≠ 0 := zpow_ne_zero n ht
      rw [zpow_sub_one₀ ht]
      field_simp
      ring

end OSR.IntegrationRec
