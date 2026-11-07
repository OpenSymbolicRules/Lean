import OSR.Catalog
import OSR.OMObject

/-!
# Calculus

Migration of `OpenSymbolicRules/Calculus` at commit
`eb9eb87aa7ffcd6dd7da055fa6b6d87f35f840da`: 29 of its 32 rules (the other 3
use the invented `osr#Apply`).  v0.1 `FreeQ` becomes an independence
constraint (`CRule.independent`); the v0.1 power rule is refuted
(`derivPow_counterexample`).

A calculus rule has one of two shapes, with `F`, `G`, `L` field expressions:

* `diff(λx. F) ⟶ λx. G` (`calculus1#diff`, `fns1#lambda`): wherever `F` is
  defined on a neighbourhood of `t`, the function `v ↦ F[x := v]` has
  derivative `G[x := t]` at `t` (`HasDerivAt`), and `G` is defined there;
* `limit(a, both_sides, λx. F) ⟶ L` (`limit1#limit`, `limit1#both_sides`):
  `F[x := v]` tends to `L` as `v` tends to `a` with `v ≠ a` (`Tendsto` along
  `𝓝[≠] a`), and `L` is defined.

`x` is the only variable of `F` and `G`, so instantiating a rule only renames
the bound variable (`deriv_instance`, `limit_instance`).
-/

namespace OSR.Calculus

open OSR Filter Topology

/-- The two shapes of a calculus rule. -/
inductive Shape where
  | deriv
  | limit
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A calculus rule. -/
structure CRule where
  id : String
  legacyId : Option String := none
  shape : Shape
  /-- The bound variable of the lambda. -/
  x : String
  /-- Body of the lambda in the pattern. -/
  body : Expr
  /-- Limit point (limits only). -/
  point : Expr := .int 0
  /-- Body of the resulting lambda (derivatives) or the limit value. -/
  result : Expr
  priority : Nat
  description : String
  provenance : Provenance
  /-- Metavariables whose match must not mention the bound variable (v0.1
  `FreeQ`, an `independent` matching constraint). -/
  independent : List String := []
  deriving Repr, Inhabited, BEq

def diffSymbol : OMSymbol := ⟨"calculus1", "diff"⟩
def lambdaSymbol : OMSymbol := ⟨"fns1", "lambda"⟩
def limitSymbol : OMSymbol := ⟨"limit1", "limit"⟩
def bothSidesSymbol : OMSymbol := ⟨"limit1", "both_sides"⟩

/-- `λx. e` as an OpenMath object. -/
def lamOM (x : String) (e : Expr) : OMObj := .ombind lambdaSymbol [x] e.toOM

/-- The pattern as an OpenMath object. -/
def CRule.patternOM (r : CRule) : OMObj :=
  match r.shape with
  | .deriv => .oma diffSymbol [lamOM r.x r.body]
  | .limit => .oma limitSymbol [r.point.toOM, .oms bothSidesSymbol, lamOM r.x r.body]

/-- The replacement as an OpenMath object. -/
def CRule.replacementOM (r : CRule) : OMObj :=
  match r.shape with
  | .deriv => lamOM r.x r.result
  | .limit => r.result.toOM

def CRule.symbols (r : CRule) : List OMSymbol :=
  let shape := match r.shape with
    | .deriv => [diffSymbol, lambdaSymbol]
    | .limit => [limitSymbol, bothSidesSymbol, lambdaSymbol]
  (shape ++ r.point.symbols.filter (fun _ => r.shape == .limit) ++ r.body.symbols ++
    r.result.symbols).eraseDups

/-- Well-formedness: the body only mentions the bound variable and
independent metavariables, the result only variables of the body, and the
bound variable is not a metavariable of the point. -/
def CRule.wellFormed (r : CRule) : Bool :=
  r.body.varList.all (fun n => n = r.x ∨ n ∈ r.independent) &&
    r.result.varList.all (fun n => n = r.x ∨ n ∈ r.body.varList) &&
    !(r.point.varList.contains r.x) && !(r.independent.contains r.x)

/-! ## Statements -/

section Statements

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- `diff(λx. F) = λx. G` in the interpretation `I`. -/
def DerivHolds (I : Interp 𝕜) (x : String) (F G : Expr) : Prop :=
  ∀ (env : String → 𝕜) (t : 𝕜),
    (∀ᶠ v in 𝓝 t, Defined I (Function.update env x v) F) →
      Defined I (Function.update env x t) G ∧
        HasDerivAt (fun v => eval I (Function.update env x v) F)
          (eval I (Function.update env x t) G) t

/-- `limit(a, both_sides, λx. F) = L` in the interpretation `I`. -/
def LimitHolds (I : Interp 𝕜) (x : String) (a F L : Expr) : Prop :=
  ∀ env : String → 𝕜,
    (∀ᶠ v in 𝓝[≠] (eval I env a), Defined I (Function.update env x v) F) →
    Defined I env L ∧
      Tendsto (fun v => eval I (Function.update env x v) F) (𝓝[≠] (eval I env a))
        (𝓝 (eval I env L))

end Statements

/-- The certified statement of a calculus rule in a domain. -/
def CRule.Holds (r : CRule) : Domain → Prop
  | .real => match r.shape with
    | .deriv => DerivHolds Interp.real r.x r.body r.result
    | .limit => LimitHolds Interp.real r.x r.point r.body r.result
  | .complex => match r.shape with
    | .deriv => DerivHolds Interp.complex r.x r.body r.result
    | .limit => LimitHolds Interp.complex r.x r.point r.body r.result
  | .boolean => False

/-! ## Rules -/

private abbrev x : Expr := .var "x"
private abbrev sin (e : Expr) : Expr := .app1 .sin e
private abbrev cos (e : Expr) : Expr := .app1 .cos e
private abbrev tan (e : Expr) : Expr := .app1 .tan e
private abbrev exp (e : Expr) : Expr := .app1 .exp e
private abbrev ln (e : Expr) : Expr := .app1 .ln e
private abbrev arctan (e : Expr) : Expr := .app1 .arctan e
private abbrev f1 (o : Op1) (e : Expr) : Expr := .app1 o e
private abbrev root2 (e : Expr) : Expr := .app2 .root e (.int 2)
private abbrev mone : Expr := .int (-1)
private abbrev add (a b : Expr) : Expr := .app2 .add a b
private abbrev sub (a b : Expr) : Expr := .app2 .sub a b
private abbrev mul (a b : Expr) : Expr := .app2 .mul a b
private abbrev div (a b : Expr) : Expr := .app2 .div a b
private abbrev sq (e : Expr) : Expr := .pow e (.int 2)
private abbrev one : Expr := .int 1

private def repo : String := "OpenSymbolicRules/Calculus"
private def rev : String := "eb9eb87aa7ffcd6dd7da055fa6b6d87f35f840da"

private def migrated (legacy : String) : Provenance :=
  { method := .derived,
    sources := [{ name := repo, locator := legacy, revision := some rev, license := some "MIT" }] }

private def elem (n : Nat) : String := s!"calculus:2-derivatives/2.2-elementary-derivatives:{n}"
private def lim (n : Nat) : String := s!"calculus:1-limits/1.1-basic-limits:{n}"

def derivId : CRule where
  id := "calculus.derivative.id"; legacyId := some (elem 1); shape := .deriv; x := "x"
  body := x; result := one; priority := 110
  description := "Derivative of the identity"; provenance := migrated (elem 1)

def derivSin : CRule where
  id := "calculus.derivative.sin"; legacyId := some (elem 2); shape := .deriv; x := "x"
  body := sin x; result := cos x; priority := 120
  description := "Derivative of sine"; provenance := migrated (elem 2)

def derivCos : CRule where
  id := "calculus.derivative.cos"; legacyId := some (elem 3); shape := .deriv; x := "x"
  body := cos x; result := mul (.int (-1)) (sin x); priority := 130
  description := "Derivative of cosine"; provenance := migrated (elem 3)

def derivExp : CRule where
  id := "calculus.derivative.exp"; legacyId := some (elem 4); shape := .deriv; x := "x"
  body := exp x; result := exp x; priority := 140
  description := "Derivative of the exponential"; provenance := migrated (elem 4)

def derivLn : CRule where
  id := "calculus.derivative.ln"; legacyId := some (elem 5); shape := .deriv; x := "x"
  body := ln x; result := div one x; priority := 150
  description := "Derivative of the natural logarithm"; provenance := migrated (elem 5)

def derivTan : CRule where
  id := "calculus.derivative.tan"; legacyId := some (elem 6); shape := .deriv; x := "x"
  body := tan x; result := div one (sq (cos x)); priority := 160
  description := "Derivative of tangent"; provenance := migrated (elem 6)

def derivArctan : CRule where
  id := "calculus.derivative.arctan"; legacyId := some (elem 10); shape := .deriv; x := "x"
  body := arctan x; result := div one (add one (sq x)); priority := 200
  description := "Derivative of the inverse tangent"; provenance := migrated (elem 10)

def limitSinDiv : CRule where
  id := "calculus.limit.sin_div"; legacyId := some (lim 2); shape := .limit; x := "x"
  body := div (sin x) x; result := one; priority := 20
  description := "Limit of sin(x)/x at 0"; provenance := migrated (lim 2)

def limitTanDiv : CRule where
  id := "calculus.limit.tan_div"; legacyId := some (lim 3); shape := .limit; x := "x"
  body := div (tan x) x; result := one; priority := 30
  description := "Limit of tan(x)/x at 0"; provenance := migrated (lim 3)

def limitOneSubCos : CRule where
  id := "calculus.limit.one_sub_cos_div_sq"; legacyId := some (lim 4); shape := .limit; x := "x"
  body := div (sub one (cos x)) (sq x); result := div one (.int 2); priority := 40
  description := "Limit of (1 - cos(x))/x^2 at 0"; provenance := migrated (lim 4)

def limitExpSub : CRule where
  id := "calculus.limit.exp_sub_one_div"; legacyId := some (lim 5); shape := .limit; x := "x"
  body := div (sub (exp x) one) x; result := one; priority := 50
  description := "Limit of (exp(x) - 1)/x at 0"; provenance := migrated (lim 5)

def limitLogAdd : CRule where
  id := "calculus.limit.log_one_add_div"; legacyId := some (lim 6); shape := .limit; x := "x"
  body := div (ln (add one x)) x; result := one; priority := 60
  description := "Limit of log(1 + x)/x at 0"; provenance := migrated (lim 6)


def derivSinh : CRule where
  id := "calculus.derivative.sinh"; legacyId := some (elem 7); shape := .deriv; x := "x"
  body := f1 .sinh x; result := f1 .cosh x; priority := 170
  description := "Derivative of the hyperbolic sine"; provenance := migrated (elem 7)

def derivCosh : CRule where
  id := "calculus.derivative.cosh"; legacyId := some (elem 8); shape := .deriv; x := "x"
  body := f1 .cosh x; result := f1 .sinh x; priority := 180
  description := "Derivative of the hyperbolic cosine"; provenance := migrated (elem 8)

def derivTanh : CRule where
  id := "calculus.derivative.tanh"; legacyId := some (elem 9); shape := .deriv; x := "x"
  body := f1 .tanh x; result := div one (sq (f1 .cosh x)); priority := 190
  description := "Derivative of the hyperbolic tangent"; provenance := migrated (elem 9)

def derivArctanh : CRule where
  id := "calculus.derivative.arctanh"; legacyId := some (elem 11); shape := .deriv; x := "x"
  body := f1 .arctanh x; result := div one (sub one (sq x)); priority := 210
  description := "Derivative of the inverse hyperbolic tangent"; provenance := migrated (elem 11)

def derivArcsin : CRule where
  id := "calculus.derivative.arcsin"; legacyId := some (elem 12); shape := .deriv; x := "x"
  body := f1 .arcsin x; result := div one (root2 (sub one (sq x))); priority := 220
  description := "Derivative of the inverse sine"; provenance := migrated (elem 12)

def derivArccos : CRule where
  id := "calculus.derivative.arccos"; legacyId := some (elem 13); shape := .deriv; x := "x"
  body := f1 .arccos x; result := div mone (root2 (sub one (sq x))); priority := 230
  description := "Derivative of the inverse cosine"; provenance := migrated (elem 13)

def derivCot : CRule where
  id := "calculus.derivative.cot"; legacyId := some (elem 14); shape := .deriv; x := "x"
  body := f1 .cot x; result := div mone (sq (sin x)); priority := 240
  description := "Derivative of cotangent"; provenance := migrated (elem 14)

def derivSec : CRule where
  id := "calculus.derivative.sec"; legacyId := some (elem 15); shape := .deriv; x := "x"
  body := f1 .sec x; result := mul (f1 .sec x) (tan x); priority := 250
  description := "Derivative of secant"; provenance := migrated (elem 15)

def derivCsc : CRule where
  id := "calculus.derivative.csc"; legacyId := some (elem 16); shape := .deriv; x := "x"
  body := f1 .csc x; result := mul (mul mone (f1 .csc x)) (f1 .cot x); priority := 260
  description := "Derivative of cosecant"; provenance := migrated (elem 16)

def derivCoth : CRule where
  id := "calculus.derivative.coth"; legacyId := some (elem 17); shape := .deriv; x := "x"
  body := f1 .coth x; result := div mone (sq (f1 .sinh x)); priority := 270
  description := "Derivative of the hyperbolic cotangent"; provenance := migrated (elem 17)

def derivSech : CRule where
  id := "calculus.derivative.sech"; legacyId := some (elem 18); shape := .deriv; x := "x"
  body := f1 .sech x; result := mul (mul mone (f1 .sech x)) (f1 .tanh x); priority := 280
  description := "Derivative of the hyperbolic secant"; provenance := migrated (elem 18)

def derivCsch : CRule where
  id := "calculus.derivative.csch"; legacyId := some (elem 19); shape := .deriv; x := "x"
  body := f1 .csch x; result := mul (mul mone (f1 .csch x)) (f1 .coth x); priority := 290
  description := "Derivative of the hyperbolic cosecant"; provenance := migrated (elem 19)

def derivArcsinh : CRule where
  id := "calculus.derivative.arcsinh"; legacyId := some (elem 20); shape := .deriv; x := "x"
  body := f1 .arcsinh x; result := div one (root2 (add one (sq x))); priority := 300
  description := "Derivative of the inverse hyperbolic sine"; provenance := migrated (elem 20)

def derivArccosh : CRule where
  id := "calculus.derivative.arccosh"; legacyId := some (elem 21); shape := .deriv; x := "x"
  body := f1 .arccosh x; result := div one (root2 (sub (sq x) one)); priority := 310
  description := "Derivative of the inverse hyperbolic cosine"; provenance := migrated (elem 21)


private def basic (n : Nat) : String := s!"calculus:2-derivatives/2.1-basic-derivatives:{n}"

/-- `limit(a, both_sides, λx. c) ⟶ c` for `c` free of `x`. -/
def limitConst : CRule where
  id := "calculus.limit.const"; legacyId := some (lim 1); shape := .limit; x := "x"
  point := .var "a"; body := .var "c"; result := .var "c"; independent := ["c"]; priority := 10
  description := "Limit of a constant"; provenance := migrated (lim 1)

/-- `diff(λx. c) ⟶ λx. 0` for `c` free of `x`. -/
def derivConst : CRule where
  id := "calculus.derivative.const"; legacyId := some (basic 1); shape := .deriv; x := "x"
  body := .var "c"; result := .int 0; independent := ["c"]; priority := 70
  description := "Derivative of a constant"; provenance := migrated (basic 1)

/-- `diff(λx. x^n) ⟶ λx. n x^(n - 1)` for `n` free of `x`: false at `n = 0`,
`x = 0` (`derivPow_counterexample`). -/
def derivPow : CRule where
  id := "calculus.derivative.power"; legacyId := some (basic 2); shape := .deriv; x := "x"
  body := .pow x (.var "n"); result := mul (.var "n") (.pow x (add (.var "n") (.int (-1))))
  independent := ["n"]; priority := 80
  description := "Power rule"; provenance := migrated (basic 2)

/-- v0.1 rules outside the fragment, with the reason. -/
def notMigrated : List (String × String) :=
  ([1, 2, 3].map fun n =>
    (s!"calculus:2-derivatives/2.3-structural-derivatives:{n}",
      "uses osr#Apply, which is not an OpenMath symbol"))

/-! ## Proofs -/

/-- Unfold a derivative statement over `I`: introduce `env`, `t` and the
definedness hypothesis `hF`, and evaluate. -/
local macro "deriv_intro" r:ident i:ident : tactic => do
  let hF := Lean.mkIdent `hF
  let t := Lean.mkIdent `t
  let env := Lean.mkIdent `env
  `(tactic|
    (simp only [CRule.Holds, $r:ident, DerivHolds]
     intro $env:ident $t:ident $hF:ident
     simp only [Defined, eval, $i:ident, Function.update_self, intValue?_intCast] at $hF:ident ⊢
     simp only [Int.cast_one, Int.cast_neg, Int.cast_ofNat, zpow_ofNat, Option.some.injEq,
       exists_eq_left', Int.reduceLT, false_implies, true_and, and_true] at $hF:ident ⊢))

theorem derivId_real : derivId.Holds .real := by
  deriv_intro derivId Interp.real
  exact hasDerivAt_id' t

theorem derivId_complex : derivId.Holds .complex := by
  deriv_intro derivId Interp.complex
  exact hasDerivAt_id' t

theorem derivSin_real : derivSin.Holds .real := by
  deriv_intro derivSin Interp.real
  exact Real.hasDerivAt_sin t

theorem derivSin_complex : derivSin.Holds .complex := by
  deriv_intro derivSin Interp.complex
  exact Complex.hasDerivAt_sin t

theorem derivCos_real : derivCos.Holds .real := by
  deriv_intro derivCos Interp.real
  exact (Real.hasDerivAt_cos t).congr_deriv (by ring)

theorem derivCos_complex : derivCos.Holds .complex := by
  deriv_intro derivCos Interp.complex
  exact (Complex.hasDerivAt_cos t).congr_deriv (by ring)

theorem derivExp_real : derivExp.Holds .real := by
  deriv_intro derivExp Interp.real
  exact Real.hasDerivAt_exp t

theorem derivExp_complex : derivExp.Holds .complex := by
  deriv_intro derivExp Interp.complex
  exact Complex.hasDerivAt_exp t

theorem derivLn_real : derivLn.Holds .real := by
  deriv_intro derivLn Interp.real
  have ht : 0 < t := hF.self_of_nhds
  exact ⟨ht.ne', (Real.hasDerivAt_log ht.ne').congr_deriv (one_div t).symm⟩

theorem derivTan_real : derivTan.Holds .real := by
  deriv_intro derivTan Interp.real
  have ht : Real.cos t ≠ 0 := hF.self_of_nhds
  exact ⟨pow_ne_zero 2 ht, Real.hasDerivAt_tan ht⟩

theorem derivTan_complex : derivTan.Holds .complex := by
  deriv_intro derivTan Interp.complex
  have ht : Complex.cos t ≠ 0 := hF.self_of_nhds
  exact ⟨pow_ne_zero 2 ht, Complex.hasDerivAt_tan ht⟩

theorem derivArctan_real : derivArctan.Holds .real := by
  deriv_intro derivArctan Interp.real
  exact ⟨by positivity, Real.hasDerivAt_arctan t⟩

/-- Unfold a limit statement over `I`. -/
local macro "limit_intro" r:ident i:ident : tactic =>
  `(tactic|
    (simp only [CRule.Holds, $r:ident, LimitHolds]
     intro env _
     simp only [Defined, eval, $i:ident, Function.update_self, intValue?_intCast]
     simp only [Int.cast_one, Int.cast_zero, Int.cast_ofNat, zpow_ofNat, Option.some.injEq,
       exists_eq_left', Int.reduceLT, false_implies, true_and, and_true]))

/-- The slope of `f` at `0` tends to `f'(0)`, written as `(f v - f 0) / v`. -/
private theorem slope_div {𝕜 : Type} [NontriviallyNormedField 𝕜] {f : 𝕜 → 𝕜} {f' : 𝕜}
    (h : HasDerivAt f f' 0) : Tendsto (fun v => (f v - f 0) / v) (𝓝[≠] 0) (𝓝 f') := by
  have := h.tendsto_slope_zero
  simp only [zero_add, smul_eq_mul] at this
  exact this.congr fun v => by rw [div_eq_inv_mul]

theorem limitSinDiv_real : limitSinDiv.Holds .real := by
  limit_intro limitSinDiv Interp.real
  simpa using slope_div (Real.hasDerivAt_sin 0)

theorem limitSinDiv_complex : limitSinDiv.Holds .complex := by
  limit_intro limitSinDiv Interp.complex
  simpa using slope_div (Complex.hasDerivAt_sin 0)

theorem limitTanDiv_real : limitTanDiv.Holds .real := by
  limit_intro limitTanDiv Interp.real
  simpa using slope_div (Real.hasDerivAt_tan (by simp : Real.cos 0 ≠ 0))

theorem limitTanDiv_complex : limitTanDiv.Holds .complex := by
  limit_intro limitTanDiv Interp.complex
  simpa using slope_div (Complex.hasDerivAt_tan (by simp : Complex.cos 0 ≠ 0))

theorem limitExpSub_real : limitExpSub.Holds .real := by
  limit_intro limitExpSub Interp.real
  simpa using slope_div (Real.hasDerivAt_exp 0)

theorem limitExpSub_complex : limitExpSub.Holds .complex := by
  limit_intro limitExpSub Interp.complex
  simpa using slope_div (Complex.hasDerivAt_exp 0)

theorem limitLogAdd_real : limitLogAdd.Holds .real := by
  limit_intro limitLogAdd Interp.real
  have h : HasDerivAt (fun v : ℝ => Real.log (1 + v)) 1 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).const_add 1).log (by norm_num)
    simpa using this
  simpa using slope_div h

theorem limitOneSubCos_real : limitOneSubCos.Holds .real := by
  limit_intro limitOneSubCos Interp.real
  have h1 : Tendsto (fun v : ℝ => Real.sin v / v) (𝓝[≠] 0) (𝓝 1) := by
    simpa using slope_div (Real.hasDerivAt_sin 0)
  have h2 : Tendsto (fun v : ℝ => v / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_id.div_const (2 : ℝ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with v hv
      simpa using hv
  have h3 := ((h1.comp h2).pow 2).const_mul (1 / 2 : ℝ)
  simp only [one_pow, mul_one] at h3
  refine ⟨by norm_num, h3.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv : v ≠ 0 := hv
  have hc : Real.cos v = 1 - 2 * Real.sin (v / 2) ^ 2 := by
    have h := Real.cos_two_mul (v / 2)
    have h' := Real.sin_sq_add_cos_sq (v / 2)
    rw [show 2 * (v / 2) = v by ring] at h
    linarith
  simp only [Function.comp, hc]
  field_simp
  ring

theorem limitLogAdd_complex : limitLogAdd.Holds .complex := by
  limit_intro limitLogAdd Interp.complex
  have h : HasDerivAt (fun v : ℂ => Complex.log (1 + v)) 1 0 := by
    have := ((hasDerivAt_id' (0 : ℂ)).const_add 1).clog (by simp)
    simpa using this
  simpa using slope_div h

theorem limitOneSubCos_complex : limitOneSubCos.Holds .complex := by
  limit_intro limitOneSubCos Interp.complex
  have h1 : Tendsto (fun v : ℂ => Complex.sin v / v) (𝓝[≠] 0) (𝓝 1) := by
    simpa using slope_div (Complex.hasDerivAt_sin 0)
  have h2 : Tendsto (fun v : ℂ => v / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_id.div_const (2 : ℂ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with v hv
      simpa using hv
  have h3 := ((h1.comp h2).pow 2).const_mul (1 / 2 : ℂ)
  simp only [one_pow, mul_one] at h3
  refine ⟨by norm_num, h3.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv : v ≠ 0 := hv
  have hc : Complex.cos v = 1 - 2 * Complex.sin (v / 2) ^ 2 := by
    have h := Complex.cos_two_mul (v / 2)
    have h' := Complex.sin_sq_add_cos_sq (v / 2)
    rw [show 2 * (v / 2) = v by ring] at h
    linear_combination h + 2 * h'
  simp only [Function.comp, hc]
  field_simp
  ring


/-! ### Hyperbolic, reciprocal and inverse functions -/

private theorem ne_of_eventually_le {t c : ℝ} (h : ∀ᶠ v in 𝓝 t, v ≤ c) : t ≠ c := by
  rintro rfl
  obtain ⟨v, hv, hlt⟩ := (h.and_frequently (frequently_gt_nhds t)).exists
  linarith

private theorem ne_of_eventually_ge {t c : ℝ} (h : ∀ᶠ v in 𝓝 t, c ≤ v) : t ≠ c := by
  rintro rfl
  obtain ⟨v, hv, hlt⟩ := (h.and_frequently (frequently_lt_nhds t)).exists
  linarith

theorem derivSinh_real : derivSinh.Holds .real := by
  deriv_intro derivSinh Interp.real
  exact Real.hasDerivAt_sinh t

theorem derivSinh_complex : derivSinh.Holds .complex := by
  deriv_intro derivSinh Interp.complex
  exact Complex.hasDerivAt_sinh t

theorem derivCosh_real : derivCosh.Holds .real := by
  deriv_intro derivCosh Interp.real
  exact Real.hasDerivAt_cosh t

theorem derivCosh_complex : derivCosh.Holds .complex := by
  deriv_intro derivCosh Interp.complex
  exact Complex.hasDerivAt_cosh t

theorem derivTanh_real : derivTanh.Holds .real := by
  deriv_intro derivTanh Interp.real
  have hc : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  refine ⟨pow_ne_zero 2 hc, ?_⟩
  have h := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) hc
  have hf : Real.sinh / Real.cosh = Real.tanh := by
    funext v; simp [Real.tanh_eq_sinh_div_cosh]
  rw [hf] at h
  refine h.congr_deriv ?_
  have := Real.cosh_sq_sub_sinh_sq t
  field_simp
  linear_combination this

theorem derivArcsin_real : derivArcsin.Holds .real := by
  deriv_intro derivArcsin Interp.real
  have h1 : t ≠ 1 := ne_of_eventually_le (hF.mono fun v h => h.2)
  have h2 : t ≠ -1 := ne_of_eventually_ge (hF.mono fun v h => h.1)
  have hle := hF.self_of_nhds
  have hpos : 0 < 1 - t ^ 2 := by
    have : t < 1 := lt_of_le_of_ne hle.2 h1
    have : -1 < t := lt_of_le_of_ne hle.1 (Ne.symm h2)
    nlinarith
  refine ⟨⟨hpos.le, (Real.sqrt_pos.2 hpos).ne'⟩, ?_⟩
  exact Real.hasDerivAt_arcsin h2 h1

theorem derivArccos_real : derivArccos.Holds .real := by
  deriv_intro derivArccos Interp.real
  have h1 : t ≠ 1 := ne_of_eventually_le (hF.mono fun v h => h.2)
  have h2 : t ≠ -1 := ne_of_eventually_ge (hF.mono fun v h => h.1)
  have hle := hF.self_of_nhds
  have hpos : 0 < 1 - t ^ 2 := by
    have : t < 1 := lt_of_le_of_ne hle.2 h1
    have : -1 < t := lt_of_le_of_ne hle.1 (Ne.symm h2)
    nlinarith
  refine ⟨⟨hpos.le, (Real.sqrt_pos.2 hpos).ne'⟩, ?_⟩
  exact (Real.hasDerivAt_arccos h2 h1).congr_deriv (by ring)

theorem derivCot_real : derivCot.Holds .real := by
  deriv_intro derivCot Interp.real
  have hs : Real.sin t ≠ 0 := hF.self_of_nhds
  refine ⟨pow_ne_zero 2 hs, ?_⟩
  have h := (Real.hasDerivAt_cos t).div (Real.hasDerivAt_sin t) hs
  have hf : Real.cos / Real.sin = Real.cot := by
    funext v; simp [Real.cot_eq_cos_div_sin]
  rw [hf] at h
  refine h.congr_deriv ?_
  have := Real.sin_sq_add_cos_sq t
  field_simp
  linear_combination -this

theorem derivCot_complex : derivCot.Holds .complex := by
  deriv_intro derivCot Interp.complex
  have hs : Complex.sin t ≠ 0 := hF.self_of_nhds
  refine ⟨pow_ne_zero 2 hs, ?_⟩
  have h := (Complex.hasDerivAt_cos t).div (Complex.hasDerivAt_sin t) hs
  have hf : Complex.cos / Complex.sin = Complex.cot := by
    funext v; simp [Complex.cot_eq_cos_div_sin]
  rw [hf] at h
  refine h.congr_deriv ?_
  have := Complex.sin_sq_add_cos_sq t
  field_simp
  linear_combination -this

theorem derivTanh_complex : derivTanh.Holds .complex := by
  deriv_intro derivTanh Interp.complex
  have hc : Complex.cosh t ≠ 0 := hF.self_of_nhds
  refine ⟨pow_ne_zero 2 hc, ?_⟩
  have h := (Complex.hasDerivAt_sinh t).div (Complex.hasDerivAt_cosh t) hc
  have hf : Complex.sinh / Complex.cosh = Complex.tanh := by
    funext v; simp [Complex.tanh_eq_sinh_div_cosh]
  rw [hf] at h
  refine h.congr_deriv ?_
  have := Complex.cosh_sq_sub_sinh_sq t
  field_simp
  linear_combination this

theorem derivArctanh_real : derivArctanh.Holds .real := by
  deriv_intro derivArctanh Interp.real
  have ht := hF.self_of_nhds
  have hpos : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  refine ⟨hpos.ne', ?_⟩
  have h1 : 0 < 1 + t := by linarith [ht.1]
  have h2 : 0 < 1 - t := by linarith [ht.2]
  -- `artanh v = 1/2 * log ((1 + v) / (1 - v))` near `t`.
  have heq : (fun v => 1 / 2 * Real.log ((1 + v) / (1 - v))) =ᶠ[𝓝 t] Real.artanh := by
    filter_upwards [hF] with v hv
    exact (Real.artanh_eq_half_log ⟨hv.1.le, hv.2.le⟩).symm
  have hg : HasDerivAt (fun v : ℝ => (1 + v) / (1 - v)) (2 / (1 - t) ^ 2) t := by
    have h0 := ((hasDerivAt_id' t).const_add 1).div ((hasDerivAt_id' t).const_sub 1) h2.ne'
    have hfun : ((fun x : ℝ => 1 + x) / fun x => 1 - x) = fun v => (1 + v) / (1 - v) := by
      funext v; rfl
    rw [hfun] at h0
    exact h0.congr_deriv (by ring)
  have hlog := (hg.log (div_pos h1 h2).ne').const_mul (1 / 2 : ℝ)
  refine (hlog.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  field_simp
  ring

/-- `1/f` has derivative `-f'/f²`. -/
private theorem hasDerivAt_one_div {f : ℝ → ℝ} {f' t : ℝ} (h : HasDerivAt f f' t) (hf : f t ≠ 0) :
    HasDerivAt (fun v => 1 / f v) (-f' / f t ^ 2) t := by
  have := (hasDerivAt_const t (1 : ℝ)).div h hf
  exact this.congr_deriv (by ring)

theorem derivSec_real : derivSec.Holds .real := by
  deriv_intro derivSec Interp.real
  have hc : Real.cos t ≠ 0 := hF.self_of_nhds
  refine ⟨⟨hc, hc⟩, ?_⟩
  have h := hasDerivAt_one_div (Real.hasDerivAt_cos t) hc
  refine h.congr_deriv ?_
  simp only [Fn.sec, Real.tan_eq_sin_div_cos]
  field_simp

theorem derivCsc_real : derivCsc.Holds .real := by
  deriv_intro derivCsc Interp.real
  have hs : Real.sin t ≠ 0 := hF.self_of_nhds
  refine ⟨⟨hs, hs⟩, ?_⟩
  have h := hasDerivAt_one_div (Real.hasDerivAt_sin t) hs
  refine h.congr_deriv ?_
  simp only [Fn.csc, Real.cot_eq_cos_div_sin]
  field_simp

theorem derivCoth_real : derivCoth.Holds .real := by
  deriv_intro derivCoth Interp.real
  have hs : Real.sinh t ≠ 0 := hF.self_of_nhds
  refine ⟨pow_ne_zero 2 hs, ?_⟩
  have h := (Real.hasDerivAt_cosh t).div (Real.hasDerivAt_sinh t) hs
  have hf : Real.cosh / Real.sinh = Fn.coth := by
    funext v; simp [Fn.coth, Real.tanh_eq_sinh_div_cosh]
  rw [hf] at h
  refine h.congr_deriv ?_
  have := Real.cosh_sq_sub_sinh_sq t
  field_simp
  linear_combination -this

theorem derivSech_real : derivSech.Holds .real := by
  deriv_intro derivSech Interp.real
  have hc : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  have h := hasDerivAt_one_div (Real.hasDerivAt_cosh t) hc
  refine h.congr_deriv ?_
  simp only [Fn.sech, Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem derivCsch_real : derivCsch.Holds .real := by
  deriv_intro derivCsch Interp.real
  have hs : Real.sinh t ≠ 0 := hF.self_of_nhds
  refine ⟨⟨hs, hs⟩, ?_⟩
  have h := hasDerivAt_one_div (Real.hasDerivAt_sinh t) hs
  refine h.congr_deriv ?_
  simp only [Fn.csch, Fn.coth, Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem derivArcsinh_real : derivArcsinh.Holds .real := by
  deriv_intro derivArcsinh Interp.real
  have hpos : 0 < 1 + t ^ 2 := by positivity
  refine ⟨⟨hpos.le, (Real.sqrt_pos.2 hpos).ne'⟩, ?_⟩
  exact (Real.hasDerivAt_arsinh t).congr_deriv (inv_eq_one_div _)

theorem derivArccosh_real : derivArccosh.Holds .real := by
  deriv_intro derivArccosh Interp.real
  have h1 : 1 < t := lt_of_le_of_ne hF.self_of_nhds (Ne.symm (ne_of_eventually_ge hF))
  have hpos : 0 < t ^ 2 - 1 := by nlinarith
  refine ⟨⟨hpos.le, (Real.sqrt_pos.2 hpos).ne'⟩, ?_⟩
  exact (Real.hasDerivAt_arcosh h1).congr_deriv (inv_eq_one_div _)


/-! ### Rules with independent metavariables -/

theorem limitConst_real : limitConst.Holds .real := by
  simp only [CRule.Holds, limitConst, LimitHolds]
  intro env _
  simp only [Defined, eval, Function.update_apply, show ("c" : String) ≠ "x" by decide, ite_false]
  exact ⟨trivial, tendsto_const_nhds⟩

theorem limitConst_complex : limitConst.Holds .complex := by
  simp only [CRule.Holds, limitConst, LimitHolds]
  intro env _
  simp only [Defined, eval, Function.update_apply, show ("c" : String) ≠ "x" by decide, ite_false]
  exact ⟨trivial, tendsto_const_nhds⟩

theorem derivConst_real : derivConst.Holds .real := by
  simp only [CRule.Holds, derivConst, DerivHolds]
  intro env t _
  simp only [Defined, eval, Function.update_apply, show ("c" : String) ≠ "x" by decide, ite_false,
    Int.cast_zero]
  exact ⟨trivial, hasDerivAt_const t _⟩

theorem derivConst_complex : derivConst.Holds .complex := by
  simp only [CRule.Holds, derivConst, DerivHolds]
  intro env t _
  simp only [Defined, eval, Function.update_apply, show ("c" : String) ≠ "x" by decide, ite_false,
    Int.cast_zero]
  exact ⟨trivial, hasDerivAt_const t _⟩

/-- **Counterexample.**  The v0.1 power rule is false at `n = 0`, `x = 0`:
`x^0` is defined around `0`, but `0 · x^(-1)` is undefined at `0`. -/
theorem derivPow_counterexample : ¬ derivPow.Holds .real := by
  simp only [CRule.Holds, derivPow, DerivHolds]
  intro h
  have hdef : ∀ v : ℝ, Defined Interp.real (Function.update (fun _ => (0 : ℝ)) "x" v)
      (.pow x (.var "n")) := by
    intro v
    simp only [Defined, eval, Interp.real, Function.update_apply,
      show ("n" : String) ≠ "x" by decide, ite_false]
    exact ⟨trivial, trivial, 0, by simpa using intValue?_intCast (α := ℝ) 0, by omega⟩
  obtain ⟨hG, -⟩ := h (fun _ => 0) 0 (Filter.Eventually.of_forall hdef)
  simp only [Defined, eval, Interp.real, Function.update_apply,
    show ("n" : String) ≠ "x" by decide, ite_false, ite_true] at hG
  obtain ⟨-, -, -, k, hk, hne⟩ := hG
  have hk' : k = -1 := by
    have := (intValue?_eq _ _).1 hk
    push_cast at this
    exact_mod_cast this.symm
  exact hne (by omega) rfl

/-! ## Catalogue -/

/-- A calculus rule with its proofs. -/
structure CEntry where
  rule : CRule
  ruleDecl : Lean.Name
  proofs : List (Domain × Lean.Name)
  unproved : List Domain := []
  /-- Theorems refuting `CRule.Holds rule d`, per domain. -/
  counterexamples : List (Domain × Lean.Name) := []
  findings : List String := []
  deriving Repr, Inhabited

private def lnComplexFinding : String :=
  "complex: not proved; ln is defined for z ≠ 0 but the principal logarithm is not differentiable on the negative real axis (its branch cut), so the statement fails there."

private def arctanComplexFinding : String :=
  "complex: not proved; the mapping of transc1#arctan to Complex.arctan is provisional."

/-- The Calculus catalogue (limits, then derivatives, in v0.1 load order). -/
def catalog : List CEntry := [
  { rule := limitConst, ruleDecl := ``limitConst,
    proofs := [(.real, ``limitConst_real), (.complex, ``limitConst_complex)] },
  { rule := derivConst, ruleDecl := ``derivConst,
    proofs := [(.real, ``derivConst_real), (.complex, ``derivConst_complex)] },
  { rule := derivPow, ruleDecl := ``derivPow, proofs := [], unproved := [.complex],
    counterexamples := [(.real, ``derivPow_counterexample)],
    findings := ["counterexample: at n = 0 and x = 0, x^0 is defined around 0 but n * x^(n - 1) = 0 * x^(-1) is undefined at 0, so the v0.1 rule, whose only condition is FreeQ, fails there (Lean theorem derivPow_counterexample). It would hold with the condition n ≠ 0."] },
  { rule := limitSinDiv, ruleDecl := ``limitSinDiv,
    proofs := [(.real, ``limitSinDiv_real), (.complex, ``limitSinDiv_complex)] },
  { rule := limitTanDiv, ruleDecl := ``limitTanDiv,
    proofs := [(.real, ``limitTanDiv_real), (.complex, ``limitTanDiv_complex)] },
  { rule := limitOneSubCos, ruleDecl := ``limitOneSubCos,
    proofs := [(.real, ``limitOneSubCos_real), (.complex, ``limitOneSubCos_complex)] },
  { rule := limitExpSub, ruleDecl := ``limitExpSub,
    proofs := [(.real, ``limitExpSub_real), (.complex, ``limitExpSub_complex)] },
  { rule := limitLogAdd, ruleDecl := ``limitLogAdd,
    proofs := [(.real, ``limitLogAdd_real), (.complex, ``limitLogAdd_complex)] },
  { rule := derivId, ruleDecl := ``derivId,
    proofs := [(.real, ``derivId_real), (.complex, ``derivId_complex)] },
  { rule := derivSin, ruleDecl := ``derivSin,
    proofs := [(.real, ``derivSin_real), (.complex, ``derivSin_complex)] },
  { rule := derivCos, ruleDecl := ``derivCos,
    proofs := [(.real, ``derivCos_real), (.complex, ``derivCos_complex)] },
  { rule := derivExp, ruleDecl := ``derivExp,
    proofs := [(.real, ``derivExp_real), (.complex, ``derivExp_complex)] },
  { rule := derivLn, ruleDecl := ``derivLn,
    proofs := [(.real, ``derivLn_real)], unproved := [.complex], findings := [lnComplexFinding] },
  { rule := derivTan, ruleDecl := ``derivTan,
    proofs := [(.real, ``derivTan_real), (.complex, ``derivTan_complex)] },
  { rule := derivArctan, ruleDecl := ``derivArctan,
    proofs := [(.real, ``derivArctan_real)], unproved := [.complex],
    findings := [arctanComplexFinding] },
  { rule := derivSinh, ruleDecl := ``derivSinh,
    proofs := [(.real, ``derivSinh_real), (.complex, ``derivSinh_complex)] },
  { rule := derivCosh, ruleDecl := ``derivCosh,
    proofs := [(.real, ``derivCosh_real), (.complex, ``derivCosh_complex)] },
  { rule := derivTanh, ruleDecl := ``derivTanh,
    proofs := [(.real, ``derivTanh_real), (.complex, ``derivTanh_complex)] },
  { rule := derivArctanh, ruleDecl := ``derivArctanh, proofs := [(.real, ``derivArctanh_real)],
    findings := ["real: Mathlib has no derivative lemma for Real.artanh at this revision; the proof derives it from artanh x = 1/2 log((1 + x)/(1 - x)) on (-1, 1)."] },
  { rule := derivArcsin, ruleDecl := ``derivArcsin, proofs := [(.real, ``derivArcsin_real)] },
  { rule := derivArccos, ruleDecl := ``derivArccos, proofs := [(.real, ``derivArccos_real)] },
  { rule := derivCot, ruleDecl := ``derivCot,
    proofs := [(.real, ``derivCot_real), (.complex, ``derivCot_complex)] },
  { rule := derivSec, ruleDecl := ``derivSec, proofs := [(.real, ``derivSec_real)] },
  { rule := derivCsc, ruleDecl := ``derivCsc, proofs := [(.real, ``derivCsc_real)] },
  { rule := derivCoth, ruleDecl := ``derivCoth, proofs := [(.real, ``derivCoth_real)] },
  { rule := derivSech, ruleDecl := ``derivSech, proofs := [(.real, ``derivSech_real)] },
  { rule := derivCsch, ruleDecl := ``derivCsch, proofs := [(.real, ``derivCsch_real)] },
  { rule := derivArcsinh, ruleDecl := ``derivArcsinh, proofs := [(.real, ``derivArcsinh_real)] },
  { rule := derivArccosh, ruleDecl := ``derivArccosh, proofs := [(.real, ``derivArccosh_real)] }
]

/-! ## Reference rewriter -/

/-- Terms the calculus rules act on. -/
inductive CTerm where
  /-- `diff(λy. e)` -/
  | diff (y : String) (e : Expr)
  /-- `limit(a, both_sides, λy. e)` -/
  | limit (a : Expr) (y : String) (e : Expr)
  /-- `λy. e` -/
  | lam (y : String) (e : Expr)
  /-- A value. -/
  | val (e : Expr)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The OpenMath object of a term. -/
def CTerm.toOM : CTerm → OMObj
  | .diff y e => .oma diffSymbol [lamOM y e]
  | .limit a y e => .oma limitSymbol [a.toOM, .oms bothSidesSymbol, lamOM y e]
  | .lam y e => lamOM y e
  | .val e => e.toOM

/-- The independence constraints hold for a match binding the bound
variable to `y`. -/
def CRule.indepOk (r : CRule) (σ : Subst) (y : String) : Bool :=
  r.independent.all fun c => y ∉ (σ.apply c).varList

/-- Apply a rule at the root: the input's bound variable replaces the rule's,
the limit point is matched, and the independence constraints are checked. -/
def CRule.apply? (r : CRule) : CTerm → Option CTerm
  | .diff y e =>
    if r.shape = .deriv then
      match matchAux r.body e [(r.x, .var y)] with
      | some σ => if r.indepOk σ y then some (.lam y (r.result.subst σ)) else none
      | none => none
    else none
  | .limit a y e =>
    if r.shape = .limit then
      match matchAux r.body e [(r.x, .var y)] with
      | some σ =>
        match matchAux r.point a σ with
        | some σ' => if r.indepOk σ' y then some (.val (r.result.subst σ')) else none
        | none => none
      | none => none
    else none
  | _ => none

/-- The first rule that applies, in priority order. -/
def rewrite : List CRule → CTerm → Option (String × CTerm)
  | [], _ => none
  | r :: rs, t =>
    match r.apply? t with
    | some t' => some (r.id, t')
    | none => rewrite rs t

/-- A rule's result is a lambda or a value, to which no rule applies. -/
theorem apply?_result {r : CRule} {t t' : CTerm} (h : r.apply? t = some t') (q : CRule) :
    q.apply? t' = none := by
  cases t with
  | diff y e =>
    simp only [CRule.apply?] at h
    split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; rfl
        · cases h
      · cases h
    · cases h
  | limit a y e =>
    simp only [CRule.apply?] at h
    split at h
    · split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h; subst h; rfl
          · cases h
        · cases h
      · cases h
    · cases h
  | lam _ _ => simp [CRule.apply?] at h
  | val _ => simp [CRule.apply?] at h

theorem rewrite_none {t : CTerm} (hn : ∀ q : CRule, q.apply? t = none) :
    ∀ rules, rewrite rules t = none
  | [] => rfl
  | q :: qs => by simp [rewrite, hn q, rewrite_none hn qs]

theorem rewrite_some : ∀ (rules : List CRule) (t : CTerm) (s : String × CTerm),
    rewrite rules t = some s → ∃ q : CRule, q.apply? t = some s.2
  | [], _, _, h => by simp [rewrite] at h
  | r :: rs, t, s, h => by
    simp only [rewrite] at h
    split at h
    · rename_i t' ht
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨r, ht⟩
    · exact rewrite_some rs t s h

/-- **Termination.**  Normalization takes at most one step: no rule applies
to the result of a rule. -/
theorem rewrite_result (rules : List CRule) (t : CTerm) (s : String × CTerm)
    (h : rewrite rules t = some s) : rewrite rules s.2 = none := by
  obtain ⟨q, hq⟩ := rewrite_some rules t s h
  exact rewrite_none (apply?_result hq) _

/-! ## Instantiation soundness -/

section Instance

variable {α : Type} [Field α]

theorem eval_congr (I : Interp α) :
    ∀ (e : Expr) {ρ ρ' : String → α}, (∀ n ∈ e.varList, ρ n = ρ' n) → eval I ρ e = eval I ρ' e
  | .var n, _, _, h => by simpa [eval, Expr.varList] using h n (by simp [Expr.varList])
  | .int _, _, _, _ => rfl
  | .const c, _, _, _ => by cases c; rfl
  | .app1 o a, ρ, ρ', h => by
    have := eval_congr I a (ρ := ρ) (ρ' := ρ') (by simpa [Expr.varList] using h)
    cases o <;> simp [eval, this]
  | .app2 o a b, ρ, ρ', h => by
    have ha := eval_congr I a (ρ := ρ) (ρ' := ρ')
      (fun n hn => h n (by simp [Expr.varList, hn]))
    have hb := eval_congr I b (ρ := ρ) (ρ' := ρ')
      (fun n hn => h n (by simp [Expr.varList, hn]))
    cases o <;> simp [eval, ha, hb]
  | .pow a b, ρ, ρ', h => by
    have ha := eval_congr I a (ρ := ρ) (ρ' := ρ')
      (fun n hn => h n (by simp [Expr.varList, hn]))
    have hb := eval_congr I b (ρ := ρ) (ρ' := ρ')
      (fun n hn => h n (by simp [Expr.varList, hn]))
    simp [eval, ha, hb]

theorem defined_congr (I : Interp α) :
    ∀ (e : Expr) {ρ ρ' : String → α}, (∀ n ∈ e.varList, ρ n = ρ' n) →
      (Defined I ρ e ↔ Defined I ρ' e)
  | .var _, _, _, _ => Iff.rfl
  | .int _, _, _, _ => Iff.rfl
  | .const _, _, _, _ => Iff.rfl
  | .app1 o a, ρ, ρ', h => by
    have h' : ∀ n ∈ a.varList, ρ n = ρ' n := by simpa [Expr.varList] using h
    have hd := defined_congr I a h'
    have he := eval_congr I a h'
    cases o <;> simp [Defined, hd, he]
  | .app2 o a b, ρ, ρ', h => by
    have ha' : ∀ n ∈ a.varList, ρ n = ρ' n := fun n hn => h n (by simp [Expr.varList, hn])
    have hb' : ∀ n ∈ b.varList, ρ n = ρ' n := fun n hn => h n (by simp [Expr.varList, hn])
    have hda := defined_congr I a ha'
    have hdb := defined_congr I b hb'
    have hea := eval_congr I a ha'
    have heb := eval_congr I b hb'
    cases o <;> simp [Defined, hda, hdb, hea, heb]
  | .pow a b, ρ, ρ', h => by
    have ha' : ∀ n ∈ a.varList, ρ n = ρ' n := fun n hn => h n (by simp [Expr.varList, hn])
    have hb' : ∀ n ∈ b.varList, ρ n = ρ' n := fun n hn => h n (by simp [Expr.varList, hn])
    simp [Defined, defined_congr I a ha', defined_congr I b hb', eval_congr I a ha',
      eval_congr I b hb']

/-- Under a substitution that renames `x` to `y`, an expression whose other
variables are matched by terms not mentioning `y` evaluates as the original,
with `x` given the value `v` and the other variables their images. -/
theorem eval_rename (I : Interp α) {x y : String} {σ : Subst}
    (hσ : σ.find? x = some (.var y)) {e : Expr}
    (he : ∀ n ∈ e.varList, n = x ∨ y ∉ (σ.apply n).varList) (ρ : String → α) (v : α) :
    eval I (Function.update ρ y v) (e.subst σ) = eval I (Function.update (σ.env I ρ) x v) e ∧
      (Defined I (Function.update ρ y v) (e.subst σ) ↔
        Defined I (Function.update (σ.env I ρ) x v) e ∧
          ∀ n ∈ e.varList, n ≠ x → Defined I ρ (σ.apply n)) := by
  have hx : σ.apply x = .var y := by simp [Subst.apply, hσ]
  have himg : ∀ n ∈ e.varList, n ≠ x →
      (∀ m ∈ (σ.apply n).varList, Function.update ρ y v m = ρ m) := by
    intro n hn hnx m hm
    have hy : y ∉ (σ.apply n).varList := (he n hn).resolve_left hnx
    have : m ≠ y := fun h => hy (h ▸ hm)
    simp [Function.update_of_ne this]
  have henv : ∀ n ∈ e.varList,
      σ.env I (Function.update ρ y v) n = Function.update (σ.env I ρ) x v n := by
    intro n hn
    by_cases hnx : n = x
    · subst hnx; simp [Subst.env, hx, eval]
    · rw [Function.update_of_ne hnx]
      exact eval_congr I _ (himg n hn hnx)
  refine ⟨by rw [eval_subst]; exact eval_congr I e henv, ?_⟩
  rw [defined_subst, defined_congr I e henv]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun n hn hnx => (defined_congr I _ (himg n hn hnx)).1 (h2 n hn)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun n hn => ?_⟩
    by_cases hnx : n = x
    · subst hnx; rw [hx]; trivial
    · exact (defined_congr I _ (himg n hn hnx)).2 (h2 n hn hnx)

end Instance

theorem matched_find {x y : String} {p e : Expr} {σ : Subst}
    (h : matchAux p e [(x, .var y)] = some σ) : σ.find? x = some (.var y) :=
  (matchAux_spec p e _ σ h).1 x _ (by simp [Subst.find?])

theorem indep_vars {r : CRule} (hw : r.wellFormed = true) {σ : Subst} {y : String}
    (hi : r.indepOk σ y = true) :
    (∀ n ∈ r.body.varList, n = r.x ∨ y ∉ (σ.apply n).varList) ∧
      (∀ n ∈ r.result.varList, n = r.x ∨ y ∉ (σ.apply n).varList) := by
  simp only [CRule.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
  simp only [CRule.indepOk, List.all_eq_true, decide_eq_true_eq] at hi
  have hb : ∀ n ∈ r.body.varList, n = r.x ∨ y ∉ (σ.apply n).varList := by
    intro n hn
    rcases hw.1.1.1 n hn with h | h
    · exact Or.inl h
    · exact Or.inr (hi n h)
  refine ⟨hb, fun n hn => ?_⟩
  rcases hw.1.1.2 n hn with h | h
  · exact Or.inl h
  · exact hb n h

/-- **Instantiation soundness for derivatives.**  If a derivative rule holds,
its instance on `diff(λy. e)` holds with the input's bound variable. -/
theorem deriv_instance {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) (r : CRule)
    (hw : r.wellFormed = true) (hr : DerivHolds I r.x r.body r.result) {y : String} {e : Expr}
    {σ : Subst} (hm : matchAux r.body e [(r.x, .var y)] = some σ)
    (hi : r.indepOk σ y = true) :
    DerivHolds I y e (r.result.subst σ) := by
  obtain ⟨hb, hres⟩ := indep_vars hw hi
  have hσ := matched_find hm
  have he : r.body.subst σ = e := (matchAux_spec r.body e _ σ hm).2 σ (Subst.Extends.refl σ)
  have hrv : ∀ n ∈ r.result.varList, n ≠ r.x → n ∈ r.body.varList := by
    simp only [CRule.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
    intro n hn hnx; exact (hw.1.1.2 n hn).resolve_left hnx
  intro env t hF
  have hF' : ∀ᶠ v in 𝓝 t, Defined I (Function.update (σ.env I env) r.x v) r.body := by
    filter_upwards [hF] with v hv
    rw [← he] at hv
    exact ((eval_rename I hσ hb env v).2.1 hv).1
  have himg : ∀ n ∈ r.body.varList, n ≠ r.x → Defined I env (σ.apply n) := by
    have ht := hF.self_of_nhds
    rw [← he] at ht
    exact ((eval_rename I hσ hb env t).2.1 ht).2
  obtain ⟨hG, hD⟩ := hr (σ.env I env) t hF'
  refine ⟨(eval_rename I hσ hres env t).2.2 ⟨hG, fun n hn hnx => himg n (hrv n hn hnx) hnx⟩, ?_⟩
  rw [(eval_rename I hσ hres env t).1]
  have hfun : (fun v => eval I (Function.update env y v) e) =
      fun v => eval I (Function.update (σ.env I env) r.x v) r.body := by
    funext v
    rw [← he]
    exact (eval_rename I hσ hb env v).1
  rw [hfun]
  exact hD

/-- **Instantiation soundness for limits.** -/
theorem limit_instance {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) (r : CRule)
    (hw : r.wellFormed = true) (hr : LimitHolds I r.x r.point r.body r.result) {y : String}
    {a e : Expr} {σ σ' : Subst} (hm : matchAux r.body e [(r.x, .var y)] = some σ)
    (hp : matchAux r.point a σ = some σ') (hi : r.indepOk σ' y = true) :
    LimitHolds I y a e (r.result.subst σ') := by
  obtain ⟨hb, hres⟩ := indep_vars hw hi
  have hext := (matchAux_spec r.point a σ σ' hp)
  have hσ : σ'.find? r.x = some (.var y) := hext.1 _ _ (matched_find hm)
  have he : r.body.subst σ' = e :=
    (matchAux_spec r.body e _ σ hm).2 σ' hext.1
  have ha : r.point.subst σ' = a := hext.2 σ' (Subst.Extends.refl σ')
  intro env hF
  have hpt : eval I env a = eval I (σ'.env I env) r.point := by rw [← ha, eval_subst]
  rw [hpt] at hF
  have hF' : ∀ᶠ v in 𝓝[≠] (eval I (σ'.env I env) r.point),
      Defined I (Function.update (σ'.env I env) r.x v) r.body := by
    filter_upwards [hF] with v hv
    rw [← he] at hv
    exact ((eval_rename I hσ hb env v).2.1 hv).1
  have himg : ∀ n ∈ r.body.varList, n ≠ r.x → Defined I env (σ'.apply n) := by
    obtain ⟨v, hv⟩ := hF.exists
    rw [← he] at hv
    exact ((eval_rename I hσ hb env v).2.1 hv).2
  obtain ⟨hL, hT⟩ := hr (σ'.env I env) hF'
  refine ⟨?_, ?_⟩
  · rw [defined_subst]
    refine ⟨hL, fun n hn => ?_⟩
    by_cases hnx : n = r.x
    · subst hnx; simp [Subst.apply, hσ, Defined]
    · simp only [CRule.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
      exact himg n ((hw.1.1.2 n hn).resolve_left hnx) hnx
  · rw [hpt, eval_subst]
    have hfun : (fun v => eval I (Function.update env y v) e) =
        fun v => eval I (Function.update (σ'.env I env) r.x v) r.body := by
      funext v
      rw [← he]
      exact (eval_rename I hσ hb env v).1
    rw [hfun]
    exact hT

/-- What a rewrite step means: the derivative or limit statement for the
input and the result. -/
def Correct {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) : CTerm → CTerm → Prop
  | .diff y e, .lam y' g => y = y' ∧ DerivHolds I y e g
  | .limit a y e, .val L => LimitHolds I y a e L
  | _, _ => False

/-- The statement of a rule in an interpretation. -/
def CRule.HoldsIn {𝕜 : Type} [NontriviallyNormedField 𝕜] (r : CRule) (I : Interp 𝕜) : Prop :=
  match r.shape with
  | .deriv => DerivHolds I r.x r.body r.result
  | .limit => LimitHolds I r.x r.point r.body r.result

/-- **Engine soundness.**  A step with a well-formed rule that holds in `I`
is correct in `I`. -/
theorem apply?_sound {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) {r : CRule}
    (hw : r.wellFormed = true) (hr : r.HoldsIn I) {t t' : CTerm} (h : r.apply? t = some t') :
    Correct I t t' := by
  cases t with
  | diff y e =>
    simp only [CRule.apply?] at h
    split at h
    · rename_i hs
      split at h
      · rename_i σ hm
        split at h
        · rename_i hi
          simp only [Option.some.injEq] at h
          subst h
          simp only [CRule.HoldsIn, hs] at hr
          exact ⟨rfl, deriv_instance I r hw hr hm hi⟩
        · cases h
      · cases h
    · cases h
  | limit a y e =>
    simp only [CRule.apply?] at h
    split at h
    · rename_i hs
      split at h
      · rename_i σ hm
        split at h
        · rename_i σ' hp
          split at h
          · rename_i hi
            simp only [Option.some.injEq] at h
            subst h
            simp only [CRule.HoldsIn, hs] at hr
            exact limit_instance I r hw hr hm hp hi
          · cases h
        · cases h
      · cases h
    · cases h
  | lam _ _ => simp [CRule.apply?] at h
  | val _ => simp [CRule.apply?] at h

theorem holds_real {r : CRule} (h : r.Holds .real) : r.HoldsIn Interp.real := by
  unfold CRule.HoldsIn; unfold CRule.Holds at h; exact h

theorem holds_complex {r : CRule} (h : r.Holds .complex) : r.HoldsIn Interp.complex := by
  unfold CRule.HoldsIn; unfold CRule.Holds at h; exact h

/-- Every catalogue rule is well formed. -/
theorem catalog_wellFormed : ∀ e ∈ catalog, e.rule.wellFormed = true := by
  intro e he
  simp only [catalog, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end OSR.Calculus


