import OSR.Catalog
import OSR.OMObject

/-!
# Calculus

Migration of `OpenSymbolicRules/Calculus` at commit
`eb9eb87aa7ffcd6dd7da055fa6b6d87f35f840da`: the derivative and limit rules
whose functions are in the fragment.

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

/-- Well-formedness: the bound variable is the only variable of the body and
of the result, and the limit point is closed. -/
def CRule.wellFormed (r : CRule) : Bool :=
  r.body.varList.all (· = r.x) && r.result.varList.all (· = r.x) && r.point.varList.isEmpty

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

/-- v0.1 rules outside the fragment, with the reason. -/
def notMigrated : List (String × String) :=
  [(lim 1, "the side condition FreeQ (a variable does not occur free) has no OpenMath symbol"),
   ("calculus:2-derivatives/2.1-basic-derivatives:1",
     "the side condition FreeQ (a variable does not occur free) has no OpenMath symbol"),
   ("calculus:2-derivatives/2.1-basic-derivatives:2",
     "the side condition FreeQ (a variable does not occur free) has no OpenMath symbol")] ++
  ([7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21].map fun n =>
    (elem n, "uses a function outside the fragment (hyperbolic, reciprocal trigonometric, inverse sine or cosine, or square root)")) ++
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
     intro env
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

/-! ## Catalogue -/

/-- A calculus rule with its proofs. -/
structure CEntry where
  rule : CRule
  ruleDecl : Lean.Name
  proofs : List (Domain × Lean.Name)
  unproved : List Domain := []
  findings : List String := []
  deriving Repr, Inhabited

private def lnComplexFinding : String :=
  "complex: not proved; ln is defined for z ≠ 0 but the principal logarithm is not differentiable on the negative real axis (its branch cut), so the statement fails there."

private def arctanComplexFinding : String :=
  "complex: not proved; the mapping of transc1#arctan to Complex.arctan is provisional."

/-- The Calculus catalogue (limits, then derivatives, in v0.1 load order). -/
def catalog : List CEntry := [
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
    findings := [arctanComplexFinding] }
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

/-- Apply a rule at the root: the input's bound variable replaces the rule's,
and the limit point must be the rule's. -/
def CRule.apply? (r : CRule) : CTerm → Option CTerm
  | .diff y e =>
    if r.shape = .deriv then
      (matchAux r.body e [(r.x, .var y)]).map fun σ => .lam y (r.result.subst σ)
    else none
  | .limit a y e =>
    if r.shape = .limit ∧ a = r.point then
      (matchAux r.body e [(r.x, .var y)]).map fun σ => .val (r.result.subst σ)
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
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨σ, -, rfl⟩ := h
      rfl
    · cases h
  | limit a y e =>
    simp only [CRule.apply?] at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨σ, -, rfl⟩ := h
      rfl
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
    have heb := eval_congr I b hb'
    cases o <;> simp [Defined, hda, hdb, heb]
  | .pow a b, ρ, ρ', h => by
    have ha' : ∀ n ∈ a.varList, ρ n = ρ' n := fun n hn => h n (by simp [Expr.varList, hn])
    have hb' : ∀ n ∈ b.varList, ρ n = ρ' n := fun n hn => h n (by simp [Expr.varList, hn])
    simp [Defined, defined_congr I a ha', defined_congr I b hb', eval_congr I a ha',
      eval_congr I b hb']

/-- Under a substitution that renames `x` to `y`, an expression whose only
variable is `x` evaluates as the original with `x` given the value of `y`. -/
theorem eval_rename (I : Interp α) {x y : String} {σ : Subst}
    (hσ : σ.find? x = some (.var y)) {e : Expr} (he : ∀ n ∈ e.varList, n = x)
    (ρ : String → α) (v : α) :
    eval I (Function.update ρ y v) (e.subst σ) = eval I (Function.update ρ x v) e ∧
      (Defined I (Function.update ρ y v) (e.subst σ) ↔ Defined I (Function.update ρ x v) e) := by
  have hx : σ.apply x = .var y := by simp [Subst.apply, hσ]
  have henv : ∀ n ∈ e.varList, σ.env I (Function.update ρ y v) n = Function.update ρ x v n := by
    intro n hn
    rw [he n hn]
    simp [Subst.env, hx, eval]
  refine ⟨by rw [eval_subst]; exact eval_congr I e henv, ?_⟩
  rw [defined_subst, defined_congr I e henv]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun n hn => ?_⟩
    rw [he n hn, hx]
    trivial

end Instance

theorem matched_find {x y : String} {p e : Expr} {σ : Subst}
    (h : matchAux p e [(x, .var y)] = some σ) : σ.find? x = some (.var y) :=
  (matchAux_spec p e _ σ h).1 x _ (by simp [Subst.find?])

/-- **Instantiation soundness for derivatives.**  If a derivative rule holds,
its instance on `diff(λy. e)` holds with the input's bound variable. -/
theorem deriv_instance {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) (r : CRule)
    (hw : r.wellFormed = true) (hr : DerivHolds I r.x r.body r.result) {y : String} {e : Expr}
    {σ : Subst} (hm : matchAux r.body e [(r.x, .var y)] = some σ) :
    DerivHolds I y e (r.result.subst σ) := by
  simp only [CRule.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
  have hσ := matched_find hm
  have he : r.body.subst σ = e := (matchAux_spec r.body e _ σ hm).2 σ (Subst.Extends.refl σ)
  intro env t hF
  have hF' : ∀ᶠ v in 𝓝 t, Defined I (Function.update env r.x v) r.body := by
    filter_upwards [hF] with v hv
    rw [← he] at hv
    exact (eval_rename I hσ hw.1.1 env v).2.1 hv
  obtain ⟨hG, hD⟩ := hr env t hF'
  refine ⟨(eval_rename I hσ hw.1.2 env t).2.2 hG, ?_⟩
  rw [(eval_rename I hσ hw.1.2 env t).1]
  have hfun : (fun v => eval I (Function.update env y v) e) =
      fun v => eval I (Function.update env r.x v) r.body := by
    funext v
    rw [← he]
    exact (eval_rename I hσ hw.1.1 env v).1
  rw [hfun]
  exact hD

/-- **Instantiation soundness for limits.** -/
theorem limit_instance {𝕜 : Type} [NontriviallyNormedField 𝕜] (I : Interp 𝕜) (r : CRule)
    (hw : r.wellFormed = true) (hr : LimitHolds I r.x r.point r.body r.result) {y : String}
    {e : Expr} {σ : Subst} (hm : matchAux r.body e [(r.x, .var y)] = some σ) :
    LimitHolds I y r.point e (r.result.subst σ) := by
  simp only [CRule.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.isEmpty_iff] at hw
  have hσ := matched_find hm
  have he : r.body.subst σ = e := (matchAux_spec r.body e _ σ hm).2 σ (Subst.Extends.refl σ)
  intro env
  let env' := Function.update env r.x (env y)
  obtain ⟨hL, hT⟩ := hr env'
  have hself : Function.update env y (env y) = env := Function.update_eq_self y env
  have hR := eval_rename I hσ hw.1.2 env (env y)
  rw [hself] at hR
  refine ⟨hR.2.2 hL, ?_⟩
  rw [hR.1]
  have hpt : eval I env r.point = eval I env' r.point :=
    eval_congr I r.point (fun n hn => by simp [hw.2] at hn)
  rw [hpt]
  have hfun : (fun v => eval I (Function.update env y v) e) =
      fun v => eval I (Function.update env' r.x v) r.body := by
    funext v
    rw [← he, (eval_rename I hσ hw.1.1 env v).1]
    simp [env']
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
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨σ, hm, rfl⟩ := h
      simp only [CRule.HoldsIn, hs] at hr
      exact ⟨rfl, deriv_instance I r hw hr hm⟩
    · cases h
  | limit a y e =>
    simp only [CRule.apply?] at h
    split at h
    · rename_i hs
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨σ, hm, rfl⟩ := h
      simp only [CRule.HoldsIn, hs.1] at hr
      rw [hs.2]
      exact limit_instance I r hw hr hm
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
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end OSR.Calculus


