import OSR.Catalog
import OSR.Termination

/-!
# Trigonometry pilot

Migration of the 13 rules of `OpenSymbolicRules/Trigonometry` at commit
`e9b6ef0e46495c9896b5dc168dabd5f7c1fa39b5`, including the three rules that only
belong to the `sum_to_product` profile.

Changes of representation relative to OSR v0.1, none of which changes the
mathematical statement:

* n-ary `Multiply` becomes left-nested binary `arith1#times`
  (`2 * sin x * cos x` is `(2 * sin x) * cos x`);
* `Power` with exponent `2` becomes a natural-number literal power;
* priority is the v0.1 load position (file order, then position in the
  file), times ten;
* profiles are redesigned: the v0.1 `default` and `sum_to_product` profiles do
  not terminate (see `cycleFinding`), so v1 groups the rules by orientation
  (`profiles`).

Each proof reuses a Mathlib theorem directly, or rewrites with Mathlib
theorems and closes the goal with `ring`.
-/

namespace OSR.Trigonometry

open OSR

private abbrev x : Expr := .var "x"
private abbrev y : Expr := .var "y"
private abbrev a : Expr := .var "a"
private abbrev b : Expr := .var "b"
private abbrev z : Expr := .var "z"
private abbrev two : Expr := .int 2
private abbrev sin (e : Expr) : Expr := .app1 .sin e
private abbrev cos (e : Expr) : Expr := .app1 .cos e
private abbrev add (e f : Expr) : Expr := .app2 .add e f
private abbrev sub (e f : Expr) : Expr := .app2 .sub e f
private abbrev mul (e f : Expr) : Expr := .app2 .mul e f
private abbrev div (e f : Expr) : Expr := .app2 .div e f
private abbrev sq (e : Expr) : Expr := .powNat e 2

private def repo : String := "OpenSymbolicRules/Trigonometry"
private def rev : String := "e9b6ef0e46495c9896b5dc168dabd5f7c1fa39b5"

/-- Provenance for a rule migrated from Trigonometry v0.1, preserving its
original sources. -/
private def migrated (legacy : String) (orig : List Source) : Provenance :=
  { method := .derived,
    sources := { name := repo, locator := legacy, revision := some rev, license := some "MIT" } :: orig }

private def fungrim (entry file : String) : Source :=
  { name := "Fungrim MathJSON", locator := s!"corpus/{file}#{entry}", license := some "MIT" }

/-- Every profile of the rule set.  Each profile is oriented consistently so
that it terminates (see `docs/audit-m0.md`):

* `default`: expansion (angle sum, double angle);
* `product_to_sum`, `power_reduction`, `sum_to_product`: the corresponding
  transformations alone.

The Pythagorean identity and `tan ∘ arctan` belong to every profile. -/
def profiles : List String := ["default", "product_to_sum", "power_reduction", "sum_to_product"]

/-! ## Rules -/

/-- `sin(x)^2 + cos(x)^2 ⟶ 1`. -/
def pythagorean : Rule where
  id := "trigonometry.pythagorean"
  legacyId := some "trigonometry:1-basic-identities/1.1-pythagorean:1"
  vars := ["x"]
  lhs := add (sq (sin x)) (sq (cos x))
  rhs := .int 1
  profiles := profiles
  priority := 10
  description := "Pythagorean identity: sin^2(x) + cos^2(x) = 1"
  provenance := migrated "trigonometry:1-basic-identities/1.1-pythagorean:1" []

/-- `sin(x + y) ⟶ sin x cos y + cos x sin y`. -/
def sinAdd : Rule where
  id := "trigonometry.angle_sum.sin_add"
  legacyId := some "trigonometry:1-basic-identities/1.2-angle-sum:1"
  vars := ["x", "y"]
  lhs := sin (add x y)
  rhs := add (mul (sin x) (cos y)) (mul (cos x) (sin y))
  profiles := ["default"]
  priority := 20
  description := "Sine angle-sum identity"
  provenance := migrated "trigonometry:1-basic-identities/1.2-angle-sum:1" []

/-- `cos(x - y) ⟶ cos x cos y + sin x sin y`. -/
def cosSub : Rule where
  id := "trigonometry.angle_sum.cos_sub"
  legacyId := some "trigonometry:1-basic-identities/1.2-angle-sum:2"
  vars := ["x", "y"]
  lhs := cos (sub x y)
  rhs := add (mul (cos x) (cos y)) (mul (sin x) (sin y))
  profiles := ["default"]
  priority := 30
  description := "Cosine angle-difference identity"
  provenance := migrated "trigonometry:1-basic-identities/1.2-angle-sum:2" []

/-- `sin(2 x) ⟶ 2 sin x cos x`. -/
def sinTwoMul : Rule where
  id := "trigonometry.double_angle.sin"
  legacyId := some "trigonometry:1-basic-identities/1.3-double-angle:1"
  vars := ["x"]
  lhs := sin (mul two x)
  rhs := mul (mul two (sin x)) (cos x)
  profiles := ["default"]
  priority := 40
  description := "Sine double-angle identity"
  provenance := migrated "trigonometry:1-basic-identities/1.3-double-angle:1" []

/-- `cos(2 x) ⟶ cos(x)^2 - sin(x)^2`. -/
def cosTwoMul : Rule where
  id := "trigonometry.double_angle.cos"
  legacyId := some "trigonometry:1-basic-identities/1.3-double-angle:2"
  vars := ["x"]
  lhs := cos (mul two x)
  rhs := sub (sq (cos x)) (sq (sin x))
  profiles := ["default"]
  priority := 50
  description := "Cosine double-angle identity"
  provenance := migrated "trigonometry:1-basic-identities/1.3-double-angle:2" []

/-- `sin a cos b ⟶ (sin(a + b) + sin(a - b)) / 2`. -/
def sinMulCos : Rule where
  id := "trigonometry.product_to_sum.sin_cos"
  legacyId := some "trigonometry:1-basic-identities/1.4-product-to-sum:1"
  vars := ["a", "b"]
  lhs := mul (sin a) (cos b)
  rhs := div (add (sin (add a b)) (sin (sub a b))) two
  profiles := ["product_to_sum"]
  priority := 60
  description := "Product-to-sum identity for sine times cosine"
  provenance := migrated "trigonometry:1-basic-identities/1.4-product-to-sum:1"
    [fungrim "012eba" "sine.json"]

/-- `sin a sin b ⟶ (cos(a - b) - cos(a + b)) / 2`. -/
def sinMulSin : Rule where
  id := "trigonometry.product_to_sum.sin_sin"
  legacyId := some "trigonometry:1-basic-identities/1.4-product-to-sum:2"
  vars := ["a", "b"]
  lhs := mul (sin a) (sin b)
  rhs := div (sub (cos (sub a b)) (cos (add a b))) two
  profiles := ["product_to_sum"]
  priority := 70
  description := "Product-to-sum identity for two sines"
  provenance := migrated "trigonometry:1-basic-identities/1.4-product-to-sum:2"
    [fungrim "ad6c1c" "sine.json"]

/-- `sin(x)^2 ⟶ (1 - cos(2 x)) / 2`. -/
def sinSq : Rule where
  id := "trigonometry.power_reduction.sin_sq"
  legacyId := some "trigonometry:1-basic-identities/1.5-power-reduction:1"
  vars := ["x"]
  lhs := sq (sin x)
  rhs := div (sub (.int 1) (cos (mul two x))) two
  profiles := ["power_reduction"]
  priority := 80
  description := "Sine-square power reduction"
  provenance := migrated "trigonometry:1-basic-identities/1.5-power-reduction:1"
    [fungrim "cf6e35" "sine.json"]

/-- `cos(x)^2 ⟶ (1 + cos(2 x)) / 2`. -/
def cosSq : Rule where
  id := "trigonometry.power_reduction.cos_sq"
  legacyId := some "trigonometry:1-basic-identities/1.5-power-reduction:2"
  vars := ["x"]
  lhs := sq (cos x)
  rhs := div (add (.int 1) (cos (mul two x))) two
  profiles := ["power_reduction"]
  priority := 90
  description := "Cosine-square power reduction"
  provenance := migrated "trigonometry:1-basic-identities/1.5-power-reduction:2" []

/-- `sin a + sin b ⟶ 2 sin((a + b)/2) cos((a - b)/2)`. -/
def sinAddSin : Rule where
  id := "trigonometry.sum_to_product.sin_add_sin"
  legacyId := some "trigonometry:1-basic-identities/1.6-sum-to-product:1"
  vars := ["a", "b"]
  lhs := add (sin a) (sin b)
  rhs := mul (mul two (sin (div (add a b) two))) (cos (div (sub a b) two))
  profiles := ["sum_to_product"]
  priority := 100
  description := "Sum-to-product identity for two sines"
  provenance := migrated "trigonometry:1-basic-identities/1.6-sum-to-product:1" []

/-- `cos a + cos b ⟶ 2 cos((a + b)/2) cos((a - b)/2)`. -/
def cosAddCos : Rule where
  id := "trigonometry.sum_to_product.cos_add_cos"
  legacyId := some "trigonometry:1-basic-identities/1.6-sum-to-product:2"
  vars := ["a", "b"]
  lhs := add (cos a) (cos b)
  rhs := mul (mul two (cos (div (add a b) two))) (cos (div (sub a b) two))
  profiles := ["sum_to_product"]
  priority := 110
  description := "Sum-to-product identity for two cosines"
  provenance := migrated "trigonometry:1-basic-identities/1.6-sum-to-product:2" []

/-- `cos a - cos b ⟶ -2 sin((a + b)/2) sin((a - b)/2)`. -/
def cosSubCos : Rule where
  id := "trigonometry.sum_to_product.cos_sub_cos"
  legacyId := some "trigonometry:1-basic-identities/1.6-sum-to-product:3"
  vars := ["a", "b"]
  lhs := sub (cos a) (cos b)
  rhs := mul (mul (.int (-2)) (sin (div (add a b) two))) (sin (div (sub a b) two))
  profiles := ["sum_to_product"]
  priority := 120
  description := "Difference-to-product identity for two cosines"
  provenance := migrated "trigonometry:1-basic-identities/1.6-sum-to-product:3" []

/-- `tan(arctan z) ⟶ z`. -/
def tanArctan : Rule where
  id := "trigonometry.inverse.tan_arctan"
  legacyId := some "trigonometry:2-inverse-functions/2.1-tangent-inverse:1"
  vars := ["z"]
  lhs := .app1 .tan (.app1 .arctan z)
  rhs := z
  profiles := profiles
  priority := 130
  description := "Tangent cancels the principal inverse tangent"
  provenance := migrated "trigonometry:2-inverse-functions/2.1-tangent-inverse:1"
    [fungrim "1f026d" "atan.json"]

/-! ## Proofs over ℝ -/

theorem pythagorean_real : pythagorean.Holds .real := by
  osr_intro pythagorean Interp.real
  exact Real.sin_sq_add_cos_sq _

theorem sinAdd_real : sinAdd.Holds .real := by
  osr_intro sinAdd Interp.real
  exact Real.sin_add _ _

theorem cosSub_real : cosSub.Holds .real := by
  osr_intro cosSub Interp.real
  exact Real.cos_sub _ _

theorem sinTwoMul_real : sinTwoMul.Holds .real := by
  osr_intro sinTwoMul Interp.real
  exact Real.sin_two_mul _

theorem cosTwoMul_real : cosTwoMul.Holds .real := by
  osr_intro cosTwoMul Interp.real
  exact Real.cos_two_mul' _

theorem sinMulCos_real : sinMulCos.Holds .real := by
  osr_intro sinMulCos Interp.real
  refine ⟨by norm_num, ?_⟩
  rw [Real.sin_add, Real.sin_sub]; ring

theorem sinMulSin_real : sinMulSin.Holds .real := by
  osr_intro sinMulSin Interp.real
  refine ⟨by norm_num, ?_⟩
  rw [Real.cos_sub, Real.cos_add]; ring

theorem sinSq_real : sinSq.Holds .real := by
  osr_intro sinSq Interp.real
  refine ⟨by norm_num, ?_⟩
  rw [Real.cos_two_mul, Real.sin_sq]; ring

theorem cosSq_real : cosSq.Holds .real := by
  osr_intro cosSq Interp.real
  refine ⟨by norm_num, ?_⟩
  rw [Real.cos_two_mul]; ring

theorem sinAddSin_real : sinAddSin.Holds .real := by
  osr_intro sinAddSin Interp.real
  refine ⟨by norm_num, ?_⟩
  rw [Real.sin_add_sin]

theorem cosAddCos_real : cosAddCos.Holds .real := by
  osr_intro cosAddCos Interp.real
  refine ⟨by norm_num, ?_⟩
  rw [Real.cos_add_cos]

theorem cosSubCos_real : cosSubCos.Holds .real := by
  osr_intro cosSubCos Interp.real
  refine ⟨by norm_num, ?_⟩
  rw [Real.cos_sub_cos]

theorem tanArctan_real : tanArctan.Holds .real := by
  osr_intro tanArctan Interp.real
  exact Real.tan_arctan _

/-! ## Proofs over ℂ -/

theorem pythagorean_complex : pythagorean.Holds .complex := by
  osr_intro pythagorean Interp.complex
  exact Complex.sin_sq_add_cos_sq _

theorem sinAdd_complex : sinAdd.Holds .complex := by
  osr_intro sinAdd Interp.complex
  exact Complex.sin_add _ _

theorem cosSub_complex : cosSub.Holds .complex := by
  osr_intro cosSub Interp.complex
  exact Complex.cos_sub _ _

theorem sinTwoMul_complex : sinTwoMul.Holds .complex := by
  osr_intro sinTwoMul Interp.complex
  exact Complex.sin_two_mul _

theorem cosTwoMul_complex : cosTwoMul.Holds .complex := by
  osr_intro cosTwoMul Interp.complex
  exact Complex.cos_two_mul' _

theorem sinMulCos_complex : sinMulCos.Holds .complex := by
  osr_intro sinMulCos Interp.complex
  refine ⟨by norm_num, ?_⟩
  rw [Complex.sin_add, Complex.sin_sub]; ring

theorem sinMulSin_complex : sinMulSin.Holds .complex := by
  osr_intro sinMulSin Interp.complex
  refine ⟨by norm_num, ?_⟩
  rw [Complex.cos_sub, Complex.cos_add]; ring

theorem sinSq_complex : sinSq.Holds .complex := by
  osr_intro sinSq Interp.complex
  refine ⟨by norm_num, ?_⟩
  rw [Complex.cos_two_mul, Complex.sin_sq]; ring

theorem cosSq_complex : cosSq.Holds .complex := by
  osr_intro cosSq Interp.complex
  refine ⟨by norm_num, ?_⟩
  rw [Complex.cos_two_mul]; ring

theorem sinAddSin_complex : sinAddSin.Holds .complex := by
  osr_intro sinAddSin Interp.complex
  refine ⟨by norm_num, ?_⟩
  rw [Complex.sin_add_sin]

theorem cosAddCos_complex : cosAddCos.Holds .complex := by
  osr_intro cosAddCos Interp.complex
  refine ⟨by norm_num, ?_⟩
  rw [Complex.cos_add_cos]

theorem cosSubCos_complex : cosSubCos.Holds .complex := by
  osr_intro cosSubCos Interp.complex
  refine ⟨by norm_num, ?_⟩
  rw [Complex.cos_sub_cos]

/-- Over ℂ the rewrite is sound only where the pattern is defined: `arctan` is
undefined at `±i`, and `Complex.tan_arctan` needs exactly those hypotheses.
OSR v0.1 stated this rule with no condition; the definedness of the pattern
carries the restriction here, so no hypothesis was added. -/
theorem tanArctan_complex : tanArctan.Holds .complex := by
  osr_intro tanArctan Interp.complex
  exact Complex.tan_arctan hd.1.1 hd.1.2

/-! ## Catalogue -/

/-- Strategy finding shared by the rules involved in the v0.1 cycles. -/
private def cycleFinding : String :=
  "operational: the v0.1 profiles do not terminate. angle_sum.sin_add and product_to_sum.sin_cos reproduce sin(x + y), angle_sum.cos_sub and product_to_sum.sin_sin reproduce cos(x - y), and power_reduction with double_angle.cos reproduces sin(x)^2. All rules are proved; v1 splits them into consistently oriented profiles, each checked for termination on the catalogue patterns."

/-- The Trigonometry catalogue, in v0.1 load order (= priority order). -/
def catalog : List CatalogEntry := [
  { rule := pythagorean, ruleDecl := ``pythagorean,
    proofs := [(.real, ``pythagorean_real), (.complex, ``pythagorean_complex)] },
  { rule := sinAdd, ruleDecl := ``sinAdd,
    proofs := [(.real, ``sinAdd_real), (.complex, ``sinAdd_complex)],
    findings := [cycleFinding] },
  { rule := cosSub, ruleDecl := ``cosSub,
    proofs := [(.real, ``cosSub_real), (.complex, ``cosSub_complex)],
    findings := [cycleFinding] },
  { rule := sinTwoMul, ruleDecl := ``sinTwoMul,
    proofs := [(.real, ``sinTwoMul_real), (.complex, ``sinTwoMul_complex)] },
  { rule := cosTwoMul, ruleDecl := ``cosTwoMul,
    proofs := [(.real, ``cosTwoMul_real), (.complex, ``cosTwoMul_complex)],
    findings := [cycleFinding] },
  { rule := sinMulCos, ruleDecl := ``sinMulCos,
    proofs := [(.real, ``sinMulCos_real), (.complex, ``sinMulCos_complex)],
    findings := [cycleFinding] },
  { rule := sinMulSin, ruleDecl := ``sinMulSin,
    proofs := [(.real, ``sinMulSin_real), (.complex, ``sinMulSin_complex)],
    findings := [cycleFinding] },
  { rule := sinSq, ruleDecl := ``sinSq,
    proofs := [(.real, ``sinSq_real), (.complex, ``sinSq_complex)],
    findings := [cycleFinding] },
  { rule := cosSq, ruleDecl := ``cosSq,
    proofs := [(.real, ``cosSq_real), (.complex, ``cosSq_complex)],
    findings := [cycleFinding] },
  { rule := sinAddSin, ruleDecl := ``sinAddSin,
    proofs := [(.real, ``sinAddSin_real), (.complex, ``sinAddSin_complex)] },
  { rule := cosAddCos, ruleDecl := ``cosAddCos,
    proofs := [(.real, ``cosAddCos_real), (.complex, ``cosAddCos_complex)] },
  { rule := cosSubCos, ruleDecl := ``cosSubCos,
    proofs := [(.real, ``cosSubCos_real), (.complex, ``cosSubCos_complex)] },
  { rule := tanArctan, ruleDecl := ``tanArctan,
    proofs := [(.real, ``tanArctan_real), (.complex, ``tanArctan_complex)],
    findings := [
      "complex: OSR v0.1 states tan(arctan z) = z without condition and cites Fungrim 1f026d for complex z; arctan is undefined at z = ±i and Complex.tan_arctan requires z ≠ I and z ≠ -I. The rule is sound for defined patterns only; engines must not apply it at z = ±i.",
      "complex: certification is blocked by the provisional mapping of transc1#arctan to Complex.arctan (branch-cut agreement with the CD is unverified)."] }
]

/-! ## Profiles and engine soundness -/

/-- The rules of a profile, in priority order. -/
def profileRules (p : String) : List Rule :=
  (catalog.map (·.rule)).filter (p ∈ ·.profiles)

private theorem catalog_sound_real : ∀ e ∈ catalog, e.rule.Holds .real ∧ e.rule.rhsClosed = true := by
  intro e he
  simp only [catalog, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨pythagorean_real, by decide⟩, ⟨sinAdd_real, by decide⟩, ⟨cosSub_real, by decide⟩,
    ⟨sinTwoMul_real, by decide⟩, ⟨cosTwoMul_real, by decide⟩, ⟨sinMulCos_real, by decide⟩,
    ⟨sinMulSin_real, by decide⟩, ⟨sinSq_real, by decide⟩, ⟨cosSq_real, by decide⟩,
    ⟨sinAddSin_real, by decide⟩, ⟨cosAddCos_real, by decide⟩, ⟨cosSubCos_real, by decide⟩,
    ⟨tanArctan_real, by decide⟩]

private theorem catalog_sound_complex :
    ∀ e ∈ catalog, e.rule.Holds .complex ∧ e.rule.rhsClosed = true := by
  intro e he
  simp only [catalog, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨pythagorean_complex, by decide⟩, ⟨sinAdd_complex, by decide⟩,
    ⟨cosSub_complex, by decide⟩, ⟨sinTwoMul_complex, by decide⟩,
    ⟨cosTwoMul_complex, by decide⟩, ⟨sinMulCos_complex, by decide⟩,
    ⟨sinMulSin_complex, by decide⟩, ⟨sinSq_complex, by decide⟩, ⟨cosSq_complex, by decide⟩,
    ⟨sinAddSin_complex, by decide⟩, ⟨cosAddCos_complex, by decide⟩,
    ⟨cosSubCos_complex, by decide⟩, ⟨tanArctan_complex, by decide⟩]

theorem profileRules_sound_real (p : String) : RulesSound Interp.real (profileRules p) := by
  intro r hr _
  simp only [profileRules, List.mem_filter, List.mem_map] at hr
  obtain ⟨⟨e, he, rfl⟩, _⟩ := hr
  exact catalog_sound_real e he

theorem profileRules_sound_complex (p : String) :
    RulesSound Interp.complex (profileRules p) := by
  intro r hr _
  simp only [profileRules, List.mem_filter, List.mem_map] at hr
  obtain ⟨⟨e, he, rfl⟩, _⟩ := hr
  exact catalog_sound_complex e he

/-- Running the reference engine with any Trigonometry profile over ℝ
preserves definedness and value. -/
theorem normalize_sound_real (p : String) (fuel : Nat) (env : String → ℝ) (e : Expr) :
    Preserves Interp.real env e (normalize (profileRules p) fuel e).result :=
  normalize_sound _ (profileRules_sound_real p) fuel e

/-- Running the reference engine with any Trigonometry profile over ℂ
preserves definedness and value (Lean semantics; the `transc1#arctan` mapping
over ℂ is provisional). -/
theorem normalize_sound_complex (p : String) (fuel : Nat) (env : String → ℂ) (e : Expr) :
    Preserves Interp.complex env e (normalize (profileRules p) fuel e).result :=
  normalize_sound _ (profileRules_sound_complex p) fuel e

/-! ## Termination

Each profile has a weight (`OSR.Weight`) under which all its rules are
decreasing, so the reference engine terminates on every expression, within
`(weight p).eval (fun _ => 0) e` steps.  The weights differ by profile
because the profiles orient rules in opposite directions:

* `default` expands angle sums: a sine or cosine weighs exponentially in its
  argument, so splitting the argument pays for the extra operators;
* `product_to_sum` removes products of sines and cosines: products weigh
  multiplicatively;
* `power_reduction` removes squares: powers weigh polynomially in their base;
* `sum_to_product` removes sums and differences: they weigh multiplicatively,
  and a sine or cosine weighs three times its argument.

Integer literals and `π` weigh `1`; the other operators add `1` to the sum of
their arguments. -/

/-- Weight of the `default` profile. -/
def defaultWeight : Weight where
  int _ := 1
  const _ := 1
  op1 o a := match o with
    | .sin | .cos => 8 ^ (a + 1)
    | _ => a + 1
  op2 _ a b := a + b + 1
  pow a k := a + k + 1
  powNeg a k := a + k + 2
  mono1 o a a' h := by
    cases o <;> simp only
    all_goals first | omega | exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  mono2l _ _ _ _ h := by omega
  mono2r _ _ _ _ h := by omega
  monoPow _ _ _ h := by omega
  monoPowNeg _ _ _ h := by omega

/-- Weight of the `product_to_sum` profile. -/
def productToSumWeight : Weight where
  int _ := 1
  const _ := 1
  op1 o a := match o with
    | .sin | .cos => a + 3
    | _ => a + 1
  op2 o a b := match o with
    | .mul => (a + 1) * (b + 1)
    | _ => a + b + 1
  pow a k := a + k + 1
  powNeg a k := a + k + 2
  mono1 o a a' h := by cases o <;> simp only <;> omega
  mono2l o a a' b h := by cases o <;> simp only <;> first | omega | nlinarith
  mono2r o a b b' h := by cases o <;> simp only <;> first | omega | nlinarith
  monoPow _ _ _ h := by omega
  monoPowNeg _ _ _ h := by omega

/-- Weight of the `power_reduction` profile. -/
def powerReductionWeight : Weight where
  int _ := 1
  const _ := 1
  op1 _ a := a + 1
  op2 _ a b := a + b + 1
  pow a k := (a + 1) ^ (k + 1)
  powNeg a k := a + k + 2
  mono1 _ _ _ h := by omega
  mono2l _ _ _ _ h := by omega
  mono2r _ _ _ _ h := by omega
  monoPow _ _ k h := Nat.pow_lt_pow_left (by omega) (by omega)
  monoPowNeg _ _ _ h := by omega

/-- Weight of the `sum_to_product` profile. -/
def sumToProductWeight : Weight where
  int _ := 1
  const _ := 1
  op1 o a := match o with
    | .sin | .cos => 3 * a + 5
    | _ => a + 1
  op2 o a b := match o with
    | .add | .sub => (a + 1) * (b + 1)
    | _ => a + b + 1
  pow a k := a + k + 1
  powNeg a k := a + k + 2
  mono1 o a a' h := by cases o <;> simp only <;> omega
  mono2l o a a' b h := by cases o <;> simp only <;> first | omega | nlinarith
  mono2r o a b b' h := by cases o <;> simp only <;> first | omega | nlinarith
  monoPow _ _ _ h := by omega
  monoPowNeg _ _ _ h := by omega

/-- The weight proving termination of a profile. -/
def weight : String → Weight
  | "default" => defaultWeight
  | "product_to_sum" => productToSumWeight
  | "power_reduction" => powerReductionWeight
  | _ => sumToProductWeight

theorem profileRules_default :
    profileRules "default" = [pythagorean, sinAdd, cosSub, sinTwoMul, cosTwoMul, tanArctan] :=
  rfl

theorem profileRules_productToSum :
    profileRules "product_to_sum" = [pythagorean, sinMulCos, sinMulSin, tanArctan] :=
  rfl

theorem profileRules_powerReduction :
    profileRules "power_reduction" = [pythagorean, sinSq, cosSq, tanArctan] :=
  rfl

theorem profileRules_sumToProduct :
    profileRules "sum_to_product" = [pythagorean, sinAddSin, cosAddCos, cosSubCos, tanArctan] :=
  rfl

private theorem one_le_eight_pow (n : Nat) : 1 ≤ 8 ^ n := Nat.one_le_pow _ _ (by norm_num)

theorem default_decreasing : ∀ r ∈ profileRules "default", defaultWeight.Decreases r := by
  rw [profileRules_default]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro env <;>
    simp only [Weight.eval, defaultWeight, pythagorean, sinAdd, cosSub, sinTwoMul, cosTwoMul,
      tanArctan]
  · have := one_le_eight_pow (env "x"); ring_nf; nlinarith
  · have := one_le_eight_pow (env "x"); have := one_le_eight_pow (env "y")
    ring_nf; nlinarith
  · have := one_le_eight_pow (env "x"); have := one_le_eight_pow (env "y")
    ring_nf; nlinarith
  · have := one_le_eight_pow (env "x"); ring_nf; nlinarith
  · have := one_le_eight_pow (env "x"); ring_nf; nlinarith
  · omega

theorem productToSum_decreasing :
    ∀ r ∈ profileRules "product_to_sum", productToSumWeight.Decreases r := by
  rw [profileRules_productToSum]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro env <;>
    simp only [Weight.eval, productToSumWeight, pythagorean, sinMulCos, sinMulSin, tanArctan]
  all_goals nlinarith

theorem powerReduction_decreasing :
    ∀ r ∈ profileRules "power_reduction", powerReductionWeight.Decreases r := by
  rw [profileRules_powerReduction]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro env <;>
    simp only [Weight.eval, powerReductionWeight, pythagorean, sinSq, cosSq, tanArctan]
  all_goals first | omega | (ring_nf; nlinarith)

theorem sumToProduct_decreasing :
    ∀ r ∈ profileRules "sum_to_product", sumToProductWeight.Decreases r := by
  rw [profileRules_sumToProduct]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro env <;>
    simp only [Weight.eval, sumToProductWeight, pythagorean, sinAddSin, cosAddCos, cosSubCos,
      tanArctan]
  all_goals first | omega | (ring_nf; nlinarith)

theorem default_terminates : Terminates (profileRules "default") defaultWeight :=
  defaultWeight.terminates _ default_decreasing

theorem productToSum_terminates :
    Terminates (profileRules "product_to_sum") productToSumWeight :=
  productToSumWeight.terminates _ productToSum_decreasing

theorem powerReduction_terminates :
    Terminates (profileRules "power_reduction") powerReductionWeight :=
  powerReductionWeight.terminates _ powerReduction_decreasing

theorem sumToProduct_terminates :
    Terminates (profileRules "sum_to_product") sumToProductWeight :=
  sumToProductWeight.terminates _ sumToProduct_decreasing

/-- **Termination.**  For every profile and every expression, the reference
engine reaches a normal form within the weight of the expression. -/
theorem normalize_terminates (p : String) (hp : p ∈ profiles) :
    Terminates (profileRules p) (weight p) := by
  simp only [profiles, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  exacts [default_terminates, productToSum_terminates, powerReduction_terminates,
    sumToProduct_terminates]

end OSR.Trigonometry
