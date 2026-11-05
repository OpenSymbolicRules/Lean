import OSR.Catalog

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
* the `default` profile is the v0.1 default `load_order`; `sum_to_product` is
  the v0.1 profile of the same name.  Priority is the v0.1 load position
  (file order, then position in the file), times ten.

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

private def both : List String := ["default", "sum_to_product"]

/-! ## Rules -/

/-- `sin(x)^2 + cos(x)^2 ⟶ 1`. -/
def pythagorean : Rule where
  id := "trigonometry.pythagorean"
  legacyId := some "trigonometry:1-basic-identities/1.1-pythagorean:1"
  vars := ["x"]
  lhs := add (sq (sin x)) (sq (cos x))
  rhs := .int 1
  profiles := both
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
  profiles := both
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
  profiles := both
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
  profiles := both
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
  profiles := both
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
  profiles := ["default"]
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
  profiles := ["default"]
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
  profiles := both
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
  profiles := both
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
  profiles := both
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

/-- The Trigonometry catalogue, in v0.1 load order. -/
def catalog : List CatalogEntry := [
  { rule := pythagorean, ruleDecl := ``pythagorean,
    proofs := [(.real, ``pythagorean_real), (.complex, ``pythagorean_complex)] },
  { rule := sinAdd, ruleDecl := ``sinAdd,
    proofs := [(.real, ``sinAdd_real), (.complex, ``sinAdd_complex)],
    findings := ["operational: in the default profile, trigonometry.angle_sum.sin_add and trigonometry.product_to_sum.sin_cos form a rewrite cycle (sin(x + y) is reproduced); a terminating strategy must not enable both. Both rules are proved; this is a strategy property, not a mathematical error."] },
  { rule := cosSub, ruleDecl := ``cosSub,
    proofs := [(.real, ``cosSub_real), (.complex, ``cosSub_complex)] },
  { rule := sinTwoMul, ruleDecl := ``sinTwoMul,
    proofs := [(.real, ``sinTwoMul_real), (.complex, ``sinTwoMul_complex)] },
  { rule := cosTwoMul, ruleDecl := ``cosTwoMul,
    proofs := [(.real, ``cosTwoMul_real), (.complex, ``cosTwoMul_complex)] },
  { rule := sinMulCos, ruleDecl := ``sinMulCos,
    proofs := [(.real, ``sinMulCos_real), (.complex, ``sinMulCos_complex)],
    findings := ["operational: in the default profile, trigonometry.angle_sum.sin_add and trigonometry.product_to_sum.sin_cos form a rewrite cycle (sin(x + y) is reproduced); a terminating strategy must not enable both. Both rules are proved; this is a strategy property, not a mathematical error."] },
  { rule := sinMulSin, ruleDecl := ``sinMulSin,
    proofs := [(.real, ``sinMulSin_real), (.complex, ``sinMulSin_complex)] },
  { rule := sinSq, ruleDecl := ``sinSq,
    proofs := [(.real, ``sinSq_real), (.complex, ``sinSq_complex)] },
  { rule := cosSq, ruleDecl := ``cosSq,
    proofs := [(.real, ``cosSq_real), (.complex, ``cosSq_complex)] },
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

end OSR.Trigonometry
