import OSR.Rule
import OSR.LogicOps

/-!
# Registry contents for the Trigonometry pilot

Each entry relates one OpenMath symbol to its real and complex Lean
interpretations.  CD snapshots are pinned by SHA-256; the files are in the
`OpenSymbolicRules/OpenMath` repository (`cd/*.ocd`), downloaded from
`https://openmath.org/cd/`.

Obligations name the CD property (CMP text) they establish.  Where the Lean
statement is not literally the CMP, the note says how they relate.
-/

namespace OSR.Registry

open OSR

/-- Pinned content dictionaries used by the registry. -/
def cds : List CDRef := [
  { cd := "arith1", version := 3, revision := 1, date := "2004-03-30",
    sha256 := "8dab1c657db03b87da8ed3a139c2490df0e86076ab634c3804b757c5594f6d8a" },
  { cd := "transc1", version := 3, revision := 1, date := "2004-03-30",
    sha256 := "75ed9e263f1256e957d56fc30648835d3d0a0c1fc375947b0a2fa1bdf71a177d" },
  { cd := "nums1", version := 4, revision := 0, date := "2009-04-01",
    sha256 := "691c8ebfaad1375bdd54c6084b223a093782aacc634151bdb49ba70938ddbbe5" },
  { cd := "relation1", version := 3, revision := 1, date := "2004-03-30",
    sha256 := "1c50e72514373c6d60c3f82c28936670ccb8615e8cf85b40de6ee747487842e6" },
  { cd := "set1", version := 3, revision := 1, date := "2004-03-30",
    sha256 := "6d4995d2e7f1f24e062f52f600f33cceabe24e3055927e668dbea6a5dd0c5ea2" },
  { cd := "logic1", version := 4, revision := 0, date := "2004-03-30",
    sha256 := "5bd450962d9ee3f867770608ce6f823b0ad705123afb9af5d1950a39a46498cd" },
  { cd := "calculus1", version := 5, revision := 0, date := "2009-04-01",
    sha256 := "bd61e71618800e50935bd4f8503ad3d7bd7f131456854cb5d7cb49fa3df780e7" },
  { cd := "fns1", version := 4, revision := 0, date := "2009-04-01",
    sha256 := "9d45eafcb9b527de68dee8f2a129fe8ec71667ef8490fa5e50ddb7eedd3f8c5e" },
  { cd := "limit1", version := 3, revision := 1, date := "2004-03-30",
    sha256 := "b104ee1a78b9c0528344b5b375ce1790296ddeaca9d8ef5429a80e4ae4e049c6" },
  { cd := "quant1", version := 3, revision := 2, date := "2004-05-11",
    sha256 := "58e065460b461514e83fc432372e1b598a5a589ed8c5992d20913a20c49db928" },
  { cd := "setname2", version := 3, revision := 1, date := "2004-03-30",
    sha256 := "666e623a6164874963ef8263a13f471ff0abaa14adb95c1609352dfe6667fb21" },
  { cd := "setname1", version := 3, revision := 1, date := "2004-03-30",
    sha256 := "746cc460c6aec8601d72dbfe16b99451dcd24f165b2d9ec4f77b4f391bd54abd" }
]

/-! ## Semantic obligations not stated verbatim in Mathlib -/

/-- `transc1#sin` CMP 1 over ℂ: `sin(x) = (exp(ix) - exp(-ix)) / 2i`. -/
theorem complex_sin_exp (z : ℂ) :
    Complex.sin z = (Complex.exp (Complex.I * z) - Complex.exp (-(Complex.I * z))) /
      (2 * Complex.I) := by
  rw [Complex.sin]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring_nf

/-- `transc1#cos` CMP 1 over ℂ: `cos(x) = (exp(ix) + exp(-ix)) / 2`. -/
theorem complex_cos_exp (z : ℂ) :
    Complex.cos z = (Complex.exp (Complex.I * z) + Complex.exp (-(Complex.I * z))) / 2 := by
  rw [Complex.cos]
  ring_nf

/-- `transc1#sin` CMP 3: `sin A = - sin(-A)` (real). -/
theorem real_sin_cmp3 (a : ℝ) : Real.sin a = -Real.sin (-a) := by
  rw [Real.sin_neg, neg_neg]

/-- `transc1#sin` CMP 3: `sin A = - sin(-A)` (complex). -/
theorem complex_sin_cmp3 (a : ℂ) : Complex.sin a = -Complex.sin (-a) := by
  rw [Complex.sin_neg, neg_neg]

/-- `transc1#cos` CMP 3: `cos A = cos(-A)` (real). -/
theorem real_cos_cmp3 (a : ℝ) : Real.cos a = Real.cos (-a) := (Real.cos_neg a).symm

/-- `transc1#cos` CMP 3: `cos A = cos(-A)` (complex). -/
theorem complex_cos_cmp3 (a : ℂ) : Complex.cos a = Complex.cos (-a) := (Complex.cos_neg a).symm

/-- `arith1#power` CMP 2 (successor step) for natural exponents. -/
theorem pow_cmp2 {α : Type} [Monoid α] (x : α) (n : ℕ) : x ^ (n + 1) = x * x ^ n :=
  pow_succ' x n

/-- `transc1#exp` CMP: `e^(z + 2πki) = e^z` for every integer `k` (complex). -/
theorem complex_exp_cmp (z : ℂ) (k : ℤ) :
    Complex.exp (z + 2 * Real.pi * k * Complex.I) = Complex.exp z := by
  rw [Complex.exp_add]
  have : (2 * Real.pi * k * Complex.I : ℂ) = k * (2 * Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `setname1#Z` CMP: `z` is an integer iff `z` or `-z` is a natural number;
the set of integers of a field is the range of the cast. -/
theorem setname1_Z_cmp {α : Type} [Field α] (v : α) :
    v ∈ Set.range (Int.cast : ℤ → α) ↔ ∃ n : ℕ, v = n ∨ -v = n := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨n, h | h⟩ := Int.eq_nat_or_neg z
    · exact ⟨n, Or.inl (by simp [h])⟩
    · exact ⟨n, Or.inr (by simp [h])⟩
  · rintro ⟨n, h | h⟩
    · exact ⟨n, by simp [h]⟩
    · exact ⟨-n, by simp [← h]⟩

/-- `relation1#gt` CMP: `a > b ∧ b > c → a > c` (real). -/
theorem real_gt_cmp (a b c : ℝ) (h₁ : a > b) (h₂ : b > c) : a > c := lt_trans h₂ h₁

/-- `arith1#power` CMP 2 for integer exponents and a nonzero base. -/
theorem zpow_cmp2 {α : Type} [Field α] (x : α) (hx : x ≠ 0) (n : ℤ) :
    x ^ n = x * x ^ (n - 1) := by
  rw [zpow_sub_one₀ hx]
  field_simp

/-- `fns1#lambda`: Lean's own `fun` abstraction has no constant; this
identity names the function a lambda term denotes. -/
def lambda {α : Type} (f : α → α) : α → α := f

/-! ## Obligations of the further transc1 functions and arith1#root -/

theorem real_sinh_cmp (x : ℝ) : Real.sinh x = 1 / 2 * (Real.exp x - Real.exp (-x)) := by
  rw [Real.sinh_eq]; ring
theorem real_cosh_cmp (x : ℝ) : Real.cosh x = 1 / 2 * (Real.exp x + Real.exp (-x)) := by
  rw [Real.cosh_eq]; ring
theorem complex_sinh_cmp (z : ℂ) : Complex.sinh z = 1 / 2 * (Complex.exp z - Complex.exp (-z)) := by
  rw [Complex.sinh]; ring
theorem complex_cosh_cmp (z : ℂ) : Complex.cosh z = 1 / 2 * (Complex.exp z + Complex.exp (-z)) := by
  rw [Complex.cosh]; ring
theorem real_coth_cmp (x : ℝ) : Fn.coth x = 1 / Real.tanh x := rfl
theorem real_sech_cmp (x : ℝ) : Fn.sech x = 1 / Real.cosh x := rfl
theorem real_csch_cmp (x : ℝ) : Fn.csch x = 1 / Real.sinh x := rfl
theorem real_sec_cmp (x : ℝ) : Fn.sec x = 1 / Real.cos x := rfl
theorem real_csc_cmp (x : ℝ) : Fn.csc x = 1 / Real.sin x := rfl
theorem real_cot_cmp (x : ℝ) : Real.cot x = 1 / Real.tan x := by
  rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, one_div_div]
theorem complex_cot_cmp (z : ℂ) : Complex.cot z = 1 / Complex.tan z := by
  rw [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, one_div_div]
theorem real_arcsinh_cmp (x : ℝ) : Real.arsinh x = Real.log (x + Real.sqrt (1 + x ^ 2)) := rfl
theorem real_root_cmp (a : ℝ) (h : 0 ≤ a) : Real.sqrt a ^ 2 = a := Real.sq_sqrt h

/-! ## Entries -/

private def arithInterp (d : Domain) (c : Lean.Name) (obl : List Obligation)
    (defn : String := "everywhere") : Interpretation :=
  { domain := d, leanConst := c, assurance := .formallyRelated, definedness := defn,
    justification := "Field operation of the carrier; the CMPs listed hold in any field.",
    obligations := obl }

/-- The registry. -/
def entries : List SymbolEntry := [
  { symbol := ⟨"arith1", "plus"⟩, arity := 2,
    fragment := "binary only; the CD symbol is n-ary (an n-ary sum is a left-nested chain)",
    interpretations := [Domain.real, Domain.complex].map fun d =>
      arithInterp d ``HAdd.hAdd [{ cmp := "for all a,b | a + b = b + a", theoremName := ``add_comm }] },
  { symbol := ⟨"arith1", "minus"⟩, arity := 2,
    interpretations := [Domain.real, Domain.complex].map fun d =>
      arithInterp d ``HSub.hSub [{ cmp := "for all a,b | a - b = a + (-b)", theoremName := ``sub_eq_add_neg }] },
  { symbol := ⟨"arith1", "times"⟩, arity := 2,
    fragment := "binary only; the CD symbol is n-ary (an n-ary product is a left-nested chain)",
    interpretations := [Domain.real, Domain.complex].map fun d =>
      arithInterp d ``HMul.hMul [
        { cmp := "for all a,b | a * 0 = 0 and a * b = a * (b - 1) + a", theoremName := ``mul_zero,
          note := "first conjunct only" },
        { cmp := "for all a,b,c | a*(b+c) = a*b + a*c", theoremName := ``mul_add }] },
  { symbol := ⟨"arith1", "divide"⟩, arity := 2,
    interpretations := [Domain.real, Domain.complex].map fun d =>
      arithInterp d ``HDiv.hDiv [{ cmp := "whenever not(a=0) then a/a = 1", theoremName := ``div_self }]
        "divisor ≠ 0 (Lean totalizes x / 0 = 0; `Defined` requires a nonzero divisor)" },
  { symbol := ⟨"arith1", "unary_minus"⟩, arity := 1,
    interpretations := [Domain.real, Domain.complex].map fun d =>
      arithInterp d ``Neg.neg [{ cmp := "for all a | a + (-a) = 0", theoremName := ``add_neg_cancel }] },
  { symbol := ⟨"arith1", "power"⟩, arity := 2,
    fragment := "interpreted for integer exponents only; general powers (CMP 1, exp/ln) are out of scope, so a power with a non-integer exponent is undefined in the fragment",
    interpretations := [Domain.real, Domain.complex].map fun d =>
      { domain := d, leanConst := ``HPow.hPow, assurance := .formallyRelated,
        definedness := "integer exponent, and nonzero base if the exponent is negative (0^0 = 1 as in CMP 2)",
        justification := "Group-with-zero power by an integer (zpow) agrees with the integer-exponent recursion of CMP 2.",
        obligations := [
          { cmp := "if n is an integer then x^0 = 1", theoremName := ``zpow_zero },
          { cmp := "if n is an integer then x^n = x * x^(n-1)", theoremName := ``zpow_cmp2,
            note := "for x ≠ 0; at x = 0 the CMP would need 0^(-1), which is undefined" },
          { cmp := "if n is an integer then x^n = x * x^(n-1)", theoremName := ``pow_cmp2,
            note := "for natural n, every x, as x^(n+1) = x * x^n" }] } },
  { symbol := ⟨"transc1", "sin"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.sin, assurance := .formallyRelated, definedness := "everywhere",
        justification := "Restriction of Complex.sin to ℝ (Complex.ofReal_sin).",
        obligations := [
          { cmp := "sin(A + B) = sin A cos B + cos A sin B", theoremName := ``Real.sin_add },
          { cmp := "sin A = - sin(-A)", theoremName := ``real_sin_cmp3 },
          { cmp := "(real/complex agreement)", theoremName := ``Complex.ofReal_sin,
            note := "not a CMP; relates the real and complex interpretations" }] },
      { domain := .complex, leanConst := ``Complex.sin, assurance := .formallyRelated, definedness := "everywhere",
        justification := "Entire sine function, defined by the exponential formula of CMP 1.",
        obligations := [
          { cmp := "sin(x) = (exp(ix)-exp(-ix))/2i", theoremName := ``complex_sin_exp },
          { cmp := "sin(A + B) = sin A cos B + cos A sin B", theoremName := ``Complex.sin_add },
          { cmp := "sin A = - sin(-A)", theoremName := ``complex_sin_cmp3 }] }] },
  { symbol := ⟨"transc1", "cos"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.cos, assurance := .formallyRelated, definedness := "everywhere",
        justification := "Restriction of Complex.cos to ℝ (Complex.ofReal_cos).",
        obligations := [
          { cmp := "cos 2A = cos^2 A - sin^2 A", theoremName := ``Real.cos_two_mul' },
          { cmp := "cos A = cos(-A)", theoremName := ``real_cos_cmp3 },
          { cmp := "(real/complex agreement)", theoremName := ``Complex.ofReal_cos,
            note := "not a CMP; relates the real and complex interpretations" }] },
      { domain := .complex, leanConst := ``Complex.cos, assurance := .formallyRelated, definedness := "everywhere",
        justification := "Entire cosine function, defined by the exponential formula of CMP 1.",
        obligations := [
          { cmp := "cos(x) = (exp(ix)+exp(-ix))/2", theoremName := ``complex_cos_exp },
          { cmp := "cos 2A = cos^2 A - sin^2 A", theoremName := ``Complex.cos_two_mul' },
          { cmp := "cos A = cos(-A)", theoremName := ``complex_cos_cmp3 }] }] },
  { symbol := ⟨"transc1", "tan"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.tan, assurance := .formallyRelated,
        definedness := "cos x ≠ 0 (Lean totalizes tan at poles to 0)",
        justification := "Defined as sin/cos, matching the CMP where cos x ≠ 0.",
        obligations := [
          { cmp := "tan A = sin A / cos A", theoremName := ``Real.tan_eq_sin_div_cos },
          { cmp := "(real/complex agreement)", theoremName := ``Complex.ofReal_tan,
            note := "not a CMP; relates the real and complex interpretations" }] },
      { domain := .complex, leanConst := ``Complex.tan, assurance := .formallyRelated,
        definedness := "cos z ≠ 0 (Lean totalizes tan at poles to 0)",
        justification := "Defined as sin/cos, matching the CMP where cos z ≠ 0.",
        obligations := [{ cmp := "tan A = sin A / cos A", theoremName := ``Complex.tan_eq_sin_div_cos }] }] },
  { symbol := ⟨"transc1", "arctan"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.arctan, assurance := .formallyRelated, definedness := "everywhere",
        justification := "Inverse of tan restricted to (-π/2, π/2), as in CMP 2.",
        obligations := [
          { cmp := "x in (-(pi/2),(pi/2)) implies arctan(tan x) = x", theoremName := ``Real.arctan_tan },
          { cmp := "(real/complex agreement)", theoremName := ``Complex.ofReal_arctan,
            note := "not a CMP; relates the real and complex interpretations" }] },
      { domain := .complex, leanConst := ``Complex.arctan, assurance := .provisional,
        definedness := "z ≠ i and z ≠ -i (Lean assigns values at ±i)",
        justification := "Principal inverse tangent; agrees with the CMP 1 logarithmic formula off the branch cuts.",
        obligations := [],
        unresolved := [
          "Mathlib defines arctan z = -i/2 · log((1 + z i)/(1 - z i)); CMP 1 is (i/2) ln((1 - i z)/(1 + i z)). Equality off the branch cuts is not proved here.",
          "Values on the branch cuts (z = i y, |y| > 1) depend on the logarithm's cut convention; agreement with OpenMath there is unverified.",
          "Complex.arctan_tan requires -(π/2) < re z ≤ π/2 and z ≠ π/2, not the open real interval of CMP 2."] }] },
  { symbol := ⟨"transc1", "exp"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.exp, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "The real exponential; the restriction of the complex one.",
        obligations := [
          { cmp := "(real/complex agreement)", theoremName := ``Complex.ofReal_exp,
            note := "not a CMP; relates the real and complex interpretations" }] },
      { domain := .complex, leanConst := ``Complex.exp, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "The complex exponential (power series), as in Abramowitz and Stegun 4.2.",
        obligations := [
          { cmp := "for all k if k is an integer then e^(z+2*pi*k*i)=e^z",
            theoremName := ``complex_exp_cmp }] }] },
  { symbol := ⟨"transc1", "ln"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.log, assurance := .formallyRelated,
        definedness := "x > 0 (Lean totalizes: log 0 = 0, log (-x) = log x)",
        justification := "The natural logarithm on the positive reals, where it agrees with the principal complex logarithm.",
        obligations := [
          { cmp := "(real/complex agreement)", theoremName := ``Complex.ofReal_log,
            note := "not a CMP; for x ≥ 0 the real logarithm is the principal complex one" }] },
      { domain := .complex, leanConst := ``Complex.log, assurance := .formallyRelated,
        definedness := "z ≠ 0 (Lean assigns log 0 = 0)",
        justification := "Principal logarithm log |z| + i arg z with arg in (-π, π], the branch cut of the CMP.",
        obligations := [
          { cmp := "-pi < Im ln x <= pi", theoremName := ``Complex.neg_pi_lt_log_im,
            note := "lower bound" },
          { cmp := "-pi < Im ln x <= pi", theoremName := ``Complex.log_im_le_pi,
            note := "upper bound" }] }] },
  { symbol := ⟨"logic1", "and"⟩, arity := 2,
    fragment := "binary only; the CD symbol is n-ary (longer chains are left-nested)",
    interpretations := [
      { domain := .boolean, leanConst := ``and, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Two-valued Boolean function on Lean's Bool.",
        obligations := [
          { cmp := "for all x | x and not(x) = false", theoremName := ``OSR.Logic.and_cmp }] }] },
  { symbol := ⟨"logic1", "or"⟩, arity := 2,
    fragment := "binary only; the CD symbol is n-ary (longer chains are left-nested)",
    interpretations := [
      { domain := .boolean, leanConst := ``or, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Two-valued Boolean function on Lean's Bool.",
        obligations := [
          { cmp := "for all x | x or not(x) = true", theoremName := ``OSR.Logic.or_cmp1 },
          { cmp := "for all a,b | not(a and b)= (not(a) or not(b))", theoremName := ``OSR.Logic.or_cmp2 }] }] },
  { symbol := ⟨"logic1", "not"⟩, arity := 1,
    interpretations := [
      { domain := .boolean, leanConst := ``not, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Two-valued Boolean function on Lean's Bool.",
        obligations := [
          { cmp := "for all x | not(not(x))=x", theoremName := ``OSR.Logic.not_cmp }] }] },
  { symbol := ⟨"logic1", "implies"⟩, arity := 2,
    interpretations := [
      { domain := .boolean, leanConst := ``OSR.Logic.implies, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Two-valued Boolean function on Lean's Bool.",
        obligations := [
          { cmp := "for all x | false implies x", theoremName := ``OSR.Logic.implies_cmp }] }] },
  { symbol := ⟨"logic1", "equivalent"⟩, arity := 2,
    interpretations := [
      { domain := .boolean, leanConst := ``OSR.Logic.equivalent, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Two-valued Boolean function on Lean's Bool.",
        obligations := [
          { cmp := "The condition (A is equivalent to B) is equivalent to the condition that (A implies B and B implies A)", theoremName := ``OSR.Logic.equivalent_cmp }] }] },
  { symbol := ⟨"logic1", "nand"⟩, arity := 2,
    fragment := "binary only; the CD symbol is n-ary (longer chains are left-nested)",
    interpretations := [
      { domain := .boolean, leanConst := ``OSR.Logic.nand, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Two-valued Boolean function on Lean's Bool.",
        obligations := [
          { cmp := "for all x | x nand not(x) = true", theoremName := ``OSR.Logic.nand_cmp }] }] },
  { symbol := ⟨"logic1", "nor"⟩, arity := 2,
    fragment := "binary only; the CD symbol is n-ary (longer chains are left-nested)",
    interpretations := [
      { domain := .boolean, leanConst := ``OSR.Logic.nor, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Two-valued Boolean function on Lean's Bool.",
        obligations := [
          { cmp := "for all x | x nor not(x) = false", theoremName := ``OSR.Logic.nor_cmp1 },
          { cmp := "for all a,b | a and b = (not(a) nor not(b))", theoremName := ``OSR.Logic.nor_cmp2 }] }] },
  { symbol := ⟨"logic1", "xor"⟩, arity := 2,
    fragment := "binary only; the CD symbol is n-ary (longer chains are left-nested)",
    interpretations := [
      { domain := .boolean, leanConst := ``Bool.xor, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Two-valued Boolean function on Lean's Bool.",
        obligations := [
          { cmp := "for all x | x xor x = false", theoremName := ``OSR.Logic.xor_cmp1 },
          { cmp := "for all x | x xor not(x) = true", theoremName := ``OSR.Logic.xor_cmp2 }] }] },
  { symbol := ⟨"logic1", "xnor"⟩, arity := 2,
    fragment := "binary only; the CD symbol is n-ary (longer chains are left-nested)",
    interpretations := [
      { domain := .boolean, leanConst := ``OSR.Logic.xnor, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Two-valued Boolean function on Lean's Bool.",
        obligations := [
          { cmp := "for all x | x xnor x = true", theoremName := ``OSR.Logic.xnor_cmp1 },
          { cmp := "for all x | x xnor not(x) = false", theoremName := ``OSR.Logic.xnor_cmp2 }] }] },
  { symbol := ⟨"logic1", "true"⟩, arity := 0,
    interpretations := [
      { domain := .boolean, leanConst := ``Bool.true, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Two-valued Boolean function on Lean's Bool.",
        obligations := [
          { cmp := "not true = false", theoremName := ``OSR.Logic.true_cmp }] }] },
  { symbol := ⟨"logic1", "false"⟩, arity := 0,
    interpretations := [
      { domain := .boolean, leanConst := ``Bool.false, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Two-valued Boolean function on Lean's Bool.",
        obligations := [
          { cmp := "not false = true", theoremName := ``OSR.Logic.false_cmp }] }] },
  { symbol := ⟨"calculus1", "diff"⟩, arity := 1,
    fragment := "applied to a lambda term; a rule states HasDerivAt where the body is defined near the point",
    interpretations := [Domain.real, Domain.complex].map fun d =>
      { domain := d, leanConst := ``deriv, assurance := .reviewed,
        definedness := "where the function is differentiable",
        justification := "Ordinary derivative of a unary function; rules state HasDerivAt, which implies deriv f t = f'(t). The CMPs (sum and product rules) hold for differentiable functions (deriv_add, deriv_mul)." } },
  { symbol := ⟨"fns1", "lambda"⟩, arity := 0,
    fragment := "binder (OMBIND) with one bound variable",
    interpretations := [Domain.real, Domain.complex].map fun d =>
      { domain := d, leanConst := ``OSR.Registry.lambda, assurance := .reviewed,
        definedness := "everywhere",
        justification := "Lambda abstraction: the function v ↦ body[x := v] (Lean's fun)." } },
  { symbol := ⟨"limit1", "limit"⟩, arity := 3,
    fragment := "two-sided limits only (limit1#both_sides), of a lambda term",
    interpretations := [Domain.real, Domain.complex].map fun d =>
      { domain := d, leanConst := ``Filter.Tendsto, assurance := .reviewed,
        definedness := "where the limit exists",
        justification := "limit(a, both_sides, f) = L is stated as Tendsto f (𝓝[≠] a) (𝓝 L)." } },
  { symbol := ⟨"limit1", "both_sides"⟩, arity := 0,
    fragment := "method of approach of limit1#limit",
    interpretations := [Domain.real, Domain.complex].map fun d =>
      { domain := d, leanConst := ``nhdsWithin, assurance := .reviewed,
        definedness := "constant",
        justification := "Approach from both sides: the punctured neighbourhood filter 𝓝[≠] a." } },
  { symbol := ⟨"quant1", "forall"⟩, arity := 0,
    fragment := "binder (OMBIND) with one bound variable; quantifies over the truth values",
    interpretations := [
      { domain := .boolean, leanConst := ``OSR.Logic.forallBool, assurance := .reviewed,
        definedness := "everywhere",
        justification := "Universal quantification over the Booleans: ∀x. φ is φ[x := true] ∧ φ[x := false] (OSR.Logic.forallBool_iff). The CD states no CMP." }] },
  { symbol := ⟨"quant1", "exists"⟩, arity := 0,
    fragment := "binder (OMBIND) with one bound variable; quantifies over the truth values",
    interpretations := [
      { domain := .boolean, leanConst := ``OSR.Logic.existsBool, assurance := .reviewed,
        definedness := "everywhere",
        justification := "Existential quantification over the Booleans: ∃x. φ is φ[x := true] ∨ φ[x := false] (OSR.Logic.existsBool_iff). The CD states no CMP." }] },
  { symbol := ⟨"setname2", "Boolean"⟩, arity := 0,
    fragment := "carrier of the boolean domain",
    interpretations := [
      { domain := .boolean, leanConst := ``Bool, assurance := .formallyRelated,
        definedness := "constant",
        justification := "Lean's two-valued type Bool.",
        obligations := [
          { cmp := "for all b in the booleans | (there exists an nb in the booleans | nb not= b implies nb = not b)",
            theoremName := ``OSR.Logic.boolean_cmp }] }] },
  { symbol := ⟨"transc1", "sinh"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.sinh, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Mathlib's real hyperbolic sine.",
        obligations := [
          { cmp := "sinh A = 1/2 * (e^A - e^(-A))", theoremName := ``real_sinh_cmp }] },
      { domain := .complex, leanConst := ``Complex.sinh, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Mathlib's complex hyperbolic sine.",
        obligations := [
          { cmp := "sinh A = 1/2 * (e^A - e^(-A))", theoremName := ``complex_sinh_cmp }] }] },
  { symbol := ⟨"transc1", "cosh"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.cosh, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Mathlib's real hyperbolic cosine.",
        obligations := [
          { cmp := "cosh A = 1/2 * (e^A + e^(-A))", theoremName := ``real_cosh_cmp }] },
      { domain := .complex, leanConst := ``Complex.cosh, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Mathlib's complex hyperbolic cosine.",
        obligations := [
          { cmp := "cosh A = 1/2 * (e^A + e^(-A))", theoremName := ``complex_cosh_cmp }] }] },
  { symbol := ⟨"transc1", "tanh"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.tanh, assurance := .formallyRelated,
        definedness := "everywhere (cosh > 0)",
        justification := "Mathlib's real hyperbolic tangent.",
        obligations := [
          { cmp := "tanh A = sinh A / cosh A", theoremName := ``Real.tanh_eq_sinh_div_cosh }] },
      { domain := .complex, leanConst := ``Complex.tanh, assurance := .formallyRelated,
        definedness := "cosh z ≠ 0",
        justification := "Mathlib's complex hyperbolic tangent.",
        obligations := [
          { cmp := "tanh A = sinh A / cosh A", theoremName := ``Complex.tanh_eq_sinh_div_cosh }] }] },
  { symbol := ⟨"transc1", "coth"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``OSR.Fn.coth, assurance := .formallyRelated,
        definedness := "sinh x ≠ 0",
        justification := "Defined as in the CMP.",
        obligations := [
          { cmp := "coth A = 1/tanh A", theoremName := ``real_coth_cmp }] }] },
  { symbol := ⟨"transc1", "sech"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``OSR.Fn.sech, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Defined as in the CMP.",
        obligations := [
          { cmp := "sech A = 1/cosh A", theoremName := ``real_sech_cmp }] }] },
  { symbol := ⟨"transc1", "csch"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``OSR.Fn.csch, assurance := .formallyRelated,
        definedness := "sinh x ≠ 0",
        justification := "Defined as in the CMP.",
        obligations := [
          { cmp := "csch A = 1/sinh A", theoremName := ``real_csch_cmp }] }] },
  { symbol := ⟨"transc1", "cot"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.cot, assurance := .formallyRelated,
        definedness := "sin x ≠ 0",
        justification := "Mathlib's real cotangent.",
        obligations := [
          { cmp := "cot A = 1/tan A", theoremName := ``real_cot_cmp }] },
      { domain := .complex, leanConst := ``Complex.cot, assurance := .formallyRelated,
        definedness := "sin z ≠ 0",
        justification := "Mathlib's complex cotangent.",
        obligations := [
          { cmp := "cot A = 1/tan A", theoremName := ``complex_cot_cmp }] }] },
  { symbol := ⟨"transc1", "sec"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``OSR.Fn.sec, assurance := .formallyRelated,
        definedness := "cos x ≠ 0",
        justification := "Defined as in the CMP.",
        obligations := [
          { cmp := "sec A = 1/cos A", theoremName := ``real_sec_cmp }] }] },
  { symbol := ⟨"transc1", "csc"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``OSR.Fn.csc, assurance := .formallyRelated,
        definedness := "sin x ≠ 0",
        justification := "Defined as in the CMP.",
        obligations := [
          { cmp := "csc A = 1/sin A", theoremName := ``real_csc_cmp }] }] },
  { symbol := ⟨"transc1", "arcsin"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.arcsin, assurance := .formallyRelated,
        definedness := "-1 ≤ x ≤ 1 (Lean clamps outside)",
        justification := "Mathlib's real arcsine, the inverse of sin on [-π/2, π/2].",
        obligations := [
          { cmp := "x in [-(pi/2),(pi/2)] implies arcsin(sin x) = x", theoremName := ``Real.arcsin_sin }] }] },
  { symbol := ⟨"transc1", "arccos"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.arccos, assurance := .formallyRelated,
        definedness := "-1 ≤ x ≤ 1 (Lean clamps outside)",
        justification := "Mathlib's real arccosine, the inverse of cos on [0, π].",
        obligations := [
          { cmp := "x in [0,pi] implies arccos(cos x) = x", theoremName := ``Real.arccos_cos }] }] },
  { symbol := ⟨"transc1", "arcsinh"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.arsinh, assurance := .formallyRelated,
        definedness := "everywhere",
        justification := "Mathlib's real inverse hyperbolic sine.",
        obligations := [
          { cmp := "arcsinh z = ln(z + sqrt(1+z^2))", theoremName := ``real_arcsinh_cmp }] }] },
  { symbol := ⟨"transc1", "arccosh"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.arcosh, assurance := .reviewed,
        definedness := "x ≥ 1",
        justification := "Mathlib's real inverse hyperbolic cosine on [1, ∞)." }] },
  { symbol := ⟨"transc1", "arctanh"⟩, arity := 1,
    interpretations := [
      { domain := .real, leanConst := ``Real.artanh, assurance := .reviewed,
        definedness := "-1 < x < 1",
        justification := "Mathlib's real inverse hyperbolic tangent on (-1, 1)." }] },
  { symbol := ⟨"arith1", "root"⟩, arity := 2,
    fragment := "square root only (second argument 2); no complex interpretation",
    interpretations := [
      { domain := .real, leanConst := ``Real.sqrt, assurance := .formallyRelated,
        definedness := "second argument 2 and first argument ≥ 0",
        justification := "root(x, 2) is the nonnegative square root.",
        obligations := [
          { cmp := "for all a,n | power(root(a,n),n) = a (if the root exists!)", theoremName := ``real_root_cmp, note := "for n = 2 and a ≥ 0" }] }] },
  { symbol := ⟨"nums1", "pi"⟩, arity := 0,
    interpretations := [
      { domain := .real, leanConst := ``Real.pi, assurance := .reviewed, definedness := "constant",
        justification := "Real.pi is defined as twice the least positive zero of cos; reviewed against the CD description." },
      { domain := .complex, leanConst := ``Real.pi, assurance := .reviewed, definedness := "constant",
        justification := "The real constant, coerced to ℂ." }] },
  { symbol := ⟨"relation1", "neq"⟩, arity := 2,
    interpretations := [Domain.real, Domain.complex].map fun d =>
      { domain := d, leanConst := ``Ne, assurance := .reviewed, definedness := "both operands defined",
        justification := "Propositional inequality; OSR conditions additionally require both operands to be defined." } },
  { symbol := ⟨"set1", "in"⟩, arity := 2,
    fragment := "conditions only, as `x ∈ setname1#Z`",
    interpretations := [Domain.real, Domain.complex].map fun d =>
      { domain := d, leanConst := ``Membership.mem, assurance := .reviewed,
        definedness := "element defined",
        justification := "Set membership; OSR conditions additionally require the element to be defined." } },
  { symbol := ⟨"setname1", "Z"⟩, arity := 0,
    fragment := "conditions only, as the set of `set1#in`",
    interpretations := [Domain.real, Domain.complex].map fun d =>
      { domain := d, leanConst := ``Set.range, assurance := .formallyRelated,
        definedness := "constant",
        justification := "The integers of the carrier, Set.range Int.cast (ℤ embeds in ℝ and ℂ).",
        obligations := [
          { cmp := "for all z | the statements z is an integer and z is a natural number or -z is a natural number are equivalent",
            theoremName := ``setname1_Z_cmp }] } },
  { symbol := ⟨"relation1", "gt"⟩, arity := 2,
    fragment := "conditions only; no complex interpretation (ℂ is not ordered)",
    interpretations := [
      { domain := .real, leanConst := ``GT.gt, assurance := .formallyRelated,
        definedness := "both operands defined",
        justification := "The order of the reals; OSR conditions additionally require both operands to be defined.",
        obligations := [{ cmp := "a>b and b>c implies a>c", theoremName := ``real_gt_cmp }] }] }
]

/-- Look up the entry of an OpenMath symbol.  Unknown symbols return `none`
and must be rejected by callers. -/
def lookup (s : OMSymbol) : Option SymbolEntry :=
  entries.find? (·.symbol == s)

/-- The weakest assurance among the symbols used, in a domain.  A missing
entry or interpretation counts as `unsupported`. -/
def mappingAssurance (syms : List OMSymbol) (d : Domain) : Assurance :=
  let levels := syms.map fun s =>
    match lookup s >>= (·.interpretation? d) with
    | some i => i.assurance
    | none => .unsupported
  let rank : Assurance → Nat
    | .formallyRelated => 0 | .reviewed => 1 | .provisional => 2 | .unsupported => 3
  levels.foldl (fun acc a => if rank a > rank acc then a else acc) .formallyRelated

end OSR.Registry
