import OSR.Rule

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
    fragment := "exponent restricted to a natural-number literal; general powers (CMP 1, exp/ln) are out of scope",
    interpretations := [Domain.real, Domain.complex].map fun d =>
      { domain := d, leanConst := ``HPow.hPow, assurance := .formallyRelated,
        definedness := "everywhere (natural exponents; 0^0 = 1 as in CMP 2)",
        justification := "Monoid power by a natural number agrees with the integer-exponent recursion of CMP 2.",
        obligations := [
          { cmp := "if n is an integer then x^0 = 1", theoremName := ``pow_zero },
          { cmp := "if n is an integer then x^n = x * x^(n-1)", theoremName := ``pow_cmp2,
            note := "stated for natural n as x^(n+1) = x * x^n" }] } },
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
  { symbol := ⟨"nums1", "pi"⟩, arity := 0,
    interpretations := [
      { domain := .real, leanConst := ``Real.pi, assurance := .reviewed, definedness := "constant",
        justification := "Real.pi is defined as twice the least positive zero of cos; reviewed against the CD description." },
      { domain := .complex, leanConst := ``Real.pi, assurance := .reviewed, definedness := "constant",
        justification := "The real constant, coerced to ℂ." }] },
  { symbol := ⟨"relation1", "neq"⟩, arity := 2,
    interpretations := [Domain.real, Domain.complex].map fun d =>
      { domain := d, leanConst := ``Ne, assurance := .reviewed, definedness := "both operands defined",
        justification := "Propositional inequality; OSR conditions additionally require both operands to be defined." } }
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
