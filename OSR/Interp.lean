import OSR.Expr

/-!
# Interpretation of OSR expressions

`eval` gives an expression its value in a domain.  Lean's operations are total
(`x / 0 = 0`, `Real.tan` at a pole is `0`, `Complex.arctan I` has a value), so
`eval` alone cannot tell a meaningful value from a totalization artifact.
`Defined` makes the definedness conditions of the OpenMath operations
explicit; rule statements quantify over it, so a theorem can never certify a
rewrite merely because both sides agree on totalized junk values.
-/

namespace OSR

/-- The integer a value is equal to, if any (classical).  In a field of
characteristic zero this integer is unique (`intValue?_eq`). -/
noncomputable def intValue? {α : Type} [Field α] (v : α) : Option ℤ :=
  open Classical in if h : ∃ n : ℤ, (n : α) = v then some h.choose else none

theorem intValue?_eq {α : Type} [Field α] [CharZero α] (v : α) (n : ℤ) :
    intValue? v = some n ↔ v = n := by
  unfold intValue?
  split
  · rename_i h
    constructor
    · intro hs
      cases hs
      exact h.choose_spec.symm
    · intro hv
      exact congrArg some (Int.cast_injective (h.choose_spec.trans hv))
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact fun hv => h ⟨n, hv.symm⟩

theorem intValue?_intCast {α : Type} [Field α] [CharZero α] (n : ℤ) :
    intValue? (n : α) = some n :=
  (intValue?_eq _ _).2 rfl

/-- The domain-specific part of an interpretation.  Arithmetic comes from the
`Field` structure; transcendental symbols and their definedness conditions are
given here. -/
structure Interp (α : Type) [Field α] where
  sin : α → α
  cos : α → α
  tan : α → α
  arctan : α → α
  exp : α → α
  ln : α → α
  pi : α
  /-- Where OpenMath `transc1#tan` is defined. -/
  tanDefined : α → Prop
  /-- Where OpenMath `transc1#arctan` is defined. -/
  arctanDefined : α → Prop
  /-- Where OpenMath `transc1#ln` is defined. -/
  lnDefined : α → Prop
  /-- The order used by `relation1#gt` conditions, `lt a b` meaning `a < b`.
  Only the real interpretation is an OpenMath mapping; see the registry. -/
  lt : α → α → Prop
  /-- The integer a value is equal to, if any; used for `arith1#power`, which
  the fragment interprets for integer exponents only. -/
  toInt? : α → Option ℤ
  toInt?_eq : ∀ v n, toInt? v = some n ↔ v = (n : α)

/-- Real interpretation, using Mathlib's `Real` functions. -/
noncomputable def Interp.real : Interp ℝ where
  sin := Real.sin
  cos := Real.cos
  tan := Real.tan
  arctan := Real.arctan
  exp := Real.exp
  ln := Real.log
  pi := Real.pi
  tanDefined x := Real.cos x ≠ 0
  arctanDefined _ := True
  lnDefined x := 0 < x
  lt x y := x < y
  toInt? := intValue?
  toInt?_eq := intValue?_eq

/-- Complex interpretation, using Mathlib's `Complex` functions. -/
noncomputable def Interp.complex : Interp ℂ where
  sin := Complex.sin
  cos := Complex.cos
  tan := Complex.tan
  arctan := Complex.arctan
  exp := Complex.exp
  ln := Complex.log
  pi := (Real.pi : ℂ)
  tanDefined z := Complex.cos z ≠ 0
  arctanDefined z := z ≠ Complex.I ∧ z ≠ -Complex.I
  lnDefined z := z ≠ 0
  -- Not an OpenMath mapping (`relation1#gt` has no complex interpretation):
  -- both operands real and ordered.
  lt z w := z.im = 0 ∧ w.im = 0 ∧ z.re < w.re
  toInt? := intValue?
  toInt?_eq := intValue?_eq

variable {α : Type} [Field α]

/-- The value of an expression under an interpretation and a variable
assignment. -/
def eval (I : Interp α) (env : String → α) : Expr → α
  | .var n => env n
  | .int z => (z : α)
  | .const .pi => I.pi
  | .app1 .neg a => -eval I env a
  | .app1 .sin a => I.sin (eval I env a)
  | .app1 .cos a => I.cos (eval I env a)
  | .app1 .tan a => I.tan (eval I env a)
  | .app1 .arctan a => I.arctan (eval I env a)
  | .app1 .exp a => I.exp (eval I env a)
  | .app1 .ln a => I.ln (eval I env a)
  | .app2 .add a b => eval I env a + eval I env b
  | .app2 .sub a b => eval I env a - eval I env b
  | .app2 .mul a b => eval I env a * eval I env b
  | .app2 .div a b => eval I env a / eval I env b
  | .pow a e =>
    match I.toInt? (eval I env e) with
    | some n => eval I env a ^ n
    | none => 0

/-- Whether every operation in the expression is applied inside its domain of
definition, following the OpenMath operation rather than Lean's totalization. -/
def Defined (I : Interp α) (env : String → α) : Expr → Prop
  | .var _ => True
  | .int _ => True
  | .const _ => True
  | .app1 .tan a => Defined I env a ∧ I.tanDefined (eval I env a)
  | .app1 .arctan a => Defined I env a ∧ I.arctanDefined (eval I env a)
  | .app1 .ln a => Defined I env a ∧ I.lnDefined (eval I env a)
  | .app1 .exp a => Defined I env a
  | .app1 .neg a => Defined I env a
  | .app1 .sin a => Defined I env a
  | .app1 .cos a => Defined I env a
  | .app2 .div a b => Defined I env a ∧ Defined I env b ∧ eval I env b ≠ 0
  | .app2 .add a b => Defined I env a ∧ Defined I env b
  | .app2 .sub a b => Defined I env a ∧ Defined I env b
  | .app2 .mul a b => Defined I env a ∧ Defined I env b
  | .pow a e => Defined I env a ∧ Defined I env e ∧
      ∃ n, I.toInt? (eval I env e) = some n ∧ (n < 0 → eval I env a ≠ 0)

theorem Interp.toInt?_cast (I : Interp α) (n : ℤ) : I.toInt? (n : α) = some n :=
  (I.toInt?_eq _ _).2 rfl

theorem eval_pow_of {I : Interp α} {env : String → α} {a e : Expr} {n : ℤ}
    (h : I.toInt? (eval I env e) = some n) : eval I env (.pow a e) = eval I env a ^ n := by
  simp [eval, h]

end OSR
