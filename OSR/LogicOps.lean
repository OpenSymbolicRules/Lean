import OSR.Registry

/-!
# Boolean connectives

The Lean functions that interpret the `logic1` connectives in the Boolean
domain, and the CD properties (CMPs) they satisfy.  `and`, `or`, `not` and
`xor` are Lean's own `Bool` functions; the others are defined here so that the
registry can name each interpretation.
-/

namespace OSR.Logic

/-- `logic1#implies`. -/
def implies (a b : Bool) : Bool := !a || b

/-- `logic1#equivalent`. -/
def equivalent (a b : Bool) : Bool := a == b

/-- `logic1#nand`. -/
def nand (a b : Bool) : Bool := !(a && b)

/-- `logic1#nor`. -/
def nor (a b : Bool) : Bool := !(a || b)

/-- `logic1#xnor`. -/
def xnor (a b : Bool) : Bool := !(Bool.xor a b)

/-! ## CMPs of `logic1` -/

theorem and_cmp : ∀ x : Bool, (x && !x) = false := by decide
theorem or_cmp1 : ∀ x : Bool, (x || !x) = true := by decide
theorem or_cmp2 : ∀ a b : Bool, (!(a && b)) = (!a || !b) := by decide
theorem not_cmp : ∀ x : Bool, (!!x) = x := by decide
theorem implies_cmp : ∀ x : Bool, implies false x = true := by decide
theorem equivalent_cmp : ∀ a b : Bool, equivalent a b = (implies a b && implies b a) := by decide
theorem nand_cmp : ∀ x : Bool, nand x (!x) = true := by decide
theorem nor_cmp1 : ∀ x : Bool, nor x (!x) = false := by decide
theorem nor_cmp2 : ∀ a b : Bool, (a && b) = nor (!a) (!b) := by decide
theorem xor_cmp1 : ∀ x : Bool, Bool.xor x x = false := by decide
theorem xor_cmp2 : ∀ x : Bool, Bool.xor x (!x) = true := by decide
theorem xnor_cmp1 : ∀ x : Bool, xnor x x = true := by decide
theorem xnor_cmp2 : ∀ x : Bool, xnor x (!x) = false := by decide
theorem true_cmp : (!true) = false := rfl
theorem false_cmp : (!false) = true := rfl

/-- `setname2#Boolean` CMP: every Boolean `b` has another Boolean, `not b`. -/
theorem boolean_cmp : ∀ b : Bool, ∃ nb : Bool, nb ≠ b → nb = !b :=
  fun b => ⟨!b, fun _ => rfl⟩

end OSR.Logic
