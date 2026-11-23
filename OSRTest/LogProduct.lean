-- SPDX-License-Identifier: MIT
import OSR.Algebra

/-! Application tests for the real rule `algebra.log.ln_mul`. -/

namespace OSRTest.LogProduct

open OSR

private def assignment (x y : ℝ) (name : String) : ℝ := if name = "a" then x else y

private def guards (x y : ℝ) : Prop :=
  ∀ c ∈ Algebra.lnMul.conditions, c.Holds Interp.real (assignment x y)

private theorem guards_iff (x y : ℝ) : guards x y ↔ 0 < x ∧ 0 < y := by
  simp [guards, Algebra.lnMul, Cond.Holds, Defined, eval, Interp.real, assignment]

-- Apply the catalog theorem with its actual guards and its source-domain premise.
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Defined Interp.real (assignment x y) Algebra.lnMul.rhs ∧
      Real.log (x * y) = Real.log x + Real.log y := by
  have source : Defined Interp.real (assignment x y) Algebra.lnMul.lhs :=
    ⟨⟨trivial, trivial⟩, mul_pos hx hy⟩
  exact Algebra.lnMul_real (assignment x y) ((guards_iff x y).mpr ⟨hx, hy⟩) source

-- Knowing only that the first factor is positive leaves the second guard open.
example : ¬ guards 1 0 := by simp [guards_iff]

-- Dropping the guards can lose definedness even when the evaluated values agree.
example :
    Defined Interp.real (assignment (-1) (-1)) Algebra.lnMul.lhs ∧
    ¬ Defined Interp.real (assignment (-1) (-1)) Algebra.lnMul.rhs ∧
    eval Interp.real (assignment (-1) (-1)) Algebra.lnMul.lhs =
      eval Interp.real (assignment (-1) (-1)) Algebra.lnMul.rhs := by
  norm_num [Algebra.lnMul, Defined, eval, Interp.real, assignment, Real.log_neg_eq_log]

end OSRTest.LogProduct
