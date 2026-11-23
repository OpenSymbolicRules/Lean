import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Concrete mathematical counterexamples, not yet exported as OSR rules. -/

namespace OSR.LinearAlgebraPilot

open Matrix

def unit2 : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1]

theorem determinant_sum_false :
    Matrix.det (unit2 + unit2) ≠ Matrix.det unit2 + Matrix.det unit2 := by
  norm_num [unit2, Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply]

theorem determinant_scalar_false :
    Matrix.det (2 • unit2) ≠ 2 * Matrix.det unit2 := by
  norm_num [unit2, Matrix.det_fin_two, Matrix.smul_apply]

theorem trace_product_false :
    Matrix.trace (unit2 * unit2) ≠ Matrix.trace unit2 * Matrix.trace unit2 := by
  norm_num [unit2, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

def squareA : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
def squareB : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]

theorem commuting_square_expansion_false :
    (squareA + squareB) * (squareA + squareB) ≠
      squareA * squareA + 2 • (squareA * squareB) + squareB * squareB := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [squareA, squareB, Matrix.mul_apply, Fin.sum_univ_two] at h00

def inverseA : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]
def inverseB : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 1, 1]

theorem inverse_witnesses_are_invertible :
    IsUnit inverseA.det ∧ IsUnit inverseB.det := by
  norm_num [inverseA, inverseB, Matrix.det_fin_two, isUnit_iff_ne_zero]

theorem inverse_product_order_false :
    (inverseA * inverseB)⁻¹ ≠ inverseA⁻¹ * inverseB⁻¹ := by
  rw [Matrix.mul_inv_rev]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [inverseA, inverseB, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two, Ring.inverse_eq_inv] at h00

end OSR.LinearAlgebraPilot
