import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
Candidate mathematical statements for the linear algebra pilot. These are
Mathlib checks only: no typed OSR interpretation or export is certified here.
-/

namespace OSR.LinearAlgebraPilot

open Matrix

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
variable {R : Type} [CommRing R]

omit [Fintype m] [Fintype p] in
theorem transpose_product (A : Matrix m n R) (B : Matrix n p R) :
    (A * B)ᵀ = Bᵀ * Aᵀ := by
  exact Matrix.transpose_mul A B

omit [Fintype m] [Fintype n] in
theorem transpose_sum (A B : Matrix m n R) :
    (A + B)ᵀ = Aᵀ + Bᵀ := by
  exact Matrix.transpose_add A B

omit [Fintype m] [Fintype n] [CommRing R] in
theorem transpose_involution (A : Matrix m n R) : Aᵀᵀ = A := by
  exact Matrix.transpose_transpose A

theorem trace_rectangular_cycle (A : Matrix m n R) (B : Matrix n m R) :
    Matrix.trace (A * B) = Matrix.trace (B * A) := by
  exact Matrix.trace_mul_comm A B

theorem trace_transpose (A : Matrix n n R) :
    Matrix.trace Aᵀ = Matrix.trace A := by
  exact Matrix.trace_transpose A

theorem trace_sum (A B : Matrix n n R) :
    Matrix.trace (A + B) = Matrix.trace A + Matrix.trace B := by
  exact Matrix.trace_add A B

theorem trace_scalar (k : R) (A : Matrix n n R) :
    Matrix.trace (k • A) = k * Matrix.trace A := by
  simp

omit [Fintype m] [Fintype n] in
theorem transpose_scalar (k : R) (A : Matrix m n R) :
    (k • A)ᵀ = k • Aᵀ := by
  simp

omit [Fintype m] in
theorem product_associative {q : Type} [Fintype q]
    (A : Matrix m n R) (B : Matrix n p R) (C : Matrix p q R) :
    (A * B) * C = A * (B * C) := by
  exact Matrix.mul_assoc A B C

omit [Fintype m] [Fintype p] in
theorem product_distribute_left (A : Matrix m n R) (B C : Matrix n p R) :
    A * (B + C) = A * B + A * C := by
  exact Matrix.mul_add A B C

omit [Fintype m] [Fintype p] in
theorem product_distribute_right (A B : Matrix m n R) (C : Matrix n p R) :
    (A + B) * C = A * C + B * C := by
  exact Matrix.add_mul A B C

variable [DecidableEq n]

theorem determinant_product (A B : Matrix n n R) :
    Matrix.det (A * B) = Matrix.det A * Matrix.det B := by
  exact Matrix.det_mul A B

theorem determinant_transpose (A : Matrix n n R) :
    Matrix.det Aᵀ = Matrix.det A := by
  exact Matrix.det_transpose A

theorem determinant_scalar (k : R) (A : Matrix n n R) :
    Matrix.det (k • A) = k ^ Fintype.card n * Matrix.det A := by
  exact Matrix.det_smul A k

theorem determinant_identity : Matrix.det (1 : Matrix n n R) = 1 := by
  exact Matrix.det_one

-- Mathlib totalizes the inverse of a singular matrix to zero. The explicit
-- unit hypotheses retain the intended partial-inverse domain, even where a
-- Mathlib identity also holds under its totalized convention.
theorem inverse_involution (A : Matrix n n R) (hA : IsUnit A.det) :
    A⁻¹⁻¹ = A := by
  exact Matrix.nonsing_inv_nonsing_inv A hA

theorem transpose_inverse (A : Matrix n n R) (_hA : IsUnit A.det) :
    A⁻¹ᵀ = Aᵀ⁻¹ := by
  exact Matrix.transpose_nonsing_inv A

theorem inverse_product (A B : Matrix n n R)
    (_hA : IsUnit A.det) (_hB : IsUnit B.det) :
    (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  exact Matrix.mul_inv_rev A B

end OSR.LinearAlgebraPilot

namespace OSR.LinearAlgebraPilot

theorem exponential_commuting {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (h : Commute A B) :
    NormedSpace.exp (A + B) = NormedSpace.exp A * NormedSpace.exp B := by
  exact Matrix.exp_add_of_commute A B h

theorem exponential_zero {n : ℕ} :
    NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  exact NormedSpace.exp_zero

end OSR.LinearAlgebraPilot

namespace OSR.LinearAlgebraPilot

open Matrix
open scoped Matrix

variable {R : Type} [CommRing R]

theorem cross_anticommutative (u v : Fin 3 → R) : u ⨯₃ v = -(v ⨯₃ u) := by
  exact (cross_anticomm v u).symm

theorem cross_identical (u : Fin 3 → R) : u ⨯₃ u = 0 := by
  exact cross_self u

theorem vector_triple (u v w : Fin 3 → R) :
    u ⨯₃ (v ⨯₃ w) = (u ⬝ᵥ w) • v - (v ⬝ᵥ u) • w := by
  exact cross_cross_eq_smul_sub_smul' u v w

theorem cross_jacobi (u v w : Fin 3 → R) :
    u ⨯₃ (v ⨯₃ w) + v ⨯₃ (w ⨯₃ u) + w ⨯₃ (u ⨯₃ v) = 0 := by
  exact jacobi_cross u v w

theorem scalar_triple (u v w : Fin 3 → R) :
    u ⬝ᵥ (v ⨯₃ w) = Matrix.det ![u, v, w] := by
  exact triple_product_eq_det u v w

-- On the standard real Euclidean space the dot-square is the squared norm.
theorem cross_lagrange (u v : Fin 3 → R) :
    (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) = (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 := by
  simpa [dotProduct_comm, pow_two] using cross_dot_cross u v u v

end OSR.LinearAlgebraPilot

namespace OSR.LinearAlgebraPilot

variable {n : Type} [Fintype n] [DecidableEq n]
variable {F : Type} [Field F]

theorem determinant_inverse (A : Matrix n n F) (_hA : IsUnit A.det) :
    A⁻¹.det = (A.det)⁻¹ := by
  simpa only [Ring.inverse_eq_inv] using Matrix.det_nonsing_inv A

theorem inverse_scalar (k : F) (A : Matrix n n F)
    (hk : k ≠ 0) (hA : IsUnit A.det) : (k • A)⁻¹ = k⁻¹ • A⁻¹ := by
  let : Invertible k := invertibleOfNonzero hk
  simpa using Matrix.inv_smul A k hA

end OSR.LinearAlgebraPilot
