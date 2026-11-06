import Mathlib

/- Show that if \( A \) is an \( n \times n \) matrix with integer entries and \( m \) is a positive integer such that the greatest common divisor of \( \operatorname{det} A \) and \( m \) is 1, then the matrix \( \bar{A} = \bar{\Delta}(\operatorname{adj} A) \) serves as an inverse of \( A \) modulo \( m \). Here, \( \Delta \) is the determinant of \( A \), and \( \bar{\Delta} \) is its inverse modulo \( m \).-/
theorem number_theory_4726 {m n : ℕ} {A : Matrix (Fin n) (Fin n) (ZMod m)} (_ : 0 < m)
    (hdet : IsUnit A.det) : ∃ y, A.det * y = 1 ∧ A * (y • A.adjugate) = 1 := by
  -- notice that `(A.det : ZMod m)` is invertible
  have hA : A.det * A.det⁻¹ = 1 := ZMod.mul_inv_of_unit _ hdet
  use A.det⁻¹
  constructor
  -- `A.det⁻¹` is the inverse of `A.det`
  . exact hA
  -- moreover, we conclude that `(A.det⁻¹ * A.adjugate)` is inverse of `A`
  calc
    _ = A.det⁻¹ • (A * A.adjugate) := by rw [Matrix.mul_smul]
    _ = A.det⁻¹ • (A.det • 1) := by
      apply congrArg
      exact Matrix.mul_adjugate A
    _ = _ := by
      ext i j
      simp
      rw [← mul_assoc, mul_comm A.det⁻¹, hA, one_mul]
