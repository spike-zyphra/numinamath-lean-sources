import Mathlib

/- Show that if \( A \) is an \( n \times n \) matrix with a non-zero determinant (\( \operatorname{det} A \neq 0 \)), then the product of \( A \) and its adjoint \( \operatorname{adj} A \) equals the determinant of \( A \) multiplied by the identity matrix \( I \). In mathematical terms, this can be expressed as \( A(\operatorname{adj} A) = (\operatorname{det} A) I \).-/
theorem number_theory_4724 {α : Type*} [CommRing α] {n : ℕ} {A : Matrix (Fin n) (Fin n) α} (_ : A.det ≠ 0) :
    A * A.adjugate = A.det • 1 :=
  -- exactly `Matrix.mul_adjugate` in Mathlib
  Matrix.mul_adjugate A
