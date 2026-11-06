import Mathlib

theorem number_theory_4724 {α : Type*} [CommRing α] {n : ℕ} {A : Matrix (Fin n) (Fin n) α} (_ : A.det ≠ 0) :
    A * A.adjugate = A.det • 1 := by 
  apply Matrix.mul_adjugate