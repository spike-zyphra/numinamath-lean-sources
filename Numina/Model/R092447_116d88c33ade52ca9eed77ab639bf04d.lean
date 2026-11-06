import Mathlib

theorem algebra_155648 (A B C D : EuclideanSpace ℝ (Fin 3)) :
    Matrix.dotProduct (A - B) (C - D) + Matrix.dotProduct (A - C) (D - B) +
    Matrix.dotProduct (A - D) (B - C) = 0 := by
  simp [Matrix.dotProduct, Fin.sum_univ_three]
  <;> ring_nf <;> simp [Fin.sum_univ_three]
  <;> ring