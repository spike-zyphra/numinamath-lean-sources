import Mathlib

theorem calculus_15022 (a b c : EuclideanSpace ℝ (Fin 3)) (D : ℝ)
    (hD : D = Matrix.det ![a, b, c]) :
    Matrix.det ![a + b, b + c, c + a] = 2 * D := by
  rw [hD]
  simp [Matrix.det_fin_three, add_mul, mul_add, mul_assoc]
  <;> ring_nf <;> simp [Matrix.det_fin_three]
  <;> ring