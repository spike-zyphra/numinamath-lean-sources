import Mathlib

theorem calculus_23455 (x y : Fin 3 → ℝ)
    (h₀ : (x 0 - x 1)^2 + (y 0 - y 1)^2 = 9)
    (h₁ : (x 0 - x 2)^2 + (y 0 - y 2)^2 = 16)
    (h₂ : (x 1 - x 2)^2 + (y 1 - y 2)^2 = 25) :
    Matrix.det !![x 0, y 0, 1; x 1, y 1, 1; x 2, y 2, 1] ^ 2 = 144 := by
  simp [Matrix.det_fin_three, Fin.sum_univ_three, mul_add, add_mul, sub_eq_zero, mul_comm]
  <;> nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (y 0 - y 1), sq_nonneg (x 0 - x 2), sq_nonneg (y 0 - y 2), sq_nonneg (x 1 - x 2), sq_nonneg (y 1 - y 2), sq_nonneg (x 0 * (y 1 - y 2)), sq_nonneg (y 0 * (x 1 - x 2)), sq_nonneg ((x 1 * y 2 - x 2 * y 1))]