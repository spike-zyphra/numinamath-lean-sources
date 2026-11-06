import Mathlib

theorem algebra_83683 {x : Fin 5 → ℝ} (hx1 : 2 * x 0 = x 4 ^ 2 - 23) (hx2 : 4 * x 1 = x 0 ^ 2 + 7)
    (hx3 : 6 * x 2 = x 1 ^ 2 + 14) (hx4 : 8 * x 3 = x 2 ^ 2 + 23) (hx5 : 10 * x 4 = x 3 ^ 2 + 34) :
    (x 0, x 1, x 2, x 3, x 4) = (1, 2, 3, 4, 5) := by
  have h1 : (x 0 - 1)^2 + (x 1 - 2)^2 + (x 2 - 3)^2 + (x 3 - 4)^2 + (x 4 - 5)^2 = 0 := by
    nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 1 - 2), sq_nonneg (x 2 - 3), sq_nonneg (x 3 - 4), sq_nonneg (x 4 - 5)]
  have hx0 : x 0 - 1 = 0 := by nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 1 - 2), sq_nonneg (x 2 - 3), sq_nonneg (x 3 - 4), sq_nonneg (x 4 - 5)]
  have hx1' : x 1 - 2 = 0 := by nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 1 - 2), sq_nonneg (x 2 - 3), sq_nonneg (x 3 - 4), sq_nonneg (x 4 - 5)]
  have hx2' : x 2 - 3 = 0 := by nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 1 - 2), sq_nonneg (x 2 - 3), sq_nonneg (x 3 - 4), sq_nonneg (x 4 - 5)]
  have hx3' : x 3 - 4 = 0 := by nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 1 - 2), sq_nonneg (x 2 - 3), sq_nonneg (x 3 - 4), sq_nonneg (x 4 - 5)]
  have hx4' : x 4 - 5 = 0 := by nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 1 - 2), sq_nonneg (x 2 - 3), sq_nonneg (x 3 - 4), sq_nonneg (x 4 - 5)]
  have h0 : x 0 = 1 := by linarith
  have h1' : x 1 = 2 := by linarith
  have h2' : x 2 = 3 := by linarith
  have h3' : x 3 = 4 := by linarith
  have h4' : x 4 = 5 := by linarith
  simp [Prod.ext_iff, h0, h1', h2', h3', h4']
  <;> tauto