import Mathlib

theorem algebra_109685 (x y : ℝ) (h : x^2 + y^2 = 1) :
    2 * x^4 + 3 * x^2 * y^2 + y^4 + y^2 = 2 := by 
  have hx2 : x^2 = 1 - y^2 := by linarith
  have hx4 : x^4 = (x^2)^2 := by ring
  rw [hx4, hx2]
  ring_nf
  <;> nlinarith [sq_nonneg (y^2 - 1), sq_nonneg (y^2)]