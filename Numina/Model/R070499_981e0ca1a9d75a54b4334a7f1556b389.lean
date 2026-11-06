import Mathlib

theorem algebra_95164 {x y : ℝ} (hxy : x ≠ y) (h1 : y + 4 = (x - 2)^2) (h2 : x + 4 = (y - 2)^2) :
    x^2 + y^2 = 15 := by
  have h3 : y = x^2 - 4 * x := by
    nlinarith 
  have h4 : x = y^2 - 4 * y := by
    nlinarith 
  rw [h3] at h4
  nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by
    intro h'
    apply hxy
    nlinarith [h3]
  ), sq_nonneg (x - y), sq_nonneg (x + y - 4), sq_nonneg (x^2 + y^2 - 15)]