import Mathlib

theorem inequalities_166860 {x y : ℝ} (hy : y > 3 / (x - y)) (hxy : x > y) : x ^ 2 > y ^ 2 + 6 := by
  have h1 : x - y > 0 := by linarith
  have h2 : y * (x - y) > 3 := by
    have h3 : x - y > 0 := h1
    have h4 : y > 3 / (x - y) := hy
    have h5 : y * (x - y) > 3 := by
      have h6 : (3 / (x - y)) * (x - y) = 3 := by
        field_simp [show x - y ≠ 0 by linarith]
      nlinarith [h4, h3]
    linarith
  have h3 : y * x - y ^ 2 > 3 := by
    have h4 : y * (x - y) > 3 := h2
    linarith [h4]
  nlinarith [sq_pos_of_pos h1, sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 2 * y), sq_nonneg (x + 2 * y), h3, hxy]