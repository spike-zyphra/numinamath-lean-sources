import Mathlib

theorem algebra_298589 (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : x + y + z = x * y * z) (h2 : x ^ 2 = y * z) :
    3 ≤ x ^ 2 := by
  have h3 : x * y * z = x ^ 3 := by
    have eq1 : x * y * z = x * (y * z) := by ring
    rw [eq1]
    rw [show y * z = x ^ 2 by linarith [h2]]
    all_goals ring
  have h4 : x + y + z = x ^ 3 := by 
    linarith [h1, h3]
  have h5 : y + z = x ^ 3 - x := by 
    nlinarith [h4]
  have h6 : (x ^ 3 - x) ^ 2 - 4 * x ^ 2 ≥ 0 := by
    have h7 : (y + z) ^ 2 - 4 * (y * z) = (y - z) ^ 2 := by 
      linarith
    rw [show y + z = x ^ 3 - x by linarith [h5]] at h7
    rw [show y * z = x^2 by linarith [h2]] at h7
    have hquad : (y - z) ^ 2 ≥ 0 := by 
      apply sq_nonneg
    linarith [h7, hquad]
  have h7 : x ^ 2 * (x ^ 4 - 2 * x ^ 2 - 3) ≥ 0 := by
    nlinarith [h6]
  have h8 : x ^ 4 - 2 * x ^ 2 - 3 ≥ 0 := by
    have h9 : x ^ 2 > 0 := by
      exact sq_pos_of_ne_zero hx
    nlinarith
  have h9 : x ^ 2 ≥ 3 := by
    nlinarith [sq_nonneg (x ^ 2 - 3), sq_nonneg (x), sq_pos_of_pos (show (0 : ℝ) < 1 by norm_num)]
  linarith [h9]