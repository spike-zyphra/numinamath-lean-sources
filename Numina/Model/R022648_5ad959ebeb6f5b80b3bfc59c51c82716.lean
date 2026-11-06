import Mathlib

theorem algebra_318 (x y z : ℝ) (h1 : x + y = 5) (h2 : z ^ 2 = x * y + y - 9) :
    x + 2 * y + 3 * z = 8 := by
  have h3 : y = 5 - x := by linarith
  rw [h3] at h2
  have h4 : z ^ 2 = - (x - 2) ^ 2 := by
    nlinarith
  have h5 : z ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h6 : (x - 2) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h7 : z ^ 2 = 0 := by
    nlinarith [h4, h5, h6]
  have h8 : z = 0 := by
    nlinarith
  have h9 : (x - 2) ^ 2 = 0 := by
    nlinarith [h4, h7]
  have h10 : x = 2 := by
    nlinarith
  have h11 : y = 3 := by
    linarith [h1, h10]
  rw [h10, h11, h8]
  all_goals norm_num