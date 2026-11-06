import Mathlib

theorem algebra_5988 {x y : ℝ} (h : abs (2 * y - x + 13) + (y + 7) ^ 4 = 0) : x = -1 := by
  have h1 : abs (2 * y - x + 13) = 0 := by
    linarith [abs_nonneg (2 * y - x + 13), show (y + 7) ^ 4 ≥ 0 by positivity]
  have h2 : (y + 7) ^ 4 = 0 := by
    linarith [abs_nonneg (2 * y - x + 13), show (y + 7) ^ 4 ≥ 0 by positivity]
  have hy : y + 7 = 0 := by
    have h3 : (y + 7) ^ 4 = 0 := h2
    simp at h3 ⊢
    <;> nlinarith
  have h3 : 2 * y - x + 13 = 0 := by 
    rw [abs_eq_zero] at h1 
    linarith 
  have hy' : y = -7 := by 
    linarith 
  rw [hy'] at h3
  linarith 
  all_goals linarith [abs_nonneg (2 * y - x + 13), show (y + 7) ^ 4 ≥ 0 by positivity]