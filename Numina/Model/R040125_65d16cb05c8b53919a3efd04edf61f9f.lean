import Mathlib

theorem algebra_10298 {b m : ℝ} (hb : b < 0) (h : ∀ x, x ^ 2 + b * x + 1 / 3 = (x + m) ^ 2 + 1 / 12) :
    b = -1 := by 
  have eq4 := h 0
  have eq5 := h 1
  have eq6 := h (-1 : ℝ)
  have eq1 : m ^ 2 = 1 / 4 := by 
    nlinarith
  have eq2 : b = 2 * m := by
    nlinarith
  have eq3 : m = -1 / 2 := by 
    nlinarith [sq_nonneg (m + 1 / 2), sq_nonneg (b + 1), sq_nonneg (m - 1 / 2), sq_nonneg (m + 1 / 2), sq_pos_of_neg hb, eq1, eq2]
  nlinarith [eq2, eq3]