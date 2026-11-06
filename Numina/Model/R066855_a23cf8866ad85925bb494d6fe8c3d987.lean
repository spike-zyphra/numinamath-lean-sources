import Mathlib

theorem algebra_1118 (m n : ℝ) (h : ∀ x > 2015, m / (x - 2) + n / (x + 2) = (5 * x + 2) / (x ^ 2 - 4)) : m ^ 2 - n ^ 2 = 5 := by
  have eq1 := h 2017 (by norm_num)
  have eq2 := h 2018 (by norm_num)
  norm_num at eq1 eq2
  have eq3 : m + n = 5 := by
    linarith
  have eq4 : m - n = 1 := by
    linarith
  have eq5 : m = 3 := by 
    linarith
  have eq6 : n = 2 := by
    linarith
  rw [eq5, eq6]
  norm_num
  all_goals linarith