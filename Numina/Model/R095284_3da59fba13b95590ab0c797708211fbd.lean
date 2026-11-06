import Mathlib

theorem algebra_905 {a b : ℝ} (h : (a + 1) / 20 = (b + 1) / 21) (h' : (b + 1) / 21 = (a + b) / 17) :
    a / b = 8 / 9 := by
  have eq1 : 21 * a - 20 * b = -1 := by
    linarith
  have eq2 : -21 * a - 4 * b + 17 = 0 := by
    linarith
  have b_val : b = 3 / 4 := by
    linarith [eq1, eq2]
  have a_val : a = 2 / 3 := by
    rw [b_val] at eq1
    linarith
  have h1 : a / b = 8 / 9 := by
    rw [a_val, b_val]
    norm_num
  exact h1