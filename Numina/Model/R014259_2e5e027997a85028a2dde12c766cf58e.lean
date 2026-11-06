import Mathlib

theorem algebra_319639 (a b c d : ℝ) (ha : -1 ≤ a) (hb : -1 ≤ b) (hc : -1 ≤ c) (hd : -1 ≤ d)
    (h : a + b + c + d = 0) :
    a * b + b * c + c * d ≤ 5 / 4 := by 
  have h1 : d = -a - b - c := by linarith
  have h2 : a * b + b * c + c * d = a * b - a * c - c ^ 2 := by 
    rw [h1]
    nlinarith 
  rw [h2]
  nlinarith [sq_nonneg (a + 1), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2), sq_nonneg (a + 1 - (1 / 2)), sq_nonneg (b + 1), sq_nonneg (c + 1),
          mul_nonneg (show (0 : ℝ) ≤ a + 1 by linarith) (show (0 : ℝ) ≤ b + 1 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b + 1 by linarith) (show (0 : ℝ) ≤ c + 1 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ c + 1 by linarith) (show (0 : ℝ) ≤ a + 1 by linarith)]