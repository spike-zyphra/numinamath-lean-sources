import Mathlib

theorem algebra_199588 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 9 = b * 4) (h2 : b * 10 = a * 15) :
    a = 10 ∧ b = 10 := by 
  have h3 : b = 0 := by
    nlinarith
  linarith
  all_goals linarith