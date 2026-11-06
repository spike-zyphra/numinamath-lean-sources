import Mathlib

theorem algebra_170091 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a = b + 2.5) (h1 : 10 * a + 5 * b = 10 * b + 5 * a - 0.5) :
    a - b = 10 := by 
  rw [h] at h1
  norm_num at h1 ⊢
  all_goals linarith