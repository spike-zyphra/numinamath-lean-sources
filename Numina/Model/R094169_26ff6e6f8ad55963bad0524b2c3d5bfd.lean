import Mathlib

theorem algebra_7666 (x : ℕ) (h : x > 0) (h1 : (9 * 5 + x * 10) / (9 + x) = 7) :
    x ≥ 6 := by 
  by_contra h2
  push_neg at h2 
  interval_cases x <;> norm_num at h1 <;> all_goals 
    omega