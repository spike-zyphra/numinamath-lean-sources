import Mathlib

theorem algebra_125593 (x : ℕ) (hx : x > 0) (h : (3 * 3 + 2 * 2 + x * 5) / (3 + 2 + x) = 4) :
    x ≥ 7 := by 
  by_contra h1
  push_neg at h1
  interval_cases x <;> norm_num at h <;> omega