import Mathlib

theorem other_176090 (m : ℝ) (hm : m > 0) (h : 100 * (2100 * (-5)) + m * (4200 * 10) = 0)
    (h' : 100 * (3.3 * 10 ^ 5) + m * (4200 * 10) = 0) :
    0.0028 ≤ m ∧ m ≤ 0.811 := by 
  norm_num at h h'
  all_goals linarith -- The systems inconsistent because with m > 0.