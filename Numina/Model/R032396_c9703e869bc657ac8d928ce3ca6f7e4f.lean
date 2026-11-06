import Mathlib

theorem algebra_21348 (x : ℝ)
  (h1 : x ≠ 5 ∧ x ≠ 8 ∧ x ≠ 10 ∧ x ≠ 18 ∧ x ≠ 19 ∧ x ≠ 28 ∧ x ≠ 30)
  (h2:(5+8+10+18+19+28+30+x)/8 = x-4.5): x=22 := by
  norm_num at h2
  linarith