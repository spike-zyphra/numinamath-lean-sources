import Mathlib

theorem inequalities_129768 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) :
    -1/2 ≤ a*b + b*c + c*a ∧ a*b + b*c + c*a ≤ 1 := by
  constructor
  · -- Prove -1/2 ≤ a*b + b*c + c*a
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  · -- Prove a*b + b*c + c*a ≤ 1
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]