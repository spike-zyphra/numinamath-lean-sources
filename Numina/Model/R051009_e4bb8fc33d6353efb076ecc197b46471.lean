import Mathlib

theorem algebra_18682 : IsGreatest {x : ℝ | abs (5 * x - 1) = x + 3} 1 := by
  constructor
  · -- We need to show that 1 is a solution to the equation |5x - 1| = x + 3.
    show abs (5 * (1 : ℝ) - 1) = (1 : ℝ) + 3
    norm_num [abs_of_nonneg]
  · -- We need to prove that any solution y to the equation |5y - 1| = y + 3 is ≤ 1.
    intro y hy
    have h_eq : abs (5 * y - 1) = y + 3 := hy
    -- We consider two cases based on the definition of absolute value
    by_cases h : 5 * y - 1 ≥ 0
    · -- Case 1: If 5y - 1 ≥ 0, then |5y - 1| = 5y - 1
      rw [abs_of_nonneg h] at h_eq
      linarith
    · -- Case 2: If 5y - 1 < 0, then |5y - 1| = -(5y - 1) = 1 - 5y
      rw [abs_of_neg (lt_of_not_ge h)] at h_eq
      linarith