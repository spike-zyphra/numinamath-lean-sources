import Mathlib

theorem algebra_279027 (a : ℕ → ℝ) (ha : ∀ n, a n = 2 * Real.cos (Real.pi / 2 ^ (n + 1))) :
    a 1 = 2 * Real.cos (Real.pi / 2 ^ 2) ∧ a 2 = 2 * Real.cos (Real.pi / 2 ^ 3) := by
  constructor
  · -- Verify the formula for $a_1$
    rw [ha 1]
    all_goals norm_num
  · -- Verify the formula for $a_2$
    rw [ha 2]
    all_goals norm_num