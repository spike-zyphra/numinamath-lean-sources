import Mathlib

theorem algebra_22207 : IsGreatest {x : ℝ | abs (x + 5) - abs (3 * x - 6) = 0} (11 / 2) := by
  constructor
  · -- Show that 11/2 is in the set
    dsimp
    norm_num [abs_of_pos, abs_of_nonneg, abs_of_nonpos]
  · -- Show that if x in the set, then x ≤ 11/2
    intro x
    intro hx
    dsimp at hx
    by_cases h1 : x ≥ 2
    · -- If x >= 2, then |x + 5| = x + 5 and |3 * x - 6| = 3 * x - 6
      rw [abs_of_nonneg (show x + 5 ≥ 0 by linarith), abs_of_nonneg (show 3 * x - 6 ≥ 0 by linarith)] at hx
      linarith
    · -- If x < 2, need further cases
      by_cases h2 : x ≥ -5
      · -- If -5 ≤ x < 2, then |x + 5| = x + 5 and |3 * x - 6| = -(3 * x - 6)
        rw [abs_of_nonneg (show x + 5 ≥ 0 by linarith), abs_of_nonpos (show 3 * x - 6 ≤ 0 by linarith)] at hx
        linarith
      · -- If x < -5, then |x + 5| = -(x + 5) and |3 * x - 6| = -(3 * x - 6)
        rw [abs_of_nonpos (show x + 5 ≤ 0 by linarith), abs_of_nonpos (show 3 * x - 6 ≤ 0 by linarith)] at hx
        linarith