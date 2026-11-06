import Mathlib

theorem algebra_21272 : IsGreatest {z : ℝ | ∃(x y : ℝ), |x + y| + |x - y| = 2 ∧ z = x^2 - 6 * x + y^2} 8 := by
  constructor
  · -- Show that 8 is in the set, with x = -1 and y = 1.
    use -1, 1
    norm_num [abs]
    all_goals norm_num
  · -- Show that 8 is greatest in the set.
    intro z hz
    rcases hz with ⟨x, y, h1, h2⟩
    by_cases h11 : x + y ≥ 0
    · -- Case 1: x + y ≥ 0
      by_cases h12 : x - y ≥ 0
      · -- Subcase 1.1: x + y ≥ 0 and x - y ≥ 0
        rw [abs_of_nonneg h11, abs_of_nonneg h12] at h1
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + 1), sq_nonneg (y + 1)]
      · -- Subcase 1.2: x + y ≥ 0 and x - y < 0
        rw [abs_of_nonneg h11, abs_of_neg (show x - y < 0 by linarith)] at h1
        nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 1), sq_nonneg (x - 1), sq_nonneg (y + 1)]
    · -- Case 2: x + y < 0
      by_cases h12 : x - y ≥ 0
      · -- Subcase 2.1: x + y < 0 and x - y ≥ 0
        rw [abs_of_neg (show x + y < 0 by linarith), abs_of_nonneg h12] at h1
        nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - 1), sq_nonneg (y - 1)]
      · -- Subcase 2.2: x + y < 0 and x - y < 0
        rw [abs_of_neg (show x + y < 0 by linarith), abs_of_neg (show x - y < 0 by linarith)] at h1
        nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - 1), sq_nonneg (y - 1)]