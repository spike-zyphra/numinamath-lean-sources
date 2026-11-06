import Mathlib

theorem algebra_235202 :
    IsGreatest {t : ℝ | ∃ x y, t = x^2 - 6 * x + y^2 ∧ |x + y| + |x - y| = 2} 8 := by
  constructor
  · -- Choose x = -1 and y = 1
    use -1, 1
    norm_num
  · -- Show that 8 is the maximum
    intro t ht
    rcases ht with ⟨x, y, h_eq, h_abs_eq⟩
    by_cases h1 : x + y ≥ 0
    · -- Case where x + y ≥ 0
      by_cases h2 : x - y ≥ 0
      · -- Case where x + y ≥ 0 and x - y ≥ 0: |x+y| + |x-y| = 2x
        rw [abs_of_nonneg (show x + y ≥ 0 by linarith), abs_of_nonneg (show x - y ≥ 0 by linarith)] at h_abs_eq
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (y + 1), sq_nonneg (x + 1)]
      · -- Case where x + y ≥ 0 and x - y < 0: |x+y| + |x-y| = 2y
        rw [abs_of_nonneg (show x + y ≥ 0 by linarith), abs_of_neg (show x - y < 0 by linarith)] at h_abs_eq
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (y + 1), sq_nonneg (x + 1)]
    · -- Case where x + y < 0
      by_cases h3 : x - y ≥ 0
      · -- Case where x + y < 0 and x - y ≥ 0: |x+y| + |x-y| = -2y
        rw [abs_of_neg (show x + y < 0 by linarith), abs_of_nonneg (show x - y ≥ 0 by linarith)] at h_abs_eq
        nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (y - 1), sq_nonneg (x - 1)]
      · -- Case where x + y < 0 and x - y < 0: |x+y| + |x-y| = -2x
        rw [abs_of_neg (show x + y < 0 by linarith), abs_of_neg (show x - y < 0 by linarith)] at h_abs_eq
        nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (y - 1), sq_nonneg (x - 1)]