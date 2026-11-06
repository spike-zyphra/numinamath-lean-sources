import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_136342 :
  IsGreatest {t : ℝ | ∃ x y, t = x^2 - x * y + y^2 ∧ |5 * x + y| + |5 * x - y| = 20} 124 ∧
  IsLeast {t : ℝ | ∃ x y, t = x^2 - x * y + y^2 ∧ |5 * x + y| + |5 * x - y| = 20} 3 := by
  constructor
  · -- Show that 124 is the greatest element of the set
    constructor
    · -- Show that 124 is in the set
      use (2 : ℝ), (-10 : ℝ)
      norm_num [abs]
      <;> norm_num
    · -- Show that 124 is the greatest value in the set
      intro t ht
      rcases ht with ⟨x, y, ht_eq, h_abs⟩
      by_cases h1 : 5 * x + y ≥ 0
      · -- Case 1: 5x + y >= 0
        by_cases h2 : 5 * x - y ≥ 0
        · -- Case 1a: 5x - y >= 0 
          rw [abs_of_nonneg h1, abs_of_nonneg h2] at h_abs
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 10)]
        · -- Case 1b: 5x - y < 0
          rw [abs_of_nonneg h1, abs_of_neg (lt_of_not_ge h2)] at h_abs
          nlinarith [sq_nonneg (x + 2), sq_nonneg (y - 10)]
      · -- Case 2: 5x + y < 0
        by_cases h2 : 5 * x - y ≥ 0
        · -- Case 2a: 5x - y >= 0
          rw [abs_of_neg (lt_of_not_ge h1), abs_of_nonneg h2] at h_abs
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 10)]
        · -- Case 2b: 5x - y < 0
          rw [abs_of_neg (lt_of_not_ge h1), abs_of_neg (lt_of_not_ge h2)] at h_abs
          nlinarith [sq_nonneg (y - 10), sq_nonneg (x + 2)]
  · -- Show that 3 is the least element of the set
    constructor
    · -- Show that 3 is in the set
      use (2 : ℝ), (1 : ℝ)
      norm_num [abs]
      <;> norm_num
    · -- Show that 3 is the least value in the set
      intro t ht
      rcases ht with ⟨x, y, ht_eq, h_abs⟩
      by_cases h1 : 5 * x + y ≥ 0
      · -- Case 1: 5x + y >= 0
        by_cases h2 : 5 * x - y ≥ 0
        · -- Case 1a: 5x - y >= 0
          rw [abs_of_nonneg h1, abs_of_nonneg h2] at h_abs
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1)]
        · -- Case 1b: 5x - y < 0
          rw [abs_of_nonneg h1, abs_of_neg (lt_of_not_ge h2)] at h_abs
          nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 10)]
      · -- Case 2: 5x + y < 0
        by_cases h2 : 5 * x - y ≥ 0
        · -- Case 2a: 5x - y >= 0
          rw [abs_of_neg (lt_of_not_ge h1), abs_of_nonneg h2] at h_abs
          nlinarith [sq_nonneg (x + 5), sq_nonneg (y + 10)]
        · -- Case 2b: 5x - y < 0
          rw [abs_of_neg (lt_of_not_ge h1), abs_of_neg (lt_of_not_ge h2)] at h_abs
          nlinarith [sq_nonneg (y + 1), sq_nonneg (x + 2)]