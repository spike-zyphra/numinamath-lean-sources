import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_300300 :
  IsGreatest {t : ℝ | ∃ x y, t = x^2 - x * y + y^2 ∧ |5 * x + y| + |5 * x - y| = 20} 124 ∧
  IsLeast {t : ℝ | ∃ x y, t = x^2 - x * y + y^2 ∧ |5 * x + y| + |5 * x - y| = 20} 3 := by

  constructor
  · -- Show that 124 is greatest
    constructor
    · -- Show 124 is in the set
      use 2, -10
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Show all elements in the set are ≤ 124
      intro t ht
      rcases ht with ⟨x, y, h_eq, h_abs⟩

      by_cases h1 : (5 * x + y) ≥ 0 
      · -- Case where 5x+y ≥ 0
        by_cases h2 : (5 * x - y) ≥ 0
        · -- Case where both are non-negative
          rw [abs_of_nonneg h1, abs_of_nonneg h2] at h_abs
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 10), sq_nonneg (x * y), sq_nonneg ((5 * x) - y), sq_nonneg ((5 * x) + y)]
        · -- Case where 5x+y ≥0 and 5x-y < 0
          rw [abs_of_nonneg h1, abs_of_neg (by linarith)] at h_abs
          nlinarith [sq_nonneg (x * y), sq_nonneg ((5 * x) - y), sq_nonneg ((5 * x) + y), sq_nonneg (x - 2), sq_nonneg (y - 10)]
      · -- Case where 5x+y <0
        by_cases h2 : (5 * x - y) ≥ 0 
        · -- Case where 5x-y >=0 and 5x+y <0
          rw [abs_of_neg (by linarith), abs_of_nonneg h2] at h_abs
          nlinarith [sq_nonneg (x * y), sq_nonneg ((5 * x) - y), sq_nonneg ((5 * x) + y), sq_nonneg (x + 2), sq_nonneg (y + 10)]
        · -- Case where both are negative
          rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h_abs 
          have eq1 : x = -2 := by 
            linarith
          have eq2 : t = 4 + 2 * y + y^2 := by 
            rw [h_eq]
            rw [eq1]
            ring
          nlinarith [sq_nonneg (y + 1)]
  
  · -- Show that 3 is the least element
    constructor
    · -- Show that 3 is in the set
      use 2, 1
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Show that all elements in the set are ≥ 3
      intro t ht
      rcases ht with ⟨x, y, h_eq, h_abs⟩
      by_cases h1 : (5 * x + y) ≥ 0 
      · -- Case where 5x+y ≥ 0
        by_cases h2 : (5 * x - y) ≥ 0
        · -- Case 1a: Both non-negative
          rw [abs_of_nonneg h1, abs_of_nonneg h2] at h_abs
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (x * y), sq_nonneg ((5 * x) - y), sq_nonneg ((5 * x) + y)]
        · -- Case 1b: One non-negative, one negative
          rw [abs_of_nonneg h1, abs_of_neg (by linarith)] at h_abs
          nlinarith [sq_nonneg (x * y), sq_nonneg ((5 * x) - y), sq_nonneg ((5 * x) + y), sq_nonneg (x - 2), sq_nonneg (y - 1)]
      · -- Case where 5x+y <0
        by_cases h2 : (5 * x - y) ≥ 0 
        · -- Case 2a: One negative, one non-negative
          rw [abs_of_neg (by linarith), abs_of_nonneg h2] at h_abs
          nlinarith [sq_nonneg (x * y), sq_nonneg ((5 * x) - y), sq_nonneg ((5 * x) + y), sq_nonneg (x + 2), sq_nonneg (y + 10)]
        · -- Case 2b: Both negative
          rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h_abs 
          have eq1 : x = -2 := by 
            linarith
          have eq2 : t = 4 + 2 * y + y^2 := by 
            rw [h_eq]
            rw [eq1]
            ring
          nlinarith [sq_nonneg (y + 1)]