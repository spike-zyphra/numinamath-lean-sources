import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_176726 :
  IsGreatest {t : ℝ | ∃ x y : ℝ, t = x^2 - x * y + y^2 ∧ |5 * x + y| + |5 * x - y| = 20} 124 ∧
  IsLeast {t : ℝ | ∃ x y : ℝ, t = x^2 - x * y + y^2 ∧ |5 * x + y| + |5 * x - y| = 20} 3 := by
  constructor 
  · -- Show 124 is greatest
    constructor 
    · -- Show 124 is in the set.
      use -2, 10 
      norm_num [abs]
    · -- Show any element in the set is ≤ 124.
      intro t ht
      rcases ht with ⟨x, y, ht_eq, h⟩
      have h1 : |5 * x + y| + |5 * x - y| = 20 := h
      by_cases h2 : (5 * x + y) ≥ 0 
      · -- Case where 5x + y ≥ 0
        rw [abs_of_nonneg h2] at h1
        by_cases h3 : (5 * x - y) ≥ 0 
        · -- Case where 5x + y ≥ 0 and 5x - y ≥ 0
          rw [abs_of_nonneg h3] at h1 
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 10), sq_nonneg (y - 10), sq_nonneg (x + 2)]
        · -- Case where 5x + y ≥ 0 and 5x - y < 0 
          rw [abs_of_neg (show 5 * x - y < 0 by linarith)] at h1 
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 10), sq_nonneg (y + 10), sq_nonneg (x + 2)]
      · -- Case where 5x + y < 0
        rw [abs_of_neg (show (5 * x + y) < 0 by linarith)] at h1
        by_cases h3 : (5 * x - y) ≥ 0 
        · -- Case where 5x + y < 0 and 5x - y ≥ 0 
          rw [abs_of_nonneg h3] at h1
          nlinarith [sq_nonneg (x + 2), sq_nonneg (y + 10), sq_nonneg (y - 10), sq_nonneg (x - 2)]
        · -- Case where 5x + y < 0 and 5x - y < 0 
          rw [abs_of_neg (show (5 * x - y) < 0 by linarith)] at h1
          nlinarith [sq_nonneg (x + 2), sq_nonneg (y - 10), sq_nonneg (y + 10), sq_nonneg (x - 2)]
  · -- Show 3 is the least 
    constructor 
    · -- Show 3 is in the set.
      use 2, 1 
      norm_num [abs]
    · -- Show any element in the set is ≥ 3.
      intro t ht 
      rcases ht with ⟨x, y, ht_eq, h⟩ 
      have h1 : |5 * x + y| + |5 * x - y| = 20 := h
      by_cases h2 : (5 * x + y) ≥ 0 
      · -- Case 1: 5x + y ≥ 0
        rw [abs_of_nonneg h2] at h1 
        by_cases h3 : (5 * x - y) ≥ 0 
        · -- Subcase 1a: 5x - y ≥ 0 
          rw [abs_of_nonneg h3] at h1 
          have h3' : x^2 - x * y + y^2 ≥ 3 := by 
            nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1), sq_nonneg (x - 2), sq_nonneg (x + 2)]
          linarith [ht_eq, h3']
        · -- Subcase 1b: 5x - y < 0 
          rw [abs_of_neg (show 5 * x - y < 0 by linarith)] at h1 
          have h3' : x^2 - x * y + y^2 ≥ 3 := by 
            nlinarith [sq_nonneg (y - 10), sq_nonneg (y + 10), sq_nonneg (x - 2), sq_nonneg (x + 2)]
          linarith [ht_eq, h3']
      · -- Case 2: 5x + y < 0 
        rw [abs_of_neg (show (5 * x + y) < 0 by linarith)] at h1 
        by_cases h3 : (5 * x - y) ≥ 0 
        · -- Subcase 2a: 5x - y ≥ 0 
          rw [abs_of_nonneg h3] at h1 
          have h3' : x^2 - x * y + y^2 ≥ 3 := by 
            nlinarith [sq_nonneg (y - 10), sq_nonneg (y + 10), sq_nonneg (x + 2), sq_nonneg (x - 2)]
          linarith [ht_eq, h3']
        · -- Subcase 2b: 5x - y < 0 
          rw [abs_of_neg (show (5 * x - y) < 0 by linarith)] at h1 
          have h1_eq : x = -2 := by 
            linarith 
          have h3' : x^2 - x * y + y^2 ≥ 3 := by 
            rw [show x = -2 by linarith] 
            nlinarith [sq_nonneg (y + 1), sq_nonneg (y - 1), sq_nonneg (y)]
          linarith [ht_eq, h3']