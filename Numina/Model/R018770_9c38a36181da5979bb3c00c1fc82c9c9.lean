import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_281828 :
  IsGreatest {z : ℝ | ∃ x y, z = x^2 - x * y + y^2 ∧ abs (5 * x + y) + abs (5 * x - y) = 20} 124 ∧
  IsLeast {z : ℝ | ∃ x y, z = x^2 - x * y + y^2 ∧ abs (5 * x + y) + abs (5 * x - y) = 20} 3 := by
  constructor
  · -- Prove 124 is greatest in the set
    constructor
    · -- Show 124 is achievable
      use -2, 10
      constructor
      · -- Verify $z = x^2 - x * y + y^2$ 
        norm_num
      · -- Verify constraint 
        norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Show no greater element is in the set
      intro z h
      rcases h with ⟨x, y, h_eq, h_abs⟩
      have h1 : abs (5 * x + y) + abs (5 * x - y) = 20 := h_abs
      by_cases h2 : (5 * x + y) ≥ 0
      · -- Case $5x + y \geq 0$
        by_cases h3 : (5 * x - y) ≥ 0
        · -- Case $5x - y \geq 0$
          rw [abs_of_nonneg h2, abs_of_nonneg h3] at h1
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 10), sq_nonneg (x + 2), sq_nonneg (y + 10)]
        · -- Case $5x - y < 0$
          rw [abs_of_nonneg h2, abs_of_neg (lt_of_not_ge h3)] at h1
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 10), sq_nonneg (x + 2), sq_nonneg (y + 10)]
      · -- Case $5x + y < 0$
        by_cases h4 : (5 * x - y) ≥ 0
        · -- Case $5x - y \geq 0$
          rw [abs_of_neg (lt_of_not_ge h2), abs_of_nonneg h4] at h1
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 10), sq_nonneg (x + 2), sq_nonneg (y + 10)]
        · -- Case $5x - y < 0$
          rw [abs_of_neg (lt_of_not_ge h2), abs_of_neg (lt_of_not_ge h4)] at h1
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 10), sq_nonneg (x + 2), sq_nonneg (y + 10)]
  · -- Prove 3 is least in the set
    constructor
    · -- Show 3 is achievable
      use 2, 1
      constructor
      · -- Verify $z = x^2 - x * y + y^2$ 
        norm_num
      · -- Verify constraint 
        norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Show no smaller element is in the set
      intro z h
      rcases h with ⟨x, y, h_eq, h_abs⟩
      have h1 : abs (5 * x + y) + abs (5 * x - y) = 20 := h_abs
      by_cases h2 : (5 * x + y) ≥ 0
      · -- Case $5x + y \geq 0$
        by_cases h3 : (5 * x - y) ≥ 0
        · -- Case $5x - y \geq 0$
          rw [abs_of_nonneg h2, abs_of_nonneg h3] at h1
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (x + 2), sq_nonneg (y + 1)]
        · -- Case $5x - y < 0$
          rw [abs_of_nonneg h2, abs_of_neg (lt_of_not_ge h3)] at h1
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (x + 2), sq_nonneg (y + 1)]
      · -- Case $5x + y < 0$
        by_cases h4 : (5 * x - y) ≥ 0
        · -- Case $5x - y \geq 0$
          rw [abs_of_neg (lt_of_not_ge h2), abs_of_nonneg h4] at h1
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (x + 2), sq_nonneg (y + 1)]
        · -- Case $5x - y < 0$
          rw [abs_of_neg (lt_of_not_ge h2), abs_of_neg (lt_of_not_ge h4)] at h1
          nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (x + 2), sq_nonneg (y + 1)]