import Mathlib

open Real Set
open scoped Real

theorem inequalities_272761 (x : ℝ) :
  18 ≥ 5 + 8 * cos x + 4 * cos (2 * x) + cos (3 * x) ∧
  5 + 8 * cos x + 4 * cos (2 * x) + cos (3 * x) ≥ 0 := by

  have h1 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by 
    rw [cos_two_mul]

  have h2 : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by 
    rw [cos_three_mul]

  have h3 : 5 + 8 * cos x + 4 * cos (2 * x) + cos (3 * x) = 4 * cos x ^ 3 + 8 * cos x ^ 2 + 5 * cos x + 1 := by 
    rw [h1, h2]
    ring

  rw [h3] at *
  constructor
  · -- Prove the upper bound: 18 ≥ 4 * cos x ^ 3 + 8 * cos x ^ 2 + 5 * cos x + 1
    nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1 / 2), sq_nonneg (cos x + 5 / 6), sq_nonneg (cos x - 1), cos_le_one x, neg_one_le_cos x, sq_nonneg (cos x ^ 2 - 1), sq_nonneg (cos x + 1)]
  · -- Prove the lower bound: 4 * cos x ^ 3 + 8 * cos x ^ 2 + 5 * cos x + 1 ≥ 0
    nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1 / 2), sq_nonneg (cos x + 5 / 6), sq_nonneg (cos x - 1), cos_le_one x, neg_one_le_cos x, sq_nonneg (cos x ^ 2 - 1), sq_nonneg (cos x + 1)]