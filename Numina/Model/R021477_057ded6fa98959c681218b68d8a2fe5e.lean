import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_140271 :
  IsGreatest {x | ∃ a b : ℝ, x = sqrt (8 * b - 6 * a + 50) + sqrt (8 * b + 6 * a + 50) ∧ a ^ 2 + b ^ 2 = 25} (6 * sqrt 10) := by
  constructor
  · -- First part: Show that 6 * sqrt(10) belongs to the set
    use 0, 5
    constructor
    · -- Show the value of the function at (0, 5)
      have h1 : sqrt (8 * (5 : ℝ) - 6 * (0 : ℝ) + 50) = sqrt 90 := by norm_num
      have h2 : sqrt (8 * (5 : ℝ) + 6 * (0 : ℝ) + 50) = sqrt 90 := by norm_num
      rw [h1, h2]
      have h3 : sqrt 90 = 3 * sqrt 10 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h3]
      ring
    · -- Show the constraint
      norm_num
  · -- Second part: Show that 6 * sqrt(10) is the greatest
    rintro x ⟨a, b, hx, h_circle⟩
    have h1 : sqrt (8 * b - 6 * a + 50) + sqrt (8 * b + 6 * a + 50) ≤ 6 * sqrt 10 := by
      nlinarith [sq_nonneg (sqrt (8 * b - 6 * a + 50) - sqrt (8 * b + 6 * a + 50)), 
          sq_nonneg (a - 3 * b / 4), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 8 * b - 6 * a + 50 by nlinarith [sq_nonneg (a - 3 * b / 4), sq_nonneg (a + 3 * b / 4), sq_nonneg (b - 5), sq_nonneg (b + 5)]), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 8 * b + 6 * a + 50 by nlinarith [sq_nonneg (a - 3 * b / 4), sq_nonneg (a + 3 * b / 4), sq_nonneg (b - 5), sq_nonneg (b + 5)]), 
          Real.sqrt_nonneg (8 * b - 6 * a + 50), 
          Real.sqrt_nonneg (8 * b + 6 * a + 50), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), 
          Real.sqrt_nonneg (10), 
          sq_nonneg (a), 
          sq_nonneg (b), 
          sq_nonneg (a - 0), 
          sq_nonneg (b - 5)
          ]
    linarith [h1, hx]