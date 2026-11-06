import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_597650 (x : ℝ) (hx : 3/2 ≤ x ∧ x ≤ 5) :
    2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x) < 2 * sqrt 19 := by
  have h1 : 0 ≤ x + 1 := by linarith
  have h2 : 0 ≤ 2 * x - 3 := by
    linarith
  have h3 : 0 ≤ 15 - 3 * x := by
    linarith
  have h4 : 0 ≤ 2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x) := by
    positivity
  have h5 : 0 ≤ 2 * sqrt 19 := by
    positivity
  suffices (2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x)) ^ 2 < (2 * sqrt 19) ^ 2 by
    nlinarith [Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x), Real.sqrt_nonneg 19]
  
  have h6 : (2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x)) ^ 2 =
      4 * (x + 1) + (2 * x - 3) + (15 - 3 * x) + 4 * (sqrt (x + 1) * sqrt (2 * x - 3)) + 4 * (sqrt (x + 1) * sqrt (15 - 3 * x)) + 2 * (sqrt (2 * x - 3) * sqrt (15 - 3 * x)) := by
    calc
      (2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x)) ^ 2 
          = (2 * sqrt (x + 1)) ^ 2 + (sqrt (2 * x - 3)) ^ 2 + (sqrt (15 - 3 * x)) ^ 2 + 2 * (2 * sqrt (x + 1) * sqrt (2 * x - 3) + 2 * sqrt (x + 1) * sqrt (15 - 3 * x) + sqrt (2 * x - 3) * sqrt (15 - 3 * x)) := by ring
      _ = 4 * (sqrt (x + 1) ^ 2) + (sqrt (2 * x - 3) ^ 2) + (sqrt (15 - 3 * x) ^ 2) + 4 * (sqrt (x + 1) * sqrt (2 * x - 3)) + 4 * (sqrt (x + 1) * sqrt (15 - 3 * x)) + 2 * (sqrt (2 * x - 3) * sqrt (15 - 3 * x)) := by ring 
      _ = 4 * (x + 1) + (2 * x - 3) + (15 - 3 * x) + 4 * (sqrt (x + 1) * sqrt (2 * x - 3)) + 4 * (sqrt (x + 1) * sqrt (15 - 3 * x)) + 2 * (sqrt (2 * x - 3) * sqrt (15 - 3 * x)) := by 
        rw [Real.sq_sqrt (show 0 ≤ (x + 1 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (2 * x - 3 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (15 - 3 * x : ℝ) by linarith)]
        <;> nlinarith
  
  have h8 : (2 * sqrt 19) ^ 2 = 4 * 19 := by
    calc
      (2 * sqrt 19) ^ 2 = 4 * (sqrt 19) ^ 2 := by ring
      _ = 4 * 19 := by 
        rw [Real.sq_sqrt]
        all_goals norm_num
  
  rw [h6, h8]
  nlinarith [sq_nonneg (2 * sqrt (x + 1) - sqrt (2 * x - 3) - sqrt (15 - 3 * x)), sq_nonneg (sqrt (x + 1) - sqrt (2 * x - 3)), sq_nonneg (sqrt (x + 1) - sqrt (15 - 3 * x)), sq_nonneg (sqrt (2 * x - 3) - sqrt (15 - 3 * x)), 
          Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x),
          Real.sq_sqrt (show 0 ≤ (x + 1 : ℝ) by linarith),
          Real.sq_sqrt (show 0 ≤ (2 * x - 3 : ℝ) by linarith),
          Real.sq_sqrt (show 0 ≤ (15 - 3 * x : ℝ) by linarith),
          Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num),
          Real.sqrt_le_sqrt (show 0 ≤ (x + 1 : ℝ) by linarith),
          Real.sqrt_le_sqrt (show 0 ≤ (2 * x - 3 : ℝ) by linarith),
          Real.sqrt_le_sqrt (show 0 ≤ (15 - 3 * x : ℝ) by linarith),
          Real.sqrt_le_sqrt (show 0 ≤ (19 : ℝ) by norm_num),
          hx.1, hx.2, Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x), Real.sqrt_nonneg 19,Real.sqrt_nonneg 19, mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg 19), mul_nonneg (Real.sqrt_nonneg (2 * x - 3)) (Real.sqrt_nonneg 19), mul_nonneg (Real.sqrt_nonneg (15 - 3 * x)) (Real.sqrt_nonneg 19)]