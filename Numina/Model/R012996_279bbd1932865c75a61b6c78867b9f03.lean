import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_198551 (x y : ℝ) (h : x^2/3 + y^2 = 1) :
    2 ≤ abs (2*x + y - 4) + abs (4 - x - 2*y) ∧ abs (2*x + y - 4) + abs (4 - x - 2*y) ≤ 14 := by
  have h1 : 2 * x + y - 4 < 0 := by 
    nlinarith [sq_nonneg (x - 2 * Real.sqrt 3), sq_nonneg (y - 1), Real.sqrt_pos.mpr (show 0 < 3 by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (x + 2 * Real.sqrt 3), sq_nonneg (y + 1), sq_nonneg (x - 3 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x + 3 / 2), sq_nonneg (y + 1 / 2)]
  have h2 : abs (2 * x + y - 4) = 4 - (2 * x + y) := by 
    rw [abs_of_neg (by linarith)]
    all_goals linarith
  have h3 : 4 - x - 2 * y > 0 := by 
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (x + 2), sq_nonneg (y + 1), sq_nonneg (x - 3 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x + 3 / 2), sq_nonneg (y + 1 / 2)]
  have h4 : abs (4 - x - 2 * y) = 4 - x - 2 * y := by 
    rw [abs_of_pos (by linarith)]
  have hp : abs (2 * x + y - 4) + abs (4 - x - 2 * y) = 8 - 3 * x - 3 * y := by 
    linarith [h2, h4]
  have h5 : -2 ≤ x + y := by 
    nlinarith [sq_nonneg (x - 3 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x + 3 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (x - 3 * y), sq_nonneg (x + 3 * y), h]
  have h6 : x + y ≤ 2 := by 
    nlinarith [sq_nonneg (x - 3 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x + 3 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (x - 3 * y), sq_nonneg (x + 3 * y), h]
  constructor
  · -- Show that P ≥ 2
    nlinarith [hp, h5, h6]
  · -- Show that P ≤ 14
    nlinarith [hp, h5, h6]