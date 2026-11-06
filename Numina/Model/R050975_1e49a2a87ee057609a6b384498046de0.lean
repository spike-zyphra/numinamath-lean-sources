import Mathlib

open Real

theorem algebra_1122 : abs (Real.pi - 3.14) + abs (Real.pi - 22 / 7) = 1 / 350 := by

  have h1 : Real.pi - 3.14 > 0 := by
    have hpi1 : Real.pi > 3.1415 := by
      linarith [Real.pi_gt_31415, Real.pi_lt_31416]
    norm_num at hpi1 ⊢
    linarith
  have h2 : Real.pi - (22 / 7 : ℝ) < 0 := by
    have hpi2 : Real.pi < 3.1416 := by
      linarith [Real.pi_lt_31416]
    norm_num at hpi2 ⊢
    linarith

  rw [abs_of_pos h1, abs_of_neg h2]

  -- Now compute the expression: (Real.pi - 3.14) + (22 / 7 - Real.pi)
  -- Real.pi cancels
  -- Left with 22 / 7 - 3.14
  -- Convert to a fraction
  -- 22/7 = 3.142857142857
  -- 3.14 = 3 + 14/100
  -- 22/7 - 3.14 = 22/7 - 157/50
  -- Convert to common denominator 350
  -- 22/7 = 1100/350
  -- 157/50 = 1099/350
  -- 1100/350 - 1099/350 = 1/350
  linarith [Real.pi_gt_31415, Real.pi_lt_31416]