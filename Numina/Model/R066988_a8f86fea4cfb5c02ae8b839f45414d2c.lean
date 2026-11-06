import Mathlib

open Real

theorem algebra_13962 : ⌊Real.pi - 4⌋ = -1 := by
  have h1 : Real.pi > 3 := by
    linarith [Real.pi_gt_31415]
  have h4 : Real.pi < 3.1416 := by
    linarith [Real.pi_lt_31416]
  have h3 : Real.pi - 4 > (-1 : ℝ) := by
    linarith
  have h5 : Real.pi - 4 < (0 : ℝ) := by
    linarith [Real.pi_lt_31416]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> (try linarith)