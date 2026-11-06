import Mathlib

theorem calculus_12733 :
    abs (1 / 2 - (5 / 4)) / Real.sqrt ((1 ^ 2 + 2 ^ 2 + (-2) ^ 2) / 4) = 1 / 2 := by
  have h1 : abs (1 / 2 - (5 / 4) : ℝ) = (3 / 4 : ℝ) := by 
    norm_num [abs_of_neg]
  have h2 : Real.sqrt ((1 ^ 2 + 2 ^ 2 + (-2) ^ 2 : ℝ) / 4) = (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h1, h2]
  all_goals norm_num
  <;> ring_nf <;> norm_num