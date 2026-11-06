import Mathlib

open Real

theorem calculus_15575 : arccos (cos 7) = 7 - 2 * π := by
  have h1 : cos 7 = cos (7 - 2 * π) := by
    rw [show 7 - 2 * π = 7 - (2 * π) by ring]
    rw [cos_sub, cos_two_pi, sin_two_pi]
    all_goals norm_num
    all_goals ring
  have h3 : 0 ≤ 7 - 2 * π := by
    linarith [Real.pi_gt_31415, Real.pi_lt_31416]
  have h4 : 7 - 2 * π ≤ Real.pi := by
    nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
  have h5 : arccos (cos (7 - 2 * π)) = 7 - 2 * π := by 
    rw [arccos_cos]
    all_goals linarith
  rw [show cos 7 = cos (7 - 2 * π) by linarith [h1]]
  exact h5