import Mathlib

open Real

theorem algebra_119107 (x y : ℝ) (h1 : abs (x - 1 / 2) ≤ 3 / 2) (h2 : abs (y - 1 / 2) ≤ 3 / 2)
    (h3 : Real.sqrt ((2 - x) * (y + 1)) + Real.sqrt ((2 - y) * (x + 1)) = 3) :
    x + y = 1 := by
  rw [abs_le] at h1 h2
  have h4 : (3 : ℝ) =  1 / 2 * (2 - x + (y + 1)) + 1 / 2 * (2 - y + (x + 1)) := by ring
  rw [h4] at h3
  nth_rw 2 [← sq_sqrt (show 0≤2-x by linarith)] at h3
  nth_rw 2 [← sq_sqrt (show 0≤2-y by linarith)] at h3
  nth_rw 2 [← sq_sqrt (show 0≤x+1 by linarith)] at h3
  nth_rw 2 [← sq_sqrt (show 0≤y+1 by linarith)] at h3
  symm at h3; rw [← sub_eq_zero] at h3
  have h5 :  1 / 2 * (√(2 - x) ^ 2 + √(y + 1) ^ 2) + 1 / 2 * (√(2 - y) ^ 2 + √(x + 1) ^ 2) -
    (√((2 - x) * (y + 1)) + √((2 - y) * (x + 1))) = 1 / 2 * (√(2 - x) - √(y + 1)) ^ 2 + 1 / 2 * (√(2 - y) - √(x + 1)) ^ 2 := by
      rw [sqrt_mul, sqrt_mul]; ring
      all_goals linarith
  have h6 :  0 ≤ 1 / 2 * (√(2 - x) - √(y + 1)) ^ 2 := by positivity
  have h7 : 0 ≤ 1 / 2 * (√(2 - y) - √(x + 1)) ^ 2 := by positivity
  replace h6 : (√(2 - x) - √(y + 1)) ^ 2 = 0 := by linarith
  replace h7 : (√(2 - y) - √(x + 1)) ^ 2 = 0 := by linarith
  simp at h6; rw [sub_eq_zero] at h6
  apply_fun fun t => t ^ 2 at h6
  rw [sq_sqrt, sq_sqrt] at h6
  symm at h6; rw [← eq_sub_iff_add_eq] at h6
  rw [h6]; ring
  all_goals linarith