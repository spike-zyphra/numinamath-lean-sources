import Mathlib
theorem algebra_21415 (P : ℝ) (r : ℝ) (t : ℝ) (hP : P = 1000) (hr : r = 0.075) (ht : t = 2) :
    round (P * (1 + r / 4) ^ (4 * t)) = 1160 := by
  rw [hP, hr, ht]
  norm_num [round_eq]