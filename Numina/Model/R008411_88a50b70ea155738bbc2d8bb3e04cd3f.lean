import Mathlib

theorem algebra_15515 (P : ℝ) (hP : P = 1000) (r : ℝ) (hr : r = 0.01) (t : ℕ) (ht : t = 5) :
  round (P * (1 + r)^t - P) = 51 := by
  rw [hP, hr, ht]
  norm_num [round_eq]
  <;> norm_num