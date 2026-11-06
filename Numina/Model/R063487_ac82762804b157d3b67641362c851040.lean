import Mathlib

theorem algebra_21099 (P : ℝ) (hP : P = 24000) (r : ℝ) (hr : r = 0.01) (t : ℝ) (ht : t = 5 * 12 / 2) :
  round (P * (1 + r) ^ t) = 32348 := by
  rw [hP, hr, ht]
  norm_num [round_eq]
  <;> ring_nf <;> norm_num