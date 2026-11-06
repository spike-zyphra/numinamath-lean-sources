import Mathlib

theorem algebra_13086 (cedric daniel : ℝ)
    (hcedric : cedric = 12000 * (1 + 0.05)^15)
    (hdaniel : daniel = 12000 * (1 + 0.07 * 15)) :
    round (cedric - daniel) = 347 := by
  rw [hcedric, hdaniel]
  norm_num [round_eq]
  <;> ring_nf <;> norm_num