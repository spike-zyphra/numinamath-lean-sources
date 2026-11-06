import Mathlib

theorem algebra_97643 {x : ℝ} (hx : x ≠ 0) (h : (x / 2) * (1 - 20 / 100) = x * (1 - y / 100)) :
    y = 60 := by
  have eq2 : (x / 2) * (1 - 20 / 100 : ℝ) = 0.4 * x := by
    ring_nf
  rw [eq2] at h
  apply (mul_left_inj' hx).mp
  linarith