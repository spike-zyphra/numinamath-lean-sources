import Mathlib

theorem algebra_2409 {x : ℝ} (hx : x^3 = 521.077119823) : (x / 10)^3 = 0.521077119823 := by
  have h1 : (x / 10)^3 = (x^3) / (10^3 : ℝ) := by
    ring_nf
  rw [h1, hx]
  norm_num