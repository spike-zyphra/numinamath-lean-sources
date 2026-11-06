import Mathlib

theorem algebra_125507 {a b : ℝ} (h : a + b = 4) : a^3 + b^3 + 12 * a * b = 64 := by
  have hb : b = 4 - a := by linarith
  rw [hb]
  ring_nf