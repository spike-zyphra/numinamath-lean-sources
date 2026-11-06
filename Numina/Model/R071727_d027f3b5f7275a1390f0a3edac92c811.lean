import Mathlib

theorem algebra_160183 (a b : ℝ × ℝ) (ha : a = (1, 2)) (hb : b = (-3, 2)) :
    ∃ k, (k * a.1 + b.1) / (k * a.2 + b.2) = (a.1 - 3 * b.1) / (a.2 - 3 * b.2) := by
  use -1 / 3
  rw [ha, hb]
  norm_num
  <;> norm_num