import Mathlib

theorem algebra_97202 {a : ℝ} (ha : a ≠ 0) (ha' : a = 1 / 2) : (2 / a + 1 / (2 * a)) / a = 10 := by
  rw [ha']
  norm_num