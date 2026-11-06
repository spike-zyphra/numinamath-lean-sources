import Mathlib

theorem algebra_192654 {M : ℚ} (hM : M = (78^3 + 22^3) / (78^2 - 78 * 22 + 22^2)) : M = 100 := by
  rw [hM]
  norm_num