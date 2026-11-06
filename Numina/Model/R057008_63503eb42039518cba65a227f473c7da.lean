import Mathlib

theorem algebra_280071 {a : ℝ} (ha : a = 1.41 * 100) : ⌊a - 1.41⌋ = 139 := by
  rw [ha]
  norm_num [Int.floor_eq_iff]