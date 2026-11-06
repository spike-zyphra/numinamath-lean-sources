import Mathlib

theorem algebra_10278 : ⌈-√(49 / 4)⌉ = -3 := by
  have h1 : √(49 / 4 : ℝ) = 7 / 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : -√(49 / 4 : ℝ) = -7 / 2 := by
    rw [h1]
    all_goals norm_num
  rw [h2]
  norm_num [Int.ceil_eq_iff]