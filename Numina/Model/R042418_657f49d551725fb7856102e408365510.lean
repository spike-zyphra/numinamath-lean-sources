import Mathlib

open Real

theorem algebra_2969 : (√(995 * 997 * 1003 * 1005 + 64) - √(495 * 497 * 503 * 505 + 64)) = 750000 := by
  have h1 : √(995 * 997 * 1003 * 1005 + 64) = 999983 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h2 : √(495 * 497 * 503 * 505 + 64) = 249983 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  rw [h1, h2]
  all_goals norm_num