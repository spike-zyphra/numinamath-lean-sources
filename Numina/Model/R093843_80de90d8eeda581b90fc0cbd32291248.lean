import Mathlib

open Real

theorem algebra_13437 :
    IsLeast {a | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z = 8 ∧ a = x + 2 * y + 4 * z} 12 := by
  constructor
  · -- Show 12 is in the set
    use 4, 2, 1
    norm_num
  · -- Show no number less than 12 is in the set
    intro a h
    rcases h with ⟨x, y, z, hx, hy, hz, h1, ha⟩
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 2), sq_nonneg (z - 1),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
      sq_nonneg ((x / 4) - 1), sq_nonneg ((y / 2) - 1), sq_nonneg ((z / 1) - 1)]