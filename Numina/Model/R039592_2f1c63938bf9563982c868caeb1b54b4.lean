import Mathlib

open Real

theorem algebra_15078 :
    IsLeast {v | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      x * y * z = 32 ∧
      v = x ^ 2 + 4 * x * y + 4 * y ^ 2 + 2 * z ^ 2} 96 := by
  constructor
  · -- Show 96 is in the set
    use 4, 2, 4
    constructor
    · norm_num -- 0 < x
    constructor
    · norm_num -- 0 < y
    constructor
    · norm_num -- 0 < z
    constructor
    · norm_num -- x * y * z = 32
    · norm_num -- v = ...
  · -- Show 96 is the least element in the set
    intro v hv
    rcases hv with ⟨x, y, z, hx, hy, hz, hxyz, hv⟩
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 2), sq_nonneg (z - 4),
      sq_nonneg (x * y - 8), sq_nonneg (y * z - 8), sq_nonneg (x * z - 16),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      sq_nonneg (x + 2 * y - 8), sq_nonneg (z - 4)]