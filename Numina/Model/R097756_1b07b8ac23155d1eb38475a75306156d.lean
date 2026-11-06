import Mathlib

theorem algebra_122871 :
    IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z = 32 ∧ t = x ^ 2 + 4 * x * y + 4 * y ^ 2 + 2 * z ^ 2} 96 := by
  constructor
  · -- Show that 96 is achievable, with x = 4, y = 2, z = 4
    use 4, 2, 4
    norm_num
  · -- Show that 96 is the least element in the set
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, hxyz, ht⟩
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 2), sq_nonneg (z - 4), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
    ]