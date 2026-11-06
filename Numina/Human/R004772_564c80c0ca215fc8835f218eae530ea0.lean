import Mathlib

theorem algebra_321261 : IsLeast {t : ℝ | ∃x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧  x * y * z * (x + y + z) = 1 ∧ t = (x + y) * (y + z)} 2 := by
  constructor
  · use 1, √2 - 1, 1
    simp
    constructor
    · rw [Real.lt_sqrt (by norm_num)]
      norm_num
    · ring_nf
      norm_num
  · intro t
    rintro ⟨x, y, z, hx, hy, hz, h, ht⟩
    nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
      h, mul_self_nonneg (x - 1), mul_self_nonneg (z - 1),
      mul_self_nonneg (x - z), sq_nonneg (x - z),
      sq_nonneg (y - 1), sq_nonneg (y - x), sq_nonneg (y - z),
      sq_nonneg (x * z - 1), sq_nonneg (x - z)]
