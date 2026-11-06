import Mathlib

open Real Set

theorem algebra_12387 : IsLeast {a : ℝ | ∃ x y z, x ^ 2 + 6 * x * y + 18 * y ^ 2 + 12 * y * z + 4 * z ^ 2 = a ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧ x * y * z = 2 / 3} 18 := by
  constructor
  · -- Show 18 is achievable.
    use 2, 1 / 3, 1
    norm_num
  · -- Show 18 is the minimum.
    intro a ha
    rcases ha with ⟨x, y, z, h1, hx, hy, hz, h2⟩
    have h4 : x ^ 2 + 6 * x * y + 18 * y ^ 2 + 12 * y * z + 4 * z ^ 2 ≥ 18 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1 / 3), sq_nonneg (z - 1),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    linarith