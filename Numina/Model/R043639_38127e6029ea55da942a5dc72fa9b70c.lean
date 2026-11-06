import Mathlib

open Real

theorem algebra_20963 :
    IsLeast {r : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y + x * z + y * z = 1 ∧ r = 10 * x ^ 2 + 10 * y ^ 2 + z ^ 2} 4 := by

  constructor
  · -- Show that 4 is in the set
    use 1 / 3, 1 / 3, 4 / 3
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num
  · -- Show that no smaller value is in the set
    intro r hr
    rcases hr with ⟨x, y, z, hx, hy, hz, h1, hr⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg (z - 4 / 3), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]