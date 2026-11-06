import Mathlib

open Real

theorem algebra_216249 :
    IsLeast {t : ℝ | ∃x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = x * y * z ∧ t = x ^ 2 * (y * z - 1) + y ^ 2 * (z * x - 1) + z ^ 2 * (x * y - 1)} 18 := by
  constructor
  · use √3
    use √3
    use √3
    field_simp
    constructor <;> linarith
  · intro t
    rintro ⟨x, y, z, hx, hy, hz, h, ht⟩
    rw [ht]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), mul_self_nonneg (x - 2), mul_self_nonneg (y - 2), mul_self_nonneg (z - 2)]