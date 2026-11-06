import Mathlib

theorem algebra_5546 :
    IsLeast {A : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x * y + y * z + z * x - x * y * z = 2 ∧ A = x ^ 2 + y ^ 2 + z ^ 2} 3 := by
  constructor
  · -- Show 3 is in the set
    use 1, 1, 1
    norm_num
  · -- Show there is no value less than 3 in the set
    intro A h
    rcases h with ⟨x, y, z, hx, hy, hz, h1, h2⟩
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
        mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]