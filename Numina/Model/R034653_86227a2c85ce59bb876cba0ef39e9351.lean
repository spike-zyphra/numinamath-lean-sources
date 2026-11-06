import Mathlib

theorem algebra_21725:
    IsGreatest {p : ℝ | ∃(x y z : ℝ), 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ 
                          x^2 + 2 * y^2 + 5 * z^2 = 22 ∧ 
                          p = x * y + x * z + y * z} 11 := by
  constructor
  · -- Show 11 is in the set
    use 3, 2, 1
    norm_num
  · -- Show that 11 is the greatest element in the set
    intro p hp
    rcases hp with ⟨x, y, z, hx, hy, hz, h_eq, hp⟩
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 2), sq_nonneg (z - 1),
              mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]