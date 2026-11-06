import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_203977 :
  IsLeast {f | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 1 ∧ f =
    (3 * x ^ 2 - x) / (1 + x ^ 2) + (3 * y ^ 2 - y) / (1 + y ^ 2) +
    (3 * z ^ 2 - z) / (1 + z ^ 2)} 0 := by
  constructor
  · -- Show 0 is in the set
    use 1 / 3, 1 / 3, 1 / 3
    norm_num
  · -- Show 0 is the least
    intro f hf
    rcases hf with ⟨x, y, z, hx, hy, hz, hxyz, hf⟩
    have h1 : (3 * x ^ 2 - x) / (1 + x ^ 2) + (3 * y ^ 2 - y) / (1 + y ^ 2) + (3 * z ^ 2 - z) / (1 + z ^ 2) ≥ 0 := by 
      have h2 : 0 < x * y * z := by
        apply mul_pos
        apply mul_pos
        all_goals linarith
      have h3 : (3 * x ^ 2 - x) / (1 + x ^ 2) + (3 * y ^ 2 - y) / (1 + y ^ 2) + (3 * z ^ 2 - z) / (1 + z ^ 2) = 
          ( (3 * x ^ 2 - x) * (1 + y^2) * (1 + z^2) + (3 * y ^ 2 - y) * (1 + x^2) * (1 + z^2) + (3 * z ^ 2 - z) * (1 + x^2) * (1 + y^2) ) / ( (1 + x^2) * (1 + y^2) * (1 + z^2) ) := by
        field_simp
        <;> ring
      rw [h3]
      apply div_nonneg
      nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg (z - 1 / 3), 
                sq_nonneg (x * y - 1 / 9), sq_nonneg (x * z - 1 / 9), sq_nonneg (y * z - 1 / 9), 
                sq_nonneg (x * y * z - 1 / 27), hxyz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      positivity
    have hf' : f = (3 * x ^ 2 - x) / (1 + x ^ 2) + (3 * y ^ 2 - y) / (1 + y ^ 2) + (3 * z ^ 2 - z) / (1 + z ^ 2) := by
      linarith [hf]
    linarith [hf', h1]