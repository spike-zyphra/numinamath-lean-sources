import Mathlib

theorem algebra_10856 {x y z : ℝ} (h₀ : y + z = 13) (h₁ : z + x = 14) (h₂ : x + y = 15) :
    Real.sqrt (x * y * z * (x + y + z)) = 84 := by
  have h3 : x + y + z = 21 := by
    linarith
  have hx : x = 8 := by
    linarith [h₀, h3]
  have hy : y = 7 := by
    linarith [h₁, h3]
  have hz : z = 6 := by
    linarith [h₂, h3]
  rw [hx, hy, hz]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num