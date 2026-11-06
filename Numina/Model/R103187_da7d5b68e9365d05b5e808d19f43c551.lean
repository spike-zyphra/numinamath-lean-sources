import Mathlib

theorem inequalities_600322 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) ≤ 3 := by
  have h1 : 0 < 2 * x + y + z := by
    positivity
  have h2 : 0 < x + 2 * y + z := by
    positivity
  have h3 : 0 < x + y + 2 * z := by
    positivity

  have h4 : x / (2 * x + y + z) = (x * (x + 2 * y + z) * (x + y + 2 * z)) / ((2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) := by
    field_simp [h1]
    all_goals ring

  have h5 : y / (x + 2 * y + z) = (y * (2 * x + y + z) * (x + y + 2 * z)) / ((2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) := by
    field_simp [h2]
    all_goals ring

  have h6 : z / (x + y + 2 * z) = (z * (2 * x + y + z) * (x + 2 * y + z)) / ((2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) := by
    field_simp [h3]
    all_goals ring

  calc
    x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) = (x * (x + 2 * y + z) * (x + y + 2 * z) + y * (2 * x + y + z) * (x + y + 2 * z) + z * (2 * x + y + z) * (x + 2 * y + z)) / ((2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) := by
      rw [h4, h5, h6]
      ring
    _ ≤ 3 := by
      -- Multiply denominators to bring fractions to a common denominator and clear denominators
      have h7 : (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z) > 0 := by positivity
      apply (div_le_iff₀ h7).mpr
      -- Then solve the resulting polynomial inequality
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg ((x + y + z) ), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]