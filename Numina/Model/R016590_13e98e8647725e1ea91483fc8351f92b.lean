import Mathlib

open Real

theorem inequalities_259818 (α : ℝ) (hα : α > 0) :
    IsGreatest {C | ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x * y + y * z + z * x = α →
      (1 + α / x ^ 2) * (1 + α / y ^ 2) * (1 + α / z ^ 2) ≥ C * (x / z + z / x + 2)} 16 := by
  constructor
  · -- Show that 16 is in the set.
    intro x y z hx hy hz h
    have h1 : (1 + α / x ^ 2) * (1 + α / y ^ 2) * (1 + α / z ^ 2) ≥ 16 * (x / z + z / x + 2) := by
      have h2 : 0 < x * y * z := by
        positivity
      have h3 : 0 < x ^ 2 * y ^ 2 * z ^ 2 := by
        positivity
      have h4 : (1 + α / x ^ 2) * (1 + α / y ^ 2) * (1 + α / z ^ 2) - 16 * (x / z + z / x + 2) ≥ 0 := by
        have h5 : (1 + α / x ^ 2) * (1 + α / y ^ 2) * (1 + α / z ^ 2) - 16 * (x / z + z / x + 2) =
            ((x ^ 2 + α) * (y ^ 2 + α) * (z ^ 2 + α) - 16 * (x ^ 3 * y ^ 2 * z + x * y ^ 2 * z ^ 3 + 2 * x ^ 2 * y ^ 2 * z ^ 2)) / (x ^ 2 * y ^ 2 * z ^ 2) := by
          field_simp
          ring
        rw [h5]
        have h7 : (x ^ 2 + α) * (y ^ 2 + α) * (z ^ 2 + α) ≥ 16 * (x ^ 3 * y ^ 2 * z + x * y ^ 2 * z ^ 3 + 2 * x ^ 2 * y ^ 2 * z ^ 2) := by
          have h8 : α = x * y + y * z + z * x := by linarith
          rw [h8]
          nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
            sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
            mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_pos (mul_pos hx hy) hz
          ]
        have h6 : ((x ^ 2 + α) * (y ^ 2 + α) * (z ^ 2 + α) - 16 * (x ^ 3 * y ^ 2 * z + x * y ^ 2 * z ^ 3 + 2 * x ^ 2 * y ^ 2 * z ^ 2)) ≥ 0 := by linarith
        have h7 : ((x ^ 2 + α) * (y ^ 2 + α) * (z ^ 2 + α) - 16 * (x ^ 3 * y ^ 2 * z + x * y ^ 2 * z ^ 3 + 2 * x ^ 2 * y ^ 2 * z ^ 2)) / (x ^ 2 * y ^ 2 * z ^ 2) ≥ 0 := by
          apply div_nonneg
          all_goals linarith
        linarith
      linarith
    linarith
  · -- Show that 16 is greatest
    intro C hC
    have h1 := hC (Real.sqrt (α / 3)) (Real.sqrt (α / 3)) (Real.sqrt (α / 3)) (by positivity) (by positivity) (by positivity) (by
      have h1 : Real.sqrt (α / 3) * Real.sqrt (α / 3) + Real.sqrt (α / 3) * Real.sqrt (α / 3) + Real.sqrt (α / 3) * Real.sqrt (α / 3) = α := by
        have h2 : Real.sqrt (α / 3) ^ 2 = α / 3 := by
          rw [Real.sq_sqrt]
          positivity
        linarith
      linarith
    )
    have h3 : (1 + α / (Real.sqrt (α / 3)) ^ 2) * (1 + α / (Real.sqrt (α / 3)) ^ 2) * (1 + α / (Real.sqrt (α / 3)) ^ 2) = 64 := by
      have h4 : Real.sqrt (α / 3) ^ 2 = α / 3 := by
        rw [Real.sq_sqrt]
        positivity
      rw [h4]
      field_simp
      nlinarith
    have h4 : (Real.sqrt (α / 3) / (Real.sqrt (α / 3)) + (Real.sqrt (α / 3)) / (Real.sqrt (α / 3)) + 2) = (4 : ℝ) := by
      have h11 : Real.sqrt (α / 3) / (Real.sqrt (α / 3)) = 1 := by
        field_simp [show Real.sqrt (α / 3) ≠ 0 by positivity]
      linarith
    have h5 : (1 + α / (Real.sqrt (α / 3)) ^ 2) * (1 + α / (Real.sqrt (α / 3)) ^ 2) * (1 + α / (Real.sqrt (α / 3)) ^ 2) ≥ C * (Real.sqrt (α / 3) / (Real.sqrt (α / 3)) + (Real.sqrt (α / 3)) / (Real.sqrt (α / 3)) + 2) := by
      simpa using h1
    rw [h3, h4] at h5
    nlinarith