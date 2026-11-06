import Mathlib

open Real

theorem inequalities_603461 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    sqrt (x ^ 2 + x * y + y ^ 2) + sqrt (y ^ 2 + y * z + z ^ 2) +
    sqrt (z ^ 2 + z * x + x ^ 2) ≥
    sqrt 3 * (x + y + z) := by
  have h1 : sqrt (x ^ 2 + x * y + y ^ 2) ≥ (sqrt 3 / 2) * (x + y) := by
    have h1 : (x ^ 2 + x * y + y ^ 2) ≥ (3 / 4) * (x + y) ^ 2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy
      ]
    have h2 : sqrt (x ^ 2 + x * y + y ^ 2) ≥ sqrt ((3 / 4) * (x + y) ^ 2) := Real.sqrt_le_sqrt h1
    have h3 : sqrt ((3 / 4) * (x + y) ^ 2) = (sqrt 3 / 2) * (x + y) := by
      have h4 : sqrt ((3 / 4) * (x + y) ^ 2) = Real.sqrt (3 / 4) * Real.sqrt ((x + y) ^ 2) := by
        rw [← Real.sqrt_mul (by positivity)]
        all_goals positivity
      have h5 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h6 : Real.sqrt ((x + y) ^ 2) = x + y := Real.sqrt_sq (by linarith)
      rw [h4, h5, h6]
      all_goals ring_nf <;> norm_num
      all_goals nlinarith
    rw [h3] at h2
    linarith
  have h2 : sqrt (y ^ 2 + y * z + z ^ 2) ≥ (sqrt 3 / 2) * (y + z) := by
    have h1 : (y ^ 2 + y * z + z ^ 2) ≥ (3 / 4) * (y + z) ^ 2 := by
      nlinarith [sq_nonneg (y - z), sq_nonneg (y + z), mul_pos hy hz
      ]
      -- Now apply square root to both sides
    have h2 : sqrt (y ^ 2 + y * z + z ^ 2) ≥ sqrt ((3 / 4) * (y + z) ^ 2) := Real.sqrt_le_sqrt h1
    have h3 : sqrt ((3 / 4) * (y + z) ^ 2) = (sqrt 3 / 2) * (y + z) := by
      have h4 : sqrt ((3 / 4) * (y + z) ^ 2) = Real.sqrt (3 / 4) * Real.sqrt ((y + z) ^ 2) := by
        rw [← Real.sqrt_mul (by positivity)]
        all_goals positivity
      have h5 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h6 : Real.sqrt ((y + z) ^ 2) = y + z := Real.sqrt_sq (by linarith)
      rw [h4, h5, h6]
      all_goals ring_nf <;> norm_num
      all_goals nlinarith
    rw [h3] at h2
    linarith
  have h3 : sqrt (z ^ 2 + z * x + x ^ 2) ≥ (sqrt 3 / 2) * (z + x) := by
    have h1 : (z ^ 2 + z * x + x ^ 2) ≥ (3 / 4) * (z + x) ^ 2 := by
      nlinarith [sq_nonneg (z - x), sq_nonneg (z + x), mul_pos hz hx
      ]
      -- Now apply square root to both sides
    have h2 : sqrt (z ^ 2 + z * x + x ^ 2) ≥ sqrt ((3 / 4) * (z + x) ^ 2) := Real.sqrt_le_sqrt h1
    have h3 : sqrt ((3 / 4) * (z + x) ^ 2) = (sqrt 3 / 2) * (z + x) := by
      have h4 : sqrt ((3 / 4) * (z + x) ^ 2) = Real.sqrt (3 / 4) * Real.sqrt ((z + x) ^ 2) := by
        rw [← Real.sqrt_mul (by positivity)]
        all_goals positivity
      have h5 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h6 : Real.sqrt ((z + x) ^ 2) = z + x := Real.sqrt_sq (by linarith)
      rw [h4, h5, h6]
      all_goals ring_nf <;> norm_num
      all_goals nlinarith
    rw [h3] at h2
    linarith
  -- Now, summing up these inequalities:
  linarith [h1, h2, h3]