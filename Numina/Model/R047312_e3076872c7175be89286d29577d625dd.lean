import Mathlib

theorem algebra_11620 : Real.sqrt 54 * Real.sqrt 32 * Real.sqrt 6 = 72 * Real.sqrt 2 := by
  have h1 : Real.sqrt 54 * Real.sqrt 6 = 18 := by
    have h2 : Real.sqrt 54 * Real.sqrt 6 = Real.sqrt (54 * 6) := by
      rw [← Real.sqrt_mul (by norm_num)]
    rw [h2]
    have h3 : Real.sqrt (54 * 6) = (18 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h3]
  have h2 : Real.sqrt 32 = 4 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  calc
    Real.sqrt 54 * Real.sqrt 32 * Real.sqrt 6
        = (Real.sqrt 54 * Real.sqrt 6) * Real.sqrt 32 := by ring
    _ = (18) * Real.sqrt 32 := by rw [h1]
    _ = 18 * (4 * Real.sqrt 2) := by rw [h2]
    _ = 72 * Real.sqrt 2 := by ring