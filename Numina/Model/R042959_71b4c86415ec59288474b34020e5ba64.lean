import Mathlib

theorem algebra_151 (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (8 * x) * Real.sqrt (10 * x) * Real.sqrt (3 * x) * Real.sqrt (15 * x) = 15 ↔ x = 1 / 2 := by
  constructor
  · -- Assume the equation holds, prove x = 1/2
    intro h
    have h1 : Real.sqrt (8 * x) * Real.sqrt (10 * x) * Real.sqrt (3 * x) * Real.sqrt (15 * x) = Real.sqrt ((8 * x) * (10 * x) * (3 * x) * (15 * x)) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    rw [h1] at h
    have h2 : (8 * x) * (10 * x) * (3 * x) * (15 * x) = (3600 * (x ^ 4 : ℝ)) := by
      ring_nf
    have h3 : Real.sqrt ((8 * x) * (10 * x) * (3 * x) * (15 * x)) = 60 * (x ^ 2) := by
      rw [h2]
      have h5 : Real.sqrt (3600 * (x ^ 4 : ℝ)) = Real.sqrt (3600 : ℝ) * Real.sqrt ((x ^ 4 : ℝ)) := by
        rw [← Real.sqrt_mul (by positivity)]
        all_goals ring_nf
        all_goals positivity
      have h6 : Real.sqrt (3600 : ℝ) = (60 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h7 : Real.sqrt ((x ^ 4 : ℝ)) = (x ^ 2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [sq_nonneg x]
        all_goals positivity
      rw [h5, h6, h7]
      all_goals nlinarith
    rw [h3] at h
    have h8 : x ^ 2 = (1 / 4 : ℝ) := by
      nlinarith
    have h9 : x = (1 / 2 : ℝ) := by
      nlinarith [sq_nonneg x, h8, hx]
    assumption
  · -- Assume x = 1/2, prove the equation holds
    intro h
    rw [h]
    have h1 : Real.sqrt (8 * (1 / 2 : ℝ)) * Real.sqrt (10 * (1 / 2 : ℝ)) * Real.sqrt (3 * (1 / 2 : ℝ)) * Real.sqrt (15 * (1 / 2 : ℝ)) = Real.sqrt ((8 * (1 / 2 : ℝ)) * (10 * (1 / 2 : ℝ)) * (3 * (1 / 2 : ℝ)) * (15 * (1 / 2 : ℝ))) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    rw [h1]
    have h2 : (8 * (1 / 2 : ℝ)) * (10 * (1 / 2 : ℝ)) * (3 * (1 / 2 : ℝ)) * (15 * (1 / 2 : ℝ)) = (225 : ℝ) := by
      norm_num
    rw [h2]
    have h3 : Real.sqrt (225 : ℝ) = (15 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      all_goals linarith
    rw [h3]
    all_goals norm_num