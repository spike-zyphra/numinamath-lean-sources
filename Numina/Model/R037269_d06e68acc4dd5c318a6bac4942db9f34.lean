import Mathlib

theorem inequalities_285163 (t : ℝ) :
    -5 ≤ 4 * Real.sin t + Real.cos (2 * t) ∧ 4 * Real.sin t + Real.cos (2 * t) ≤ 3 := by
  have h1 : Real.cos (2 * t) = 1 - 2 * Real.sin t ^ 2 := by 
    rw [Real.cos_two_mul, Real.sin_sq]
    ring
  constructor
  · -- Prove the left inequality: -5 ≤ 4 * sin t + cos (2 * t)
    rw [h1]
    nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.sin t + 1), sq_nonneg (Real.sin t - 1), Real.sin_sq_le_one t]
  · -- Prove the right inequality: 4 * sin t + cos (2 * t) ≤ 3
    rw [h1]
    nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.sin t - 1), sq_nonneg (Real.sin t + 1), Real.sin_sq_le_one t]