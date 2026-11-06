import Mathlib

theorem calculus_16912 (x y : ℝ) :
    Real.cos x ^ 2 + Real.cos (x + y) ^ 2 - 2 * Real.cos x * Real.cos y * Real.cos (x + y) =
    Real.sin y ^ 2 := by
  have h1 : Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y := by 
    rw [Real.cos_add]
  rw [h1]
  have h2 : Real.cos x ^ 2 + (Real.cos x * Real.cos y - Real.sin x * Real.sin y) ^ 2 - 2 * Real.cos x * Real.cos y * (Real.cos x * Real.cos y - Real.sin x * Real.sin y) =
    Real.sin y ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq x, Real.cos_sq_add_sin_sq y, sq_nonneg (Real.sin x * Real.sin y), sq_nonneg (Real.cos x * Real.sin y), sq_nonneg (Real.sin x * Real.cos y), sq_nonneg (Real.cos x - Real.cos y), sq_nonneg (Real.sin x - Real.sin y), sq_nonneg (Real.cos x * Real.sin y - Real.sin x * Real.cos y)]
  linarith [h2]