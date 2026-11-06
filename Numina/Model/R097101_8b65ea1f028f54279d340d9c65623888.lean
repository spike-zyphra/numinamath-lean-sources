import Mathlib

theorem algebra_99212 (θ : ℝ) (h : 4 * Real.sin θ * Real.cos θ - 5 * Real.sin θ - 5 * Real.cos θ - 1 = 0) :
    Real.sin θ ^ 3 + Real.cos θ ^ 3 = -11 / 16 := by
  have h1 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h5 : Real.sin θ + Real.cos θ = -1 / 2 := by
    have h2 : 2 * (Real.sin θ + Real.cos θ) ^ 2 - 5 * (Real.sin θ + Real.cos θ) - 3 = 0 := by
      nlinarith [sq_nonneg (Real.sin θ - Real.cos θ), sq_nonneg (Real.sin θ + Real.cos θ), Real.sin_sq_add_cos_sq θ, sq_nonneg (4 * Real.sin θ * Real.cos θ)]
    have h6 : (Real.sin θ + Real.cos θ - 3) * (2 * (Real.sin θ + Real.cos θ) + 1) = 0 := by
      nlinarith [sq_nonneg (Real.sin θ - Real.cos θ), sq_nonneg (Real.sin θ + Real.cos θ), Real.sin_sq_add_cos_sq θ, sq_nonneg (4 * Real.sin θ * Real.cos θ)]
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- Real.sin θ + Real.cos θ - 3 = 0
      have h9 : Real.sin θ + Real.cos θ = 3 := by linarith
      nlinarith [sq_nonneg (Real.sin θ - Real.cos θ), sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]
    · -- 2 * (Real.sin θ + Real.cos θ) + 1 = 0
      nlinarith
  have h4 : Real.sin θ * Real.cos θ = ((Real.sin θ + Real.cos θ) ^ 2 - 1) / 2 := by
    have h2 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := h1
    nlinarith
  have h3 : Real.sin θ * Real.cos θ = -3 / 8 := by
    rw [h5] at h4
    nlinarith
  have h6 : Real.sin θ ^ 3 + Real.cos θ ^ 3 = (Real.sin θ + Real.cos θ) ^ 3 - 3 * (Real.sin θ * Real.cos θ) * (Real.sin θ + Real.cos θ) := by
    ring
  rw [h6, h5, h3]
  nlinarith [h1, h4]