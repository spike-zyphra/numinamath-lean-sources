import Mathlib

theorem algebra_287922 (θ : ℝ) (h : Real.sin θ^3 + Real.cos θ^3 = 11 / 16) :
    Real.sin θ + Real.cos θ = 1 / 2 := by 
  have h1 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have eq1 : Real.sin θ ^ 3 + Real.cos θ ^ 3 = (Real.sin θ + Real.cos θ) * ((Real.sin θ ^ 2 + Real.cos θ ^ 2) - Real.sin θ * Real.cos θ) := by 
    ring
  rw [h1] at eq1
  have eq2 : Real.sin θ ^ 3 + Real.cos θ ^ 3 = (Real.sin θ + Real.cos θ) * (1 - Real.sin θ * Real.cos θ) := by 
    linarith [eq1]
  rw [h] at eq2
  have h2 : (Real.sin θ + Real.cos θ) ^ 2 = 1 + 2 * (Real.sin θ * Real.cos θ) := by 
    have h3 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := h1
    nlinarith [h3, sq_nonneg (Real.sin θ - Real.cos θ), sq_nonneg (Real.sin θ + Real.cos θ)]
  -- From h2, solve for Real.sin θ * Real.cos θ
  have eq3 : Real.sin θ * Real.cos θ = ((Real.sin θ + Real.cos θ) ^ 2 - 1) / 2 := by 
    linarith [h2]
  rw [eq3] at eq2
  have h3 : 8 * (Real.sin θ + Real.cos θ) ^ 3 - 24 * (Real.sin θ + Real.cos θ) + 11 = 0 := by
    nlinarith [eq2, h1, sq_nonneg (Real.sin θ - Real.cos θ), sq_nonneg (Real.sin θ + Real.cos θ)]
  have h4 : Real.sin θ + Real.cos θ = 1 / 2 := by
    have h5 : 8 * (Real.sin θ + Real.cos θ) ^ 3 - 24 * (Real.sin θ + Real.cos θ) + 11 = 0 := h3
    have h6 : (Real.sin θ + Real.cos θ - 1 / 2) * (8 * (Real.sin θ + Real.cos θ) ^ 2 + 4 * (Real.sin θ + Real.cos θ) - 22) = 0 := by
      nlinarith [h5]
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case where Real.sin θ + Real.cos θ = 1 / 2
      linarith
    · -- Case where 8 * (Real.sin θ + Real.cos θ) ^ 2 + 4 * (Real.sin θ + Real.cos θ) - 22 = 0
      nlinarith [sq_nonneg (Real.sin θ - Real.cos θ), sq_nonneg (Real.sin θ + Real.cos θ - 1 / 2), sq_nonneg (Real.sin θ + Real.cos θ + 1 / 2), sq_nonneg (Real.sin θ ^ 2 - Real.cos θ ^ 2), sq_nonneg (Real.sin θ * Real.cos θ)]
  linarith [h4]