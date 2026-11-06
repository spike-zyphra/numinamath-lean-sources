import Mathlib

theorem algebra_11269 (θ : Real) (h₀ : Real.sin θ + Real.cos θ = 7 / 5) (h₁ : Real.tan θ < 1) :
    Real.sin θ = 3 / 5 := by
  have h2 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h3 : Real.cos θ = 7 / 5 - Real.sin θ := by
    linarith [h₀]
  rw [h3] at h2
  have h4 : 25 * (Real.sin θ) ^ 2 - 35 * (Real.sin θ) + 12 = 0 := by
    nlinarith
  have h5 : (Real.sin θ - 4 / 5) * (Real.sin θ - 3 / 5) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case $\sin \theta = 4/5$
    have h8 : Real.sin θ = 4 / 5 := by
      linarith
    have h9 : Real.cos θ = 3 / 5 := by
      linarith [h₀, h8]
    have h10 : Real.tan θ = 4 / 3 := by
      rw [Real.tan_eq_sin_div_cos]
      rw [h8, h9]
      all_goals norm_num
    linarith [h10, h₁]
  · -- Case $\sin \theta = 3/5$
    linarith