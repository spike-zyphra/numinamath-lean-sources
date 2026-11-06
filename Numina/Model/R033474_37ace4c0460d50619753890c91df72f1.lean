import Mathlib

theorem algebra_281219 (α β γ : ℝ) (h : α + β + γ = Real.pi) :
    Real.sin α ^ 2 + Real.sin β ^ 2 - Real.sin γ ^ 2 = 2 * Real.sin α * Real.sin β * Real.cos γ ∧
    Real.cos α ^ 2 + Real.cos β ^ 2 - Real.cos γ ^ 2 = 1 - 2 * Real.sin α * Real.sin β * Real.cos γ := by
  have h1 : γ = Real.pi - (α + β) := by linarith
  have h2 : Real.sin γ = Real.sin (α + β) := by
    rw [h1]
    have h3 : Real.sin (Real.pi - (α + β)) = Real.sin (α + β) := by
      rw [Real.sin_pi_sub]
    linarith
  have h3 : Real.cos γ = - Real.cos (α + β) := by 
    rw [h1]
    have h4 : Real.cos (Real.pi - (α + β)) = - Real.cos (α + β) := by 
      rw [Real.cos_pi_sub]
    linarith
  have h4 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by 
    rw [Real.sin_add]
  have h5 : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := by
    rw [Real.cos_add]
  have h6 : Real.sin γ = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by 
    rw [h2, h4]
  have h7 : Real.cos γ = - (Real.cos α * Real.cos β - Real.sin α * Real.sin β) := by 
    rw [h3, h5]
    all_goals ring
  constructor 
  · -- Prove the first identity
    rw [h6, h7]
    nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq (α + β), 
          sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.cos α - Real.cos β), 
          Real.sin_sq_add_cos_sq (α + β), 
          sq_nonneg (Real.sin α * Real.sin β), sq_nonneg (Real.cos α * Real.cos β),
          sq_nonneg (Real.sin α * Real.cos β), sq_nonneg (Real.cos α * Real.sin β)
        ]
  · -- Prove the second identity
    rw [h7]
    nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq (α + β), 
          sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.cos α - Real.cos β), 
          Real.sin_sq_add_cos_sq (α + β), 
          sq_nonneg (Real.sin α * Real.sin β), sq_nonneg (Real.cos α * Real.cos β),
          sq_nonneg (Real.sin α * Real.cos β), sq_nonneg (Real.cos α * Real.sin β)
        ]