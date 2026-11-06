import Mathlib

theorem inequalities_179231 (α β γ x : ℝ) (h₀ : 0 ≤ α) (h₁ : 0 ≤ β) (h₂ : 0 ≤ γ)
    (h₃ : α * β + β * γ + γ * α + 2 * α * β * γ = 1) (h₄ : x = α + β + γ) :
    x ≥ 3 / 2 := by
  have h5 : x = α + β + γ := by linarith
  have h6 : α * β + β * γ + γ * α + 2 * α * β * γ = 1 := h₃
  have h8 : α + β + γ = x := by linarith
  have h9 : (α + β + γ) ≥ 3 / 2 := by
    nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), 
          sq_nonneg (α + β + γ - 3 / 2), 
          mul_nonneg h₀ h₁, 
          mul_nonneg h₁ h₂, 
          mul_nonneg h₂ h₀, 
          mul_nonneg (show 0 ≤ α * β by nlinarith) (show 0 ≤ γ by linarith) 
          ]
  linarith [h8, h9]