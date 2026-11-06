import Mathlib

theorem algebra_6628 (α β γ : ℝ) (h₀ : α + β + γ = 9) (h₁ : α^2 + β^2 + γ^2 = 29) (h₂ : α^3 + β^3 + γ^3 = 99) :
    α^4 + β^4 + γ^4 = 353 := by
  have h₃ : α * β + β * γ + γ * α = 26 := by
    have h : α ^ 2 + β ^ 2 + γ ^ 2 = (α + β + γ) ^ 2 - 2 * (α * β + β * γ + γ * α) := by ring
    rw [h₀] at h
    linarith

  have h₄ : α * β * γ = 24 := by
    have h : α ^ 3 + β ^ 3 + γ ^ 3 = (α + β + γ) ^ 3 - 3 * (α + β + γ) * (α * β + β * γ + γ * α) + 3 * (α * β * γ) := by ring
    rw [h₀, h₃] at h
    linarith

  have h₅ : α ^ 3 = 9 * α ^ 2 - 26 * α + 24 := by
    nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), h₀, h₁, h₂]

  have h₆ : β ^ 3 = 9 * β ^ 2 - 26 * β + 24 := by
    nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), h₀, h₁, h₂]

  have h₇ : γ ^ 3 = 9 * γ ^ 2 - 26 * γ + 24 := by
    nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), h₀, h₁, h₂]

  have h₈ : α ^ 4 = 55 * α ^ 2 - 210 * α + 216 := by
    calc
      α ^ 4 = α * α ^ 3 := by ring
      _ = α * (9 * α ^ 2 - 26 * α + 24) := by rw [h₅]
      _ = 9 * α ^ 3 - 26 * α ^ 2 + 24 * α := by ring
      _ = 9 * (9 * α ^ 2 - 26 * α + 24) - 26 * α ^ 2 + 24 * α := by rw [h₅]
      _ = 55 * α ^ 2 - 210 * α + 216 := by ring

  have h₉ : β ^ 4 = 55 * β ^ 2 - 210 * β + 216 := by
    calc
      β ^ 4 = β * β ^ 3 := by ring
      _ = β * (9 * β ^ 2 - 26 * β + 24) := by rw [h₆]
      _ = 9 * β ^ 3 - 26 * β ^ 2 + 24 * β := by ring
      _ = 9 * (9 * β ^ 2 - 26 * β + 24) - 26 * β ^ 2 + 24 * β := by rw [h₆]
      _ = 55 * β ^ 2 - 210 * β + 216 := by ring

  have h₁₀ : γ ^ 4 = 55 * γ ^ 2 - 210 * γ + 216 := by
    calc
      γ ^ 4 = γ * γ ^ 3 := by ring
      _ = γ * (9 * γ ^ 2 - 26 * γ + 24) := by rw [h₇]
      _ = 9 * γ ^ 3 - 26 * γ ^ 2 + 24 * γ := by ring
      _ = 9 * (9 * γ ^ 2 - 26 * γ + 24) - 26 * γ ^ 2 + 24 * γ := by rw [h₇]
      _ = 55 * γ ^ 2 - 210 * γ + 216 := by ring

  nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), h₀, h₁, h₂, h₈, h₉, h₁₀]