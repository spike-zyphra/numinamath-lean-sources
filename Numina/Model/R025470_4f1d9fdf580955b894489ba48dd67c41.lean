import Mathlib

open Real

theorem algebra_9601 {f : ℝ → ℝ} (hf : ∀ x, f x = sqrt (1 - (x - 2022)^2) + 2023)
    (x₁ x₂ : ℝ) (hx₁ : 2022 < x₁) (hx₂ : x₁ < x₂) (hx₂' : x₂ < 2023) :
    x₁ * f x₂ < x₂ * f x₁ := by
  have hfx₁ : f x₁ = sqrt (1 - (x₁ - 2022)^2) + 2023 := hf x₁
  have hfx₂ : f x₂ = sqrt (1 - (x₂ - 2022)^2) + 2023 := hf x₂
  rw [hfx₁, hfx₂]
  have h1 : 0 < x₁ - 2022 := by linarith
  have h2 : x₁ - 2022 < x₂ - 2022 := by linarith
  have h3 : x₂ - 2022 < 1 := by linarith
  have h4 : 0 < x₂ - 2022 := by linarith
  have h5 : 0 ≤ sqrt (1 - (x₁ - 2022)^2) := Real.sqrt_nonneg (1 - (x₁ - 2022)^2)
  have h6 : 0 ≤ sqrt (1 - (x₂ - 2022)^2) := Real.sqrt_nonneg (1 - (x₂ - 2022)^2)
  have h7 : sqrt (1 - (x₂ - 2022)^2) < sqrt (1 - (x₁ - 2022)^2) := by
    apply Real.sqrt_lt_sqrt
    · -- Show that 1 - (x₂ - 2022)^2 ≥ 0
      nlinarith [sq_nonneg (x₂ - 2022), Real.sqrt_nonneg (1 - (x₂ - 2022) ^ 2)]
    · -- Show that 1 - (x₂ - 2022)^2 < 1 - (x₁ - 2022)^2
      nlinarith [sq_nonneg (x₁ - 2022), sq_nonneg (x₂ - 2022), sq_pos_of_pos (show 0 < x₂ - x₁ by linarith), sq_nonneg (x₂ - x₁)]
  nlinarith [sq_nonneg (x₁ * sqrt (1 - (x₂ - 2022) ^ 2) - x₂ * sqrt (1 - (x₁ - 2022) ^ 2)), 
          sq_nonneg (sqrt (1 - (x₂ - 2022) ^ 2) - sqrt (1 - (x₁ - 2022) ^ 2)), 
          Real.sqrt_nonneg (1 - (x₁ - 2022) ^ 2), 
          Real.sqrt_nonneg (1 - (x₂ - 2022) ^ 2), 
          Real.sq_sqrt (show 0 ≤ (1 - (x₁ - 2022) ^ 2 : ℝ) by nlinarith [sq_nonneg (x₁ - 2022), sq_nonneg (x₂ - 2022)]), 
          Real.sq_sqrt (show 0 ≤ (1 - (x₂ - 2022) ^ 2 : ℝ) by nlinarith [sq_nonneg (x₁ - 2022), sq_nonneg (x₂ - 2022)]), 
          mul_pos (show 0 < x₁ - 2022 by linarith) (show 0 < x₂ - x₁ by linarith), 
          mul_pos (show 0 < x₂ - x₁ by linarith) (show 0 < 2023 - x₂ by linarith)
      ]