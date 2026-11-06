import Mathlib

theorem inequalities_146718 (x y z : ℝ)
    (h₀ : 0 ≤ x) (h₁ : 0 ≤ y) (h₂ : 0 ≤ z)
    (h₃ : x + y + z = 1) :
    2 ≤ (1 - x^2)^2 + (1 - y^2)^2 + (1 - z^2)^2 ∧
    (1 - x^2)^2 + (1 - y^2)^2 + (1 - z^2)^2 ≤ (1 + x) * (1 + y) * (1 + z) := by

  have h4 : z = 1 - x - y := by
    linarith

  constructor
  · -- Prove the left inequality: 2 ≤ (1 - x^2)^2 + (1 - y^2)^2 + (1 - z^2)^2
    rw [show z = 1 - x - y by linarith]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg ((1 - x - y) - 1), 
          mul_nonneg h₀ h₁, mul_nonneg h₁ (show 0 ≤ 1 - x - y by nlinarith), 
          mul_nonneg (show 0 ≤ 1 - x - y by nlinarith) h₀]
  · -- Prove the right inequality: (1 - x^2)^2 + (1 - y^2)^2 + (1 - z^2)^2 ≤ (1 + x) * (1 + y) * (1 + z)
    rw [show z = 1 - x - y by linarith]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg ((1 - x - y) - 1), 
          mul_nonneg h₀ h₁, mul_nonneg h₁ (show 0 ≤ 1 - x - y by nlinarith), 
          mul_nonneg (show 0 ≤ 1 - x - y by nlinarith) h₀, 
          mul_nonneg (mul_nonneg h₀ h₁) (show 0 ≤ 1 - x - y by nlinarith)]