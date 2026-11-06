import Mathlib

theorem inequalities_600661
    (a b c d : ℝ)
    (h₀ : 0 ≤ a)
    (h₁ : 0 ≤ b)
    (h₂ : 0 ≤ c)
    (h₃ : 0 ≤ d)
    (h₄ : a + b + c + d = 4) :
    b * c * d + c * d * a + d * a * b + a * b * c - a * b * c * d ≤
    (1 / 2) * (a * b + a * c + a * d + b * c + b * d + c * d) := by

  have h5 : d = 4 - a - b - c := by 
    linarith

  rw [show d = 4 - a - b - c by linarith]

  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - (4 - a - b - c)), 
          sq_nonneg (b - c), sq_nonneg (b - (4 - a - b - c)), sq_nonneg (c - (4 - a - b - c)), 
          mul_nonneg h₀ h₁, mul_nonneg h₀ h₂, mul_nonneg h₀ (show 0 ≤ (4 - a - b - c) by nlinarith), 
          mul_nonneg h₁ h₂, mul_nonneg h₁ (show 0 ≤ (4 - a - b - c) by nlinarith), 
          mul_nonneg h₂ (show 0 ≤ (4 - a - b - c) by nlinarith)
        ]