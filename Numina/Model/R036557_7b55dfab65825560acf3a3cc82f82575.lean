import Mathlib

theorem inequalities_50
    (a b c : ℝ)
    (h₀ : 0 ≤ a)
    (h₁ : 0 ≤ b)
    (h₂ : 0 ≤ c)
    (h₃ : a + b + c = 3) :
    (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) ≥ (a + 1) * (b + 1) * (c + 1) := by
  have h4 : c = 3 - a - b := by linarith
  rw [h4]
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * (3 - a - b) - 1), sq_nonneg (b * (3 - a - b) - 1),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((3 - a - b) - 1),
          sq_nonneg (a * b * (3 - a - b) - 1), sq_nonneg (a * b + b * (3 - a - b) + a * (3 - a - b) - 3),
          mul_nonneg h₀ h₁, mul_nonneg h₁ (show 0 ≤ 3 - a - b by nlinarith [h₀, h₁, show (0:ℝ) ≤ a + b by linarith [h₀, h₁]]), 
          mul_nonneg (show 0 ≤ 3 - a - b by nlinarith [h₀, h₁, show (0:ℝ) ≤ a + b by linarith [h₀, h₁]]) h₀, 
          mul_nonneg (show 0 ≤ 3 - a - b by nlinarith [h₀, h₁, show (0:ℝ) ≤ a + b by linarith [h₀, h₁]]) h₁
]