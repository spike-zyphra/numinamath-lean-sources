import Mathlib

theorem inequalities_600898
    (a b c : ℝ)
    (h₀ : 0 ≤ a)
    (h₁ : 0 ≤ b)
    (h₂ : 0 ≤ c)
    (h₃ : a + b + c = 1) :
    (1 - a^2)^2 + (1 - b^2)^2 + (1 - c^2)^2 ≥ 2 := by 
  have h4 : c = 1 - a - b := by linarith
  rw [h4]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          sq_nonneg (a + b - (1 - a - b)), 
          mul_nonneg h₀ h₁, mul_nonneg h₁ (show 0 ≤ 1 - a - b by nlinarith), 
          mul_nonneg h₀ (show 0 ≤ 1 - a - b by nlinarith), 
          sq_nonneg (a*b - (1 - a - b)*a), sq_nonneg (a*b - (1 - a - b)*b), sq_nonneg ((1 - a - b)*a - (1 - a - b)*b)]