import Mathlib

theorem inequalities_154930 (a b c d p q : ℝ) (h₀ : a * b + c * d = 2 * p * q)
    (h₁ : 0 < p ^ 2) (h₂ : p ^ 2 ≤ a * c) :
    b * d ≤ q ^ 2 := by
        nlinarith [sq_nonneg (a * b - c * d), 
          sq_nonneg (a * d - b * c), 
          sq_nonneg (a * q - c * p), 
          sq_nonneg (b * p - d * q),
          h₀, h₁, h₂, 
          mul_self_nonneg (a - c), 
          mul_self_nonneg (b - d), 
          mul_self_nonneg (p - q)]