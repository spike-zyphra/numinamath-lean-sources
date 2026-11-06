import Mathlib

theorem inequalities_109966 (a b c d p q : ℝ) (h₀ : a * b + c * d = 2 * p * q)
    (h₁ : a * c ≥ p ^ 2) (h₂ : p ^ 2 > 0) :
    b * d ≤ q ^ 2 := by
  nlinarith [sq_nonneg (a * d - c * b), sq_nonneg (a * q - c * q), sq_nonneg (b * q - d * q),
    sq_nonneg (a * b - c * d), sq_nonneg (a * q - p * c), sq_nonneg (b * p - d * p),
    mul_self_nonneg (a - c), mul_self_nonneg (b - d), mul_self_nonneg (p - q)]