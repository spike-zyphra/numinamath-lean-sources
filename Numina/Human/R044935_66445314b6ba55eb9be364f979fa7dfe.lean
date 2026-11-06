import Mathlib

/- 1. Task. Prove that if $a+b$ is a positive number, then

$$
\frac{a}{b^{2}}+\frac{b}{a^{2}} \geq \frac{1}{a}+\frac{1}{b}
$$ -/
theorem inequalities_282331 (a b : ℝ) (h₀ : a ≠ 0) (h₁ : b ≠ 0)
    (h₂ : a + b > 0) :
    a / b^2 + b / a^2 ≥ 1 / a + 1 / b := by

    -- we just need to show the difference a / b ^ 2 + b / a ^ 2 - (1 / a + 1 / b) is non-negative
    apply le_of_sub_nonneg

    -- bringing the left side to a common denominator
    have : a / b ^ 2 + b / a ^ 2 - (1 / a + 1 / b) = (a ^ 3 + b ^ 3 - a ^ 2 * b - a * b ^ 2) / (a * b) ^ 2 := by
      field_simp
      ring
    rw [this]

    -- and factoring the numerator repeatedly
    have : (a ^ 3 + b ^ 3 - a ^ 2 * b - a * b ^ 2) = (a + b) * (a - b) ^ 2 := by ring
    rw [this]

    -- we are left to show that (a + b) * (a - b) ^ 2 / (a * b) ^ 2 ≥ 0 
    apply div_nonneg
    · apply mul_nonneg  -- show the numerator is non-negative
      · linarith
      apply sq_nonneg
    apply sq_nonneg -- show the denominator is non-negative
