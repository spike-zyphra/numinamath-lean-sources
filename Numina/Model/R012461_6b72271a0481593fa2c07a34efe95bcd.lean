import Mathlib

theorem algebra_311001 {a b c d : ℝ} (h₀ : a^2 + b^2 = 1) (h₁ : c^2 + d^2 = 1)
    (h₂ : a * c + b * d = 0) : a^2 + c^2 = 1 ∧ b^2 + d^2 = 1 ∧ a * b + c * d = 0 := by
  constructor
  · -- Prove that $a ^ 2 + c ^ 2 = 1$. 
    have eq3 : a ^ 2 + c ^ 2 = 1 := by
      nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (a - c), sq_nonneg (b - d)]
    tauto

  constructor 
  · -- Prove that $b ^ 2 + d ^ 2 = 1$. 
    have eq4 : b ^ 2 + d ^ 2 = 1 := by
      nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (a - c), sq_nonneg (b - d)]
    tauto

  · -- Prove that $a * b + c * d = 0$. 
    nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a + d), sq_nonneg (b + c), h₀, h₁, sq_nonneg (a * b - c * d), sq_nonneg (a * d + b * c), sq_nonneg (a * b + c * d)]