import Mathlib

theorem algebra_315272 {a b x y : ℝ} (h₀ : a^2 + b^2 = 1) (h₁ : x^2 + y^2 = 1)
    (h₂ : a * x + b * y = 0) : a^2 + x^2 = 1 ∧ b^2 + y^2 = 1 ∧ a * b + x * y = 0 := by
  constructor
  · -- Show that a ^ 2 + x ^ 2 = 1
    nlinarith [sq_nonneg (a - x), sq_nonneg (b - y), sq_nonneg (a * y - b * x)]
  constructor
  · -- Show that b ^ 2 + y ^ 2 = 1
    nlinarith [sq_nonneg (a - x), sq_nonneg (b - y), sq_nonneg (a * y - b * x)]
  · -- Show that a * b + x * y = 0
    have h3 : a ^ 2 + x ^ 2 = 1 := by
      nlinarith [sq_nonneg (a - x), sq_nonneg (b - y), sq_nonneg (a * y - b * x)]
    have h4 : b ^ 2 + y ^ 2 = 1 := by
      nlinarith [sq_nonneg (a - x), sq_nonneg (b - y), sq_nonneg (a * y - b * x)]
    nlinarith [sq_nonneg (a + x), sq_nonneg (b + y), sq_nonneg (a - b), sq_nonneg (x - y), 
      sq_nonneg (a * y - b * x), sq_nonneg (a * x + b * y), 
      h3, h4, mul_self_nonneg (a - x), mul_self_nonneg (b - y), 
      mul_self_nonneg (a + x), mul_self_nonneg (b + y)]