import Mathlib

theorem inequalities_56137
    (a b x y : ℝ)
    (h₀ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ x ∧ 0 ≤ y)
    (h₁ : a^5 + b^5 ≤ 1)
    (h₂ : x^5 + y^5 ≤ 1) :
    a^2 * x^3 + b^2 * y^3 ≤ 1 := by 
  rcases h₀ with ⟨ha, hb, hx, hy⟩
  nlinarith [sq_nonneg (a^2 - a * x), sq_nonneg (b^2 - b * y), sq_nonneg (x^2 - a * x), sq_nonneg (y^2 - b * y), sq_nonneg (a - x), sq_nonneg (b - y), sq_nonneg (a^2 - x^2), sq_nonneg (b^2 - y^2), sq_nonneg (a * x - b * y), mul_nonneg ha hb, mul_nonneg ha hx, mul_nonneg ha hy, mul_nonneg hb hx, mul_nonneg hb hy, mul_nonneg hx hy, mul_nonneg (show (0:ℝ) ≤ a^2 by positivity) (show (0:ℝ) ≤ x^2 by positivity), mul_nonneg (show (0:ℝ) ≤ b^2 by positivity) (show (0:ℝ) ≤ y^2 by positivity), sq_nonneg (a * x), sq_nonneg (b * y), sq_nonneg (a^2 - b^2), sq_nonneg (x^2 - y^2)]