import Mathlib

theorem algebra_314769 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : ∃ x y, x^2 + a * x + 2 * b = 0 ∧ y^2 + 2 * b * y + a = 0) :
    a + b ≥ 6 := by 
  rcases h1 with ⟨x, y, hx, hy⟩
  have h2 : a ^ 2 - 8 * b ≥ 0 := by 
    nlinarith [sq_nonneg (x + a / 2)]
  have h3 : b ^ 2 - a ≥ 0 := by 
    nlinarith [sq_nonneg (y + b)]
  nlinarith [sq_nonneg (a - 4), sq_nonneg (b - 2), mul_pos ha hb]