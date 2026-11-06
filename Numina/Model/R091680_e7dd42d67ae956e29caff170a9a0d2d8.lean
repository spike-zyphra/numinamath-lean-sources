import Mathlib

theorem algebra_300245 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : ∃ x : ℝ, x^2 + a * x + 2 * b = 0) (h2 : ∃ y : ℝ, y^2 + 2 * b * y + a = 0) :
    a^2 + b^2 ≥ 20 := by
  rcases h1 with ⟨x, hx⟩
  have h11 : a^2 - 8 * b ≥ 0 := by
    nlinarith [sq_nonneg (x + a / 2)]
  rcases h2 with ⟨y, hy⟩
  have h22 : 4 * b^2 - 4 * a ≥ 0 := by
    nlinarith [sq_nonneg (y + b)]
  have h12 : a^2 ≥ 8 * b := by linarith
  have h23 : b^2 ≥ a := by nlinarith
  nlinarith [sq_nonneg (a - 4), sq_nonneg (b - 2),
            h11, h23, mul_pos ha hb
            ]