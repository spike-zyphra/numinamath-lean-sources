import Mathlib

theorem algebra_304958 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : ∃ x : ℝ, x^2 + a * x + 2 * b = 0) (h2 : ∃ x : ℝ, x^2 + 2 * b * x + a = 0) :
    a + b ≥ 6 := by 
  rcases h1 with ⟨x1, hx1⟩
  have h1' : a^2 ≥ 8 * b := by
    nlinarith [sq_nonneg (x1 + a / 2)]
  
  rcases h2 with ⟨x2, hx2⟩
  have h2' : b^2 ≥ a := by
    nlinarith [sq_nonneg (x2 + b)]
  
  nlinarith [sq_nonneg (a - 4), sq_nonneg (b - 2),
          mul_pos ha hb, h1', h2']