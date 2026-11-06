import Mathlib

theorem algebra_16359 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hroots : ∃ x : ℝ, x^2 + a * x + 2 * b = 0 ∧ ∃ x : ℝ, x^2 + 2 * b * x + a = 0) :
    a + b ≥ 6 := by
  rcases hroots with ⟨x, hx1, ⟨y, hy1⟩⟩

  have h1 : a ^ 2 ≥ 8 * b := by
    nlinarith [sq_nonneg (x + a / 2)]
  
  have h2 : b ^ 2 ≥ a := by 
    nlinarith [sq_nonneg (y + 2 * b / 2)]
  
  nlinarith [sq_nonneg (a - 4), sq_nonneg (b - 2),
          mul_pos ha hb
        ]