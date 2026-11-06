import Mathlib

theorem algebra_266521 {x y : ℝ} (h : ∃ a b c, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
    a * (-1) ^ 2 + b * (-1) + c = 1 ∧ 5 * a + 2 * b - 6 = 0 ∧ a * 1 ^ 2 + b * 1 + c = 0) :
    x ^ 2 + x + 2 * y - 2 = 0 := by 
  rcases h with ⟨a, b, c, ha, hb, hc, h1, h2, h3⟩
  have eq1 : a = 2 := by
    linarith 
  have eq2 : b = -3 := by
    linarith
  have eq3 : c = 0 := by
    linarith 
  nlinarith