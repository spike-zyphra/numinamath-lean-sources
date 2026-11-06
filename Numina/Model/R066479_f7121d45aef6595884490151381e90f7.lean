import Mathlib

theorem algebra_235611
    (a b c d : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : a + b = 2 * c + 23 * d)
    (h₂ : 3 * a = 2 * b + 2 * c + 14 * d) :
    a > b := by
  have ha1 : 0 < a := h₀.left
  have hb1 : 0 < b := h₀.right.left
  have hc1 : 0 < c := h₀.right.right.left
  have hd1 : 0 < d := h₀.right.right.right
  linarith