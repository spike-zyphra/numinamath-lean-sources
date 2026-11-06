import Mathlib

theorem algebra_14282 (a b c d x y : ℝ)
(h₀ : a > b ∧ b > c ∧ c > d)
(h₁ : a + b = x ∧ a + c = y ∧ a + d = 320 ∧ b + c = 287 ∧ b + d = 189 ∧ c + d = 234) :
x + y = 791 := by
  rcases h₁ with ⟨h1, h2, h3, h4, h5, h6⟩
  linarith