import Mathlib

theorem algebra_306488 (a b : ℕ) (ha : a > 0) (hb : b > 0)
    (h1 : ∃ x, a - x = b ∧ b - x = 10) (h2 : ∃ y, b - y = a ∧ a - y = 25) :
    a > b ∧ a - b = 5 := by
  rcases h1 with ⟨x, h1₁, h1₂⟩ 
  rcases h2 with ⟨y, h2₁, h2₂⟩
  omega