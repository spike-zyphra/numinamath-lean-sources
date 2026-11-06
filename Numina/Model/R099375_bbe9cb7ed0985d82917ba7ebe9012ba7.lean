import Mathlib

theorem algebra_218928 (h : ∃ x y, x > 0 ∧ y > 0 ∧ x * 5 = y * 6 + 90 ∧ x * 3 = y * 2) :
    y * 6 = 360 := by 
  rcases h with ⟨x, y, hx, hy, h1, h2⟩
  nlinarith