import Mathlib

theorem algebra_96387 (h : ∃ x, x ∈ Set.Ioo 10 11 ∧ (x * 6) % 11 = (10 * 3) % 11) :
    x = 15 := by 
  rcases h with ⟨x, hx, h2⟩
  rcases hx with ⟨h3, h4⟩
  omega