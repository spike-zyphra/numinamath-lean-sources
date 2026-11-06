import Mathlib

theorem algebra_20815 : IsLeast {x | ∃ a b c d e f : ℤ, x = 1 + 2 + 3 - (4 + 5) + 6 ∨ x = 1 + 2 + 3 - 4 + (5 + 6) ∨ x = 1 + 2 + 3 - 4 - 5 + 6 ∨ x = 1 + 2 + 3 - 4 - 5 - 6 ∨ x = 1 + 2 + 3 + (4 + 5) + 6 ∨ x = 1 + 2 + 3 + 4 + (5 + 6) ∨ x = 1 + 2 + 3 + 4 - 5 + 6 ∨ x = 1 + 2 + 3 + 4 - 5 - 6} (-9) := by
  constructor
  · -- Show that -9 is in the set
    exact ⟨0, 0, 0, 0, 0, 0, Or.inr (Or.inr (Or.inr (Or.inl (by norm_num))))⟩
  · -- Show that -9 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, c, d, e, f, h⟩
    rcases h with (h | h | h | h | h | h | h | h) <;> omega