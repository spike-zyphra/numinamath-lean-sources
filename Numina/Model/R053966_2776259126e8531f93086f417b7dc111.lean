import Mathlib

theorem number_theory_244632 (a b c : ℤ) (h : a = 2 ∧ b = 2 ∧ c = 2) :
    ¬∃ x y z, x + y + z = 17 ∧ x - y + z = 1999 ∧ x + y - z = 2105 := by
  intro h
  rcases h with ⟨x, y, z, h1, h2, h3⟩
  omega