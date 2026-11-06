import Mathlib

theorem algebra_274165 (h : ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ x = y + 358 ∧ y = z - 5000 ∧ z - 397 = x) :
    x = 4206 := by
  rcases h with ⟨x, y, z, hx, hy, hz, h1, h2, h3⟩
  omega