import Mathlib

theorem inequalities_44805 (x y z : ℝ) :
    ¬(x^2 + y + 1 / 4 < 0 ∧ y^2 + z + 1 / 4 < 0 ∧ z^2 + x + 1 / 4 < 0) := by
  intro h
  rcases h with ⟨h₁, h₂, h₃⟩
  nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (z + 1 / 2),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]