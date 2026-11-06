import Mathlib

theorem algebra_278637 (mom lele : ℕ) (h₀ : mom = lele + 24) :
    ¬∃ x, x > 0 ∧ mom + x = 6 * (lele + x) := by
  rintro ⟨x, hx, h⟩
  rw [h₀] at h
  omega