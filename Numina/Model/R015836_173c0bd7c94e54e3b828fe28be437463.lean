import Mathlib

theorem calculus_22893 (x y : ℝ) (t : ℝ)
    (h : x = 8 + 2 * t ∧ y = -1 + 3 * t) :
    y = (3 / 2) * x - 13 := by
  rcases h with ⟨hx, hy⟩
  have ht : t = (x - 8) / 2 := by
    linarith
  rw [ht] at hy
  linarith