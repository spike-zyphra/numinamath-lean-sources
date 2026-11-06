import Mathlib

theorem algebra_51 {x y : ℝ} (h : abs (x + y) = y - x) :
    x = 0 ∧ y ≥ 0 ∨ y = 0 ∧ x ≤ 0 := by
  by_cases h1 : x + y ≥ 0
  · -- Case 1: x + y ≥ 0, so abs (x + y) = x + y
    rw [abs_of_nonneg h1] at h
    have hx : x = 0 := by linarith
    have hy : y ≥ 0 := by linarith
    left
    exact ⟨hx, hy⟩
  · -- Case 2: x + y < 0, so abs (x + y) = -(x + y)
    rw [abs_of_neg (lt_of_not_ge h1)] at h
    have hy : y = 0 := by linarith
    have hx : x ≤ 0 := by linarith
    right
    exact ⟨hy, hx⟩