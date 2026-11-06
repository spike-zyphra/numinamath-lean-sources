import Mathlib

theorem algebra_159217 {f : ℝ → ℝ} (h : ∀ x x0, f (x - x0) = f x + f x0 - 2 * x * x0 + 1) :
    ∀ x, f x = x ^ 2 - 1 := by
  have h0 : f 0 = -1 := by
    specialize h 0 0
    simp at h
    linarith

  intro x
  have eq1 := h x x
  simp at eq1
  rw [h0] at eq1

  linarith