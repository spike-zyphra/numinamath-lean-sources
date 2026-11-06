import Mathlib

theorem algebra_227024 {f : ℝ → ℝ} (h : ∀ x, f x - f (2 - x) = 0) :
    ∃ a, ∀ x, f x = f (2 * a - x) := by
  use 1
  intro x
  have h1 : f x = f (2 - x) := by 
    have h_eq : f x - f (2 - x) = 0 := h x
    linarith 
  rw [show 2 * (1 : ℝ) - x = (2 - x) by ring]
  exact h1