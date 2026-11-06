import Mathlib

theorem algebra_288604 (f : ℝ → ℝ) (hf : f = fun x => x^3 - x^2 + 1) :
    ∀ x, x > 0 → f x ≥ 0 ∧ x < 0 → f x ≤ 0 := by
  intro x hx1 h
  have h1 : f x = x^3 - x^2 + 1 := by rw [hf]
  rw [h1]
  have hx2 : x < 0 := h.2
  linarith