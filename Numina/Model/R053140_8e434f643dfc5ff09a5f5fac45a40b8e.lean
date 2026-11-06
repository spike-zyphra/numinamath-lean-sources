import Mathlib

theorem algebra_179596 {f : ℝ → ℝ} (h : ∀ x > 0, f (2 * x) = 2 / (2 + x)) :
    ∀ x > 0, 2 * f x = 8 / (4 + x) := by
  intro x hx
  have h1 := h (x / 2) (by linarith)
  have eq1 : 2 * (x / 2) = x := by ring
  rw [eq1] at h1
  rw [h1]
  field_simp
  <;> ring