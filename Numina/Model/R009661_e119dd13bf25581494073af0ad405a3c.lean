import Mathlib

theorem algebra_9179 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x)
    (h₁ : ∀ x ≥ 0, f x = 2 * x - x ^ 2) :
    ∀ x < 0, f x = -2 * x - x ^ 2 := by
  intro x hx 
  have h2 : -x ≥ 0 := by linarith 
  have h3 : f (-x) = 2 * (-x) - (-x) ^ 2 := h₁ (-x) h2 
  have h4 : f (-x) = f x := h₀ x 
  rw [h3] at h4 
  linarith [h4]