import Mathlib


theorem algebra_9250 {f : ℝ → ℝ} (h : ∀ x, 2 * f x + f (-x) = 2 * x) :
    ∀ x, f x = 2 * x := by
  intro x
  have h1 := h x
  have h2 := h (-x)
  simp [show -(-x) = x by ring] at h2
  have eq3 : f (-x) = -f x := by 
    linarith
  rw [eq3] at h1
  linarith