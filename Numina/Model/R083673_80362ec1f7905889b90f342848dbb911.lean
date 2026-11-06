import Mathlib

theorem algebra_108709 (a : ℝ) (f : ℝ → ℝ) (h : ∀ x, f (a - x) = -f (a + x)) :
    ∀ x, f x = -f (2 * a - x) := by 
  intro x
  have h1 := h (a - x)
  have h2 : f (a - (a - x)) = -f (a + (a - x)) := by 
    simpa using h1
  have h3 : f (a - (a - x)) = f x := by 
    ring_nf
  have h4 : f (a + (a - x)) = f (2 * a - x) := by 
    ring_nf
  rw [h3] at h2
  rw [h4] at h2
  linarith