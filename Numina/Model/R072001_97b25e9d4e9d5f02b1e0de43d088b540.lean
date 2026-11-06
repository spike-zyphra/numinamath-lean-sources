import Mathlib

theorem algebra_129263 (f : ℝ → ℝ) (h : ∀ x y, f (x + y) = f x - f y) :
    ∀ x, f x = 0 := by
  have h0 : f 0 = 0 := by
    specialize h 0 0
    simp at h
    linarith

  have h2 : ∀ x, f (2 * x) = 0 := by
    intro x
    have h1 : f (x + x) = f x - f x := h x x
    have eq1 : x + x = (2 * x : ℝ) := by ring
    rw [eq1] at h1 
    have eq2 : f (2 * x) = f x - f x := h1
    have eq_zero : f x - f x = 0 := by
      ring_nf
      all_goals linarith
    rw [eq_zero] at eq2 
    exact eq2

  intro x
  have h3 : f x = 0 := by
    have h4 : f (2 * (x / 2)) = 0 := h2 (x / 2)
    have h5 : 2 * (x / 2) = x := by 
      ring_nf
    rw [h5] at h4 
    exact h4

  exact h3