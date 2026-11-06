import Mathlib

theorem algebra_301347 (f : ℝ → ℝ) (h : ∀ x y, f (x * y) = f x * f y - x - y) :
    ∀ x, f x = x + 1 := by 
  have h1 : f 0 = 1 := by
    have h00 := h 0 0 
    simp at h00 
    have h0 : (f 0) * (f 0 - 1) = 0 := by
      linarith 
    cases' (mul_eq_zero.mp h0) with h4 h5
    · -- Case h4 : f(0) = 0 
      have h2 := h 1 0 
      simp [h4] at h2 
      all_goals linarith 
    · -- Case h5 : f(0) - 1 = 0 
      linarith 
  intro x 
  have h2 := h x 0 
  simp [h1] at h2 
  linarith