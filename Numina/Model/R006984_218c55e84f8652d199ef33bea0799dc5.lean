import Mathlib

theorem inequalities_170229 (f : ℝ → ℝ) (h1 : ∀ x, f x ≤ x)
    (h2 : ∀ x y, f (x + y) ≤ f x + f y) : ∀ x, f x = x := by
  have h0 : f 0 = 0 := by 
    have h10 : f 0 ≤ 0 := by apply h1
    have h20 : f 0 ≥ 0 := by
      specialize h2 0 0 
      norm_num at h2
      linarith
      all_goals linarith
    linarith
  intro x 
  have h1' : f x ≤ x := h1 x
  have h3 : f (x + (-x)) ≤ f x + f (-x) := h2 x (-x)
  have h21 : f (x + (-x)) = f 0 := by 
    ring_nf
  rw [h21] at h3
  rw [h0] at h3
  have h6 : f (-x) ≤ -x := by 
    specialize h1 (-x)
    linarith
  have h7 : f x ≥ x := by 
    linarith [h3, h6]
  linarith [h7, h1']