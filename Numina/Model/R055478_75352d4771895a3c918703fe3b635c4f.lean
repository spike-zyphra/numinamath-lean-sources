import Mathlib

theorem inequalities_42786 (f : ℝ → ℝ) :
    (∀ x y z, f (x * y) + f (x * z) ≥ f x * f (y * z) + 1) ↔ ∀ x, f x = 1 := by
  constructor
  · -- First prove f(x) = 1 for all x from the inequality
    intro h
    have h1 : f 0 = 1 := by
      have h0 := h 0 0 0
      simp at h0
      nlinarith [sq_nonneg (f 0 - 1)]
    
    have h2 : ∀ t, f t ≤ 1 := by 
      intro t
      have h0:= h 0 1 t
      simp [h1] at h0 
      nlinarith

    have h3 : f 1 = 1 := by 
      have h1_eq := h 1 1 1
      simp at h1_eq 
      nlinarith [sq_nonneg (f 1 - 1)]

    intro x 
    have h4 : f x ≥ 1 := by 
      have hx1 := h x 1 1
      simp [show x * 1 = x by ring, show (1 : ℝ) * 1 = (1 : ℝ) by ring, h3] at hx1 
      nlinarith 
    have hx2 : f x ≤ 1 := h2 x 
    linarith 

  · -- Now prove the reverse
    intro hf x y z
    have h1 : f (x * y) = 1 := by 
      apply hf 
    have h2 : f (x * z) = 1 := by 
      apply hf 
    have h3 : f x = 1 := by 
      apply hf 
    have h4 : f (y * z) = 1 := by 
      apply hf 
    rw [h1, h2, h3, h4]
    all_goals norm_num