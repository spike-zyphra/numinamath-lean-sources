import Mathlib

theorem algebra_265118 (f : ℝ → ℝ) :
    (∀ x y, f (f x) + f (f y) = 2 * y + f (x - y)) ↔ (∀ x, f x = x) := by 
  constructor
  · -- Assume f satisfies the equation, prove f x = x
    intro h 
    have h1 : ∀ x, f (f x) = x + f 0 / 2 := by 
      intro x 
      have h2 := h x x 
      simp at h2 
      linarith 
    -- Prove f 0 = 0 
    have h2' : f (f (f 0)) = 0 := by
      have eq1 := h (f 0) (0)
      simp [show f (f 0) = f 0 / 2 by 
        have h4' := h1 0 
        norm_num at h4' ⊢ 
        linarith] at eq1 ⊢
      all_goals linarith 
    -- Use above to prove f 0 = 0 
    have h3' : f 0 = 0 := by 
      have eq1 : f (f (f 0)) = f 0 + f 0 / 2 := by 
        specialize h1 (f 0) 
        simpa using h1 
      rw [h2'] at eq1 
      linarith 
    have h3 : ∀ x, f (f x) = x := by
      intro x
      have h1' := h1 x 
      rw [h3'] at h1' 
      linarith 
    intro x 
    have h4 := h x 0 
    simp [h3', h3] at h4 ⊢ 
    all_goals linarith 
  · -- Assume f x = x for all x, prove the functional equation 
    intro h x y 
    simp [h] 
    all_goals linarith