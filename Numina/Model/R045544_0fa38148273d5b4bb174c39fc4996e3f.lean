import Mathlib

theorem algebra_115785 (f : ℝ → ℝ) (h : ∀ x y, f x * f y = f (x - y)) :
    ∀ x, f x = 0 ∨ f x = 1 := by
  have h1 : f 0 * f 0 = f 0 := by
    specialize h 0 0
    norm_num at h ⊢
    all_goals linarith
  have h2 : f 0 = 0 ∨ f 0 = 1 := by 
    have h3 : f 0 * f 0 = f 0 := h1
    have h4 : f 0 * (f 0 - 1) = 0 := by
      linarith 
    cases' (mul_eq_zero.mp h4) with h5 h6 
    · -- f 0 = 0 
      left 
      linarith 
    · -- f 0 - 1 = 0 
      right 
      linarith
  cases' h2 with h2 h2
  · -- f 0 = 0 
    have h3 : ∀ x, f x * f x = 0 := by 
      intro x 
      specialize h x x 
      simp [h2] at h ⊢ 
      all_goals linarith 
    intro x 
    have h4 : f x * f x = 0 := h3 x 
    have h5 : f x = 0 := by 
      cases (mul_eq_zero.mp h4) with 
      | inl h6 => linarith 
      | inr h7 => linarith 
    left 
    exact h5 
  · -- f 0 = 1 
    have eq1 : ∀ x, f x * f x = 1 := by 
      intro x 
      specialize h x x 
      simp [h2] at h ⊢ 
      all_goals linarith 
    have eq2 : ∀ x, f (-x) = f x := by 
      intro x 
      have h3 : f 0 * f x = f (0 - x) := by 
        specialize h 0 x 
        simpa using h 
      simp [h2] at h3 
      have h4 : f (-x) = f x := by 
        linarith 
      exact h4 
    intro x 
    have eq3 : f x * (f (2 * x) - 1) = 0 := by 
      have h4x2 : f (2 * x) * f x = f x := by 
        specialize h (2 * x) x 
        ring_nf at h ⊢ 
        all_goals linarith 
      nlinarith 
    cases' (mul_eq_zero.mp eq3) with h5 h6 
    · -- f x = 0 
      exfalso 
      have h6 : f x * f x = 1 := eq1 x 
      rw [h5] at h6 
      nlinarith 
    · -- f (2 * x) - 1 = 0 
      have h2x : f (2 * x) = 1 := by 
        linarith 
      have h11 : f x = 1 := by 
        have h15 : f (x / 2) * f (x / 2) = 1 := by 
          specialize eq1 (x / 2) 
          norm_num at eq1 ⊢ 
          all_goals linarith 
        have h14 : f (x / 2) * f (- (x / 2)) = f x := by 
          specialize h (x / 2) (- (x / 2)) 
          have h5 : (x / 2 : ℝ) - (- (x / 2)) = x := by 
            ring 
          rw [h5] at h 
          all_goals linarith 
        have h17 : f (- (x / 2)) = f (x / 2) := by 
          specialize eq2 (x / 2) 
          all_goals linarith 
        rw [h17] at h14 
        nlinarith 
      right 
      exact h11