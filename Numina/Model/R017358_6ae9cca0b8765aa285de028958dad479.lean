import Mathlib

theorem algebra_13169 {f : ℝ → ℝ} (h : ∀ x y, f (2 * x + f y) = x + y + f x) :
    ∀ x, f x = x := by 
  have h1 : ∀ y, f (f y) = y + f 0 := by 
    intro y 
    specialize h 0 y 
    norm_num at h 
    simpa using h 
  -- Proving injective 
  have h2 : ∀ y₁ y₂, f y₁ = f y₂ → y₁ = y₂ := by 
    intro y₁ y₂ h_eq 
    have h3 := h1 y₁ 
    have h4 := h1 y₂ 
    rw [h_eq] at h3 
    linarith 
  -- Proving f(0) = 0 
  have h3 : f 0 = 0 := by 
    have h4 : f (f 0) = f 0 := by 
      specialize h1 0 
      norm_num at h1 ⊢ 
      linarith 
    have h7 : f 0 = 0 := by 
      apply h2 
      all_goals 
      linarith [h4] 
    exact h7 
  -- Proving f(2x) = x + f(x) 
  have h4 : ∀ x, f (2 * x) = x + f x := by 
    intro x 
    specialize h x 0 
    simp [h3] at h 
    linarith 
  -- Proving the key property f(2x + y) = x + f(y) + f(x) 
  have h5 : ∀ (x y : ℝ), f (2 * x + y) = x + f y + f x := by 
    intro x y 
    have eq1 := h x (f y) 
    have eq2 : 2 * x + f (f y) = 2 * x + y := by 
      have eq3 : f (f y) = y := by 
        specialize h1 y 
        linarith 
      rw [eq3] 
    have eq3 : f (2 * x + y) = x + f y + f x := by 
      rw [show 2 * x + y = 2 * x + f (f y) by linarith [eq2]]
      linarith [eq1]
    exact eq3 
  -- Deriving f(-x) = -x 
  have h6 : ∀ x, f (-x) = -x := by 
    intro x 
    have eq6 := h5 x (-x) 
    have eq7 : f (2 * x + -x) = x + f (-x) + f x := eq6 
    have eq8 : (2 * x + -x : ℝ) = x := by ring 
    rw [eq8] at eq7 
    have eq10 : f (-x) = -x := by 
      have eq11 : f x = f x := by trivial 
      linarith 
    exact eq10 
  intro x 
  specialize h6 (-x) 
  have eq12 : f (-(-x)) = -(-x) := h6 
  simp only [neg_neg] at eq12 
  linarith