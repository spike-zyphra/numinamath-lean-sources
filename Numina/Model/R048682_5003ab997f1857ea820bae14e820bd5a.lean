import Mathlib

theorem algebra_257615 {f : ℤ → ℤ → ℤ} (h1 : ∀ x, f x x = x)
    (h2 : ∀ x, f x 0 = 2 * x) (h3 : ∀ a b c d, f a b + f c d = f (a + c) (b + d)) :
    f 2 3 + f 0 3 = -2 ∧ f 1024 48 = 2000 := by
  -- setting a = 0, b = x, c = x, d = 0
  have h4 : ∀ y, f 0 y = -y := by
    intro y
    have eq1 := h3 0 y y 0
    simp [h1, h2] at eq1 
    linarith
  have h5 : ∀ a b, f a b = 2 * a - b := by
    intro a b
    have eq1 := h3 a 0 0 b
    have h6 : f a 0 = 2 * a := by 
      specialize h2 a 
      simpa using h2
    simp [h6, h4 b] at eq1 
    linarith
  -- compute the answers
  have h11 : f 2 3 + f 0 3 = -2 := by 
    rw [h5 2 3, h5 0 3]
    all_goals norm_num 
  have h22 : f 1024 48 = 2000 := by 
    rw [h5 1024 48]
    all_goals norm_num 
  exact ⟨h11, h22⟩