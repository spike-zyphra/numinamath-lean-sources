import Mathlib

theorem algebra_239730 {f : ℝ → ℝ} (h : ∀ x y, f (x ^ 2 * y) = f (x * y) + y * f (f x + y)) :
    ∀ y, f y = 0 := by

  have h1 : ∀ y, y * f (f 0 + y) = 0 := by
    intro y
    have eq1 : f (0 ^ 2 * y) = f (0 * y) + y * f (f 0 + y) := h 0 y
    simp at eq1 ⊢ 
    by_cases h2 : y = 0 
    · -- If y = 0, then the equation is 0 = 0.
      rw [h2]
      all_goals norm_num 
    · -- Now consider the case where y ≠ 0. From eq1, which is y = 0 ∨ f (f 0 + y) = 0, and y ≠ 0, we must have f (f 0 + y) = 0.
      have h3 : f (f 0 + y) = 0 := by 
        tauto 
      rw [h3] 
      all_goals 
      norm_num [h2]

  have hf0 : f 0 = 0 := by 
    have eq1 := h1 (-f 0)
    have : -f 0 * f (f 0 + (-f 0)) = 0 := by simpa using eq1 
    have eq2 : f 0 + (-f 0) = (0 : ℝ) := by 
      linarith 
    have eq3 : -f 0 * f (f 0 + (-f 0)) = -f 0 * f (0) := by 
      rw [show f 0 + (-f 0) = (0 : ℝ) by linarith] 
    rw [eq3] at this 
    have eq4 : f 0 ^ 2 = 0 := by 
      nlinarith
    have eq5 : f 0 = 0 := by 
      nlinarith 
    exact eq5

  have h2 : ∀ y, y * f y = 0 := by 
    intro y 
    have eq1 := h1 y 
    have : f 0 + y = y := by 
      rw [hf0] 
      all_goals linarith 
    rw [this] at eq1 
    linarith 

  intro y
  by_cases hy : y = 0 
  · -- If y = 0, then f 0 = 0 by hf0.
    rw [hy]
    all_goals norm_num [hf0]
  · -- If y ≠ 0, from h2 y : y * f y = 0, multiply both sides by the inverse of y.
    have hy' : y ≠ 0 := hy
    have eq1 := h2 y
    have eq2 : f y = 0 := by 
      apply (mul_left_inj' hy').mp 
      linarith 
    exact eq2