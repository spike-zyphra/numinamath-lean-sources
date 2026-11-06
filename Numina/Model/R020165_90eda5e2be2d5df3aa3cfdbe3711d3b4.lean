import Mathlib

theorem algebra_294111 {f : ℝ → ℝ} (h : ∀ x y, f x * f y = f (x * y) + x + y) :
    ∀ x, f x = 1 + x := by
  have h1 : f 0 * f 0 = f (0 * 0) + 0 + 0 := h 0 0
  have h2 : f 0 * f 0 = f 0 := by
    simp at h1 ⊢
    linarith
  have h3 : f 0 = 1 := by 
    by_cases h4 : f 0 = 0
    · -- Assume f 0 = 0 
      have eq1 := h 1 0
      norm_num [h4] at eq1
      all_goals linarith
    · -- Assume f 0 ≠ 0
      have : f 0 * (f 0 - 1) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.mp this) with h5 h6 
      · -- f 0 = 0 
        contradiction
      · -- f 0 - 1 = 0 
        linarith
  have eq2 := h 1 1
  norm_num at eq2 
  have h4 : f 1 = 2 ∨ f 1 = -1 := by 
    have h5 : f 1 ^ 2 - f 1 - 2 = 0 := by linarith
    have h6 : (f 1 - 2) * (f 1 + 1) = 0 := by nlinarith 
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- f 1 - 2 = 0 
      left 
      linarith
    · -- f 1 + 1 = 0 
      right 
      linarith
  cases h4 with 
  | inl h5 =>
    intro x
    have eq3 := h x 1 
    simp [h5] at eq3 
    linarith 
  | inr h5 =>
    have eq3 := h 1 0 
    norm_num [h3] at eq3 
    norm_num [h5] at eq3 
    all_goals linarith