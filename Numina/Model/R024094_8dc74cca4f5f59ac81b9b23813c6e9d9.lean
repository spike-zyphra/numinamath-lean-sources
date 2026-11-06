import Mathlib

theorem algebra_253749 (a : ℕ → ℝ) (ha1 : a 1 = 1)
    (han : ∀ n, a (n + 1) = a n + 1 / a n) :
    14 < a 1000 ∧ a 1000 < 18 := by

  have h1 := han 0
  norm_num [ha1] at h1
  
  by_cases h : a 0 = 0
  · -- Case a 0 = 0
    have h2 : a 0 = 0 := h 
    rw [h2] at h1
    norm_num at h1 
    all_goals linarith 
  · -- Case a 0 ≠ 0 
    have h3 : a 0 ≠ 0 := h
    have h4 : a 0 = a 0 ^ 2 + 1 := by 
      field_simp [h3] at h1 
      linarith 
    have h5 : a 0 ^ 2 - a 0 + 1 = 0 := by 
      nlinarith 
    have h6 : (a 0 - 1 / 2) ^ 2 ≥ 0 := by 
      apply sq_nonneg 
    have h7 : (a 0 - 1 / 2) ^ 2 = - (3 / 4 : ℝ) := by 
      nlinarith 
    nlinarith [sq_nonneg (a 0 - 1 / 2)]