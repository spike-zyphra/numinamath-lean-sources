import Mathlib

theorem algebra_8699
    {f : ℝ → ℝ}
    (h : ∀ x, 2 * f x + f (x ^ 2 - 1) = 1) :
    f (Real.sqrt 2) = 1 / 3 := by 
  have h1 := h (Real.sqrt 2)
  have h2 := h 1
  have h3 := h (0 : ℝ)
  have h4 := h (-1 : ℝ)
  have eq1 : 2 * f (Real.sqrt 2) + f 1 = 1 := by 
    have h1' := h1
    rw [show (Real.sqrt 2) ^ 2 - 1 = (1 : ℝ) by 
      have h22 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      linarith 
    ] at h1' 
    linarith 
  have eq2 : 2 * f 1 + f (0 : ℝ) = 1 := by 
    have h2' := h2 
    rw [show (1 : ℝ) ^ 2 - 1 = (0 : ℝ) by norm_num] at h2' 
    linarith 
  have eq3 : 2 * f (0 : ℝ) + f (-1 : ℝ) = 1 := by 
    have h3' := h3 
    rw [show (0 : ℝ) ^ 2 - 1 = (-1 : ℝ) by norm_num] at h3' 
    linarith 
  have eq4 : 2 * f (-1 : ℝ) + f (0 : ℝ) = 1 := by 
    have h4' := h4 
    rw [show (-1 : ℝ) ^ 2 - 1 = (0 : ℝ) by norm_num] at h4' 
    linarith 
  have h_eq1 : f (0 : ℝ) = 1 / 3 := by 
    linarith [eq3, eq4] 
  have h_eq2 : f (-1 : ℝ) = 1 / 3 := by 
    linarith [eq3, eq4] 
  have h_eq3 : f 1 = 1 / 3 := by 
    linarith [eq2, h_eq1] 
  linarith [eq1, h_eq3]