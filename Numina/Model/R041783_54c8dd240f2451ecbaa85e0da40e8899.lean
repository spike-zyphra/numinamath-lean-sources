import Mathlib

theorem algebra_285161 {f : ℝ → ℝ} (h : ∀ x y, f (x * y + 1) = f x * f y - f y - x + 2) :
    10 * f 2006 + f 0 = 20071 := by
  have h1 := h 0 0
  norm_num at h1 
  have h2 := h 1 0
  norm_num at h2 
  have h3 := h 2 0
  norm_num at h3 
  have h4 := h 0 1
  norm_num at h4 
  have h5 := h 2006 0
  norm_num at h5 
  have h6 : f 0 = 1 := by
    have h7 := h 0 1
    norm_num at h7 
    have h8 := h 0 0
    norm_num at h8 
    have h9 := h 1 0
    norm_num at h9 
    have h10 := h 2 0
    norm_num at h10 
    have h11 := h 0 2
    norm_num at h11 
    nlinarith [sq_nonneg (f 1 - 2), sq_nonneg (f 0 - 1), sq_nonneg (f 2006 - 2007)]
  have h7 : f 1 = 2 := by
    have h8 := h 0 0
    norm_num at h8 
    rw [h6] at h8 
    linarith 
  -- Solving for f(2006)
  have h8 : f 2006 = 2007 := by
    have h9 := h 2006 0
    norm_num at h9 
    rw [h6, h7] at h9
    linarith 
  -- Computing 10 * f(2006) + f(0)
  rw [h8, h6]
  norm_num