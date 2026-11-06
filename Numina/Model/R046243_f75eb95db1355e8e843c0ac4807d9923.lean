import Mathlib

theorem algebra_2869 (x b : ℝ) (hx : x = 6 + Real.sqrt b) (h : x^2 - 12 * x + 32 = 70) :
    b = 74 := by 
  rw [hx] at h
  have h1 : (6 + Real.sqrt b) ^ 2 - 12 * (6 + Real.sqrt b) + 32 = 70 := h
  have h3 : (Real.sqrt b) ^ 2 = 74 := by
    nlinarith [Real.sqrt_nonneg b]
  have h4 : 0 ≤ b := by
    by_contra h5
    push_neg at h5
    have h5 : b < (0 : ℝ) := by linarith 
    -- Show that if b < 0, then sqrt b = 0, but then the solution x would invalid.
    have h6 : Real.sqrt b = 0 := by
      rw [Real.sqrt_eq_zero']
      all_goals nlinarith 
    rw [h6] at h1 
    nlinarith 
  -- Derive the value of b from h3
  have h5 : b = 74 := by
    have h7 : (Real.sqrt b) ^ 2 = b := by
      rw [Real.sq_sqrt]
      linarith 
    nlinarith [h3, h7, Real.sqrt_nonneg b]
  linarith [h5]