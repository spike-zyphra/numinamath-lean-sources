import Mathlib

theorem algebra_13461 (x : ℝ) (hx : x = Real.sqrt x + 30) :
    x = 36 := by 
  have h1 : x ≥ 0 := by 
    by_contra h
    push_neg at h
    have h2 : Real.sqrt x = 0 := by 
      rw [Real.sqrt_eq_zero']
      linarith 
      all_goals nlinarith 
    rw [h2] at hx 
    nlinarith 
  have h2 : x - Real.sqrt x - 30 = 0 := by 
    linarith 
  have h3 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x 
  have h4 : Real.sqrt x ^ 2 = x := by 
    rw [Real.sq_sqrt] 
    linarith [h1] 
  have h5 : Real.sqrt x ^ 2 - Real.sqrt x - 30 = 0 := by 
    nlinarith [h2, h4] 
  have h6 : (Real.sqrt x - 6) * (Real.sqrt x + 5) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp h6) with h7 h8 
  · 
    have h9 : Real.sqrt x = 6 := by 
      linarith 
    have h10 : x = 36 := by 
      have h11 : Real.sqrt x = 6 := h9 
      have h12 : x = Real.sqrt x ^ 2 := by 
        nlinarith [Real.sq_sqrt (show 0 ≤ x from by linarith [h1, Real.sqrt_nonneg x]), Real.sqrt_nonneg x] 
      rw [h12, h11] 
      all_goals nlinarith 
    exact h10 
  · 
    have h9 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x 
    nlinarith