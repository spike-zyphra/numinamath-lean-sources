import Mathlib

theorem algebra_317991 (a b : ℝ) (ha : a ≥ 1) (h : ∃ x : ℝ, x^2 - 2 * b * x - (a - 2 * b^2) = 0)
    (h' : 2 * a^2 - a * b^2 - 5 * a + b^2 + 4 = 0) : a^2 + b^2 = 6 := by
  rcases h with ⟨x, hx⟩ 
  have h1 : (x-b)^2 = a - b^2 := by
    nlinarith 
  have h2 : a - b^2 ≥ 0 := by
    nlinarith [sq_nonneg (x-b)]
  by_cases h3 : a > 1 
  · -- Assume a > 1
    -- From h' equation we can solve for b^2.
    have h4 : a - 1 > 0 := by linarith 
    have h5 : b^2 = (2 * a^2 - 5 * a + 4) / (a - 1) := by 
      have h5 : a -1 > 0 := h4 
      field_simp 
      nlinarith [h']
    -- Now we show a = 2
    have h6 : (a - 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b^2 - 2), h5, sq_nonneg (b), sq_nonneg (x - b), sq_nonneg (a - 2)]
    have h7 : a = 2 := by nlinarith 
    have h8 : b^2 = 2 := by 
      rw [show a = 2 by linarith] at h5 
      nlinarith 
    have h9 : a ^ 2 + b^2 = 6 := by 
      nlinarith [h8] 
    linarith 
  · -- Assume a =1
    push_neg at h3 
    have h4 : a = 1 := by linarith 
    rw [h4] at h' 
    nlinarith