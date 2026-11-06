import Mathlib

theorem algebra_273419 (n : ℝ) (h : 0 ≤ n) (h' : Real.sqrt (25 - Real.sqrt n) = 3) :
    n = 256 := by
  have h1 : 25 - Real.sqrt n ≥ 0 := by
    by_contra h2
    push_neg at h2
    have h2' : Real.sqrt (25 - Real.sqrt n) = 0 := by
      rw [Real.sqrt_eq_zero']
      linarith
      all_goals linarith [Real.sqrt_nonneg n]
    rw [h2'] at h'
    all_goals nlinarith [Real.sqrt_nonneg (25 - Real.sqrt n), Real.sqrt_nonneg n]

  have h2 : (Real.sqrt (25 - Real.sqrt n)) ^ 2 = 3 ^ 2 := by
    rw [h']
  
  have h3 : Real.sqrt (25 - Real.sqrt n) ^ 2 = (25 - Real.sqrt n) := by
    rw [Real.sq_sqrt]
    all_goals linarith [h1]

  have h4 : Real.sqrt n = 16 := by
    nlinarith [h2, h3, Real.sqrt_nonneg (25 - Real.sqrt n), Real.sqrt_nonneg n]

  have h5 : n = (Real.sqrt n) ^ 2 := by
    rw [Real.sq_sqrt]
    all_goals linarith

  rw [h4] at h5
  nlinarith