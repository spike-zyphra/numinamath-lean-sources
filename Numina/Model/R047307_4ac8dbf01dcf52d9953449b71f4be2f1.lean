import Mathlib

open Real

theorem algebra_189743 {x : ℝ} (hx : x ≥ 0) :
    42 * (sqrt (x + 2018) + sqrt (x + 2)) = 2018 - 2 ↔ x = 7 := by
  constructor
  · -- Assume left side, prove right side
    intro h
    have h1 : sqrt (x + 2018) + sqrt (x + 2) = 48 := by
      nlinarith
    have h2 : sqrt (x + 2018) = 48 - sqrt (x + 2) := by 
      linarith [h1]
    have h3 : sqrt (x + 2018) ^ 2 = (48 - sqrt (x + 2)) ^ 2 := by
      rw [h2]
    have h4 : sqrt (x + 2018) ^ 2 = x + 2018 := by
      rw [Real.sq_sqrt]
      linarith
    have h5 : (48 - sqrt (x + 2)) ^ 2 = 48 ^ 2 - 2 * 48 * sqrt (x + 2) + (sqrt (x + 2) ^ 2) := by
      ring
    rw [h4] at h3
    rw [h5] at h3
    have h6 : sqrt (x + 2) ^ 2 = x + 2 := by
      rw [Real.sq_sqrt]
      linarith
    rw [h6] at h3
    have h7 : sqrt (x + 2) = 3 := by
      nlinarith [Real.sqrt_nonneg (x + 2), Real.sqrt_nonneg (x + 2018)]
    have h8 : x + 2 = 9 := by 
      have h7' : sqrt (x + 2) = 3 := h7
      have h9 : sqrt (x + 2) ^ 2 = 9 := by 
        rw [h7']
        norm_num
      have h10 : sqrt (x + 2) ^ 2 = x + 2 := by 
        rw [Real.sq_sqrt]
        linarith
      linarith
    linarith
  · -- Assume right side, prove left side
    intro h
    rw [h]
    have h1 : sqrt (7 + (2018 : ℝ)) = 45 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt (7 + (2 : ℝ)) = 3 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num