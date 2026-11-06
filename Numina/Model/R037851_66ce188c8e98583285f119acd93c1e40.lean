import Mathlib

open Real

theorem inequalities_180257 (a : ℝ) :
    (a^2 + a + 2) / sqrt (a^2 + a + 1) ≥ 2 := by

  have h1 : a^2 + a + 1 > 0 := by 
    nlinarith [sq_nonneg (a + 1 / 2), sq_nonneg (a + 1)]
  
  have h2 : sqrt (a^2 + a + 1) > 0 := by 
    apply Real.sqrt_pos.2 
    linarith [h1]

  have h3 : a^2 + a + 2 ≥ 2 * sqrt (a^2 + a + 1) := by 
    have h4 : (sqrt (a^2 + a + 1)) ^ 2 = a^2 + a + 1 := by 
      rw [Real.sq_sqrt] 
      linarith 
    have h5 : (a^2 + a + 2) ^ 2 ≥ 4 * (a^2 + a + 1) := by 
      nlinarith [sq_nonneg (a ^ 2 + a + 1), sq_nonneg (a + 1), sq_nonneg (a), sq_nonneg (a - 1)]
    have h6 : (2 * sqrt (a^2 + a + 1)) ^ 2 = 4 * (a^2 + a + 1) := by 
      calc 
        (2 * sqrt (a^2 + a + 1)) ^ 2 = 4 * (sqrt (a^2 + a + 1) ^ 2) := by 
          ring_nf 
        _ = 4 * (a ^ 2 + a + 1) := by 
          rw [Real.sq_sqrt (by linarith)]
  
    have h7 : a^2 + a + 2 ≥ 0 := by 
      nlinarith [sq_nonneg (a + 1 / 2), sq_nonneg (a + 1)]
  
    have h8 : 2 * sqrt (a^2 + a + 1) ≥ 0 := by 
      nlinarith [Real.sqrt_nonneg (a^2 + a + 1)]
  
    nlinarith [h5, h6, h7, h8, sq_nonneg ((a^2 + a + 2) - 2 * sqrt (a^2 + a + 1))]
  
  have h4 : sqrt (a^2 + a + 1) > 0 := h2
  
  have h9 : (a^2 + a + 2) / sqrt (a^2 + a + 1) ≥ 2 := by 
    have h4 : sqrt (a^2 + a + 1) > 0 := h2
    have h10 : a^2 + a + 2 ≥ 2 * sqrt (a^2 + a + 1) := h3
  
    have h11 : (a^2 + a + 2) / sqrt (a^2 + a + 1) ≥ (2 * sqrt (a^2 + a + 1)) / sqrt (a^2 + a + 1) := by 
      apply (div_le_div_right h4).mpr 
      linarith
  
    have h12 : (2 * sqrt (a^2 + a + 1)) / sqrt (a^2 + a + 1) = 2 := by 
      field_simp [h4]

    linarith [h11, h12]

  exact h9