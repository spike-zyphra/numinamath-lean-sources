import Mathlib

theorem inequalities_170257 (a : ℝ) :
    (a^2 + a + 2) / Real.sqrt (a^2 + a + 1) ≥ 2 := by

  have h1 : a ^ 2 + a + 1 > 0 := by
    nlinarith [sq_nonneg (a + 1 / 2)]
  
  have h2 : Real.sqrt (a ^ 2 + a + 1) > 0 := by
    apply Real.sqrt_pos.mpr
    linarith [h1]

  have h3 : (a ^ 2 + a + 2) ≥ 2 * Real.sqrt (a ^ 2 + a + 1) := by 
    have h4 : (Real.sqrt (a ^ 2 + a + 1)) ^ 2 = a ^ 2 + a + 1 := by
      rw [Real.sq_sqrt]
      nlinarith [sq_nonneg (a), sq_nonneg (a + 1)]

    have h5 : (a ^ 2 + a + 2 : ℝ) ^ 2 ≥ 4 * (a ^ 2 + a + 1) := by
      nlinarith [sq_nonneg (a ^ 2 + a + 2 * a), sq_nonneg (a * (a + 1)), sq_nonneg (a + 1 / 2)]
    
    have h7 : (a ^ 2 + a + 2) ^ 2 ≥ (2 * Real.sqrt (a ^ 2 + a + 1)) ^ 2 := by
      nlinarith [h4, Real.sqrt_nonneg (a^2 + a + 1), sq_nonneg (a ^ 2 + a + 2 * a), sq_nonneg (a * (a + 1)), sq_nonneg (a + 1 / 2), Real.sqrt_nonneg (a ^ 2 + a + 1)]
    
    have h8 : (a ^ 2 + a + 2) ≥ (2 * Real.sqrt (a ^ 2 + a + 1)) := by
      nlinarith [show (0 : ℝ) ≤ Real.sqrt (a ^ 2 + a + 1) from Real.sqrt_nonneg (a ^ 2 + a + 1), sq_nonneg (a ^ 2 + a + 2 - 2 * Real.sqrt (a ^ 2 + a + 1))]
    
    linarith
  
  have h9 : (a^2 + a + 2) / Real.sqrt (a ^ 2 + a + 1) ≥ 2 := by
    have h4 : Real.sqrt (a ^ 2 + a + 1) > 0 := h2
    apply (le_div_iff₀ h4).mpr
    linarith

  exact h9