import Mathlib

open Real

theorem inequalities_106844 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sqrt (a^2 + b^2) ≥ (a + b) / sqrt 2 := by
  have h1 : 0 ≤ (a + b) / sqrt 2 := by
    apply div_nonneg
    · -- Show a + b ≥ 0
      linarith
    · -- Show sqrt 2 ≥ 0
      positivity

  have h2 : sqrt (a^2 + b^2) ≥ (a + b) / sqrt 2 := by
    have h3 : sqrt (a^2 + b^2) ≥ 0 := by positivity

    have h4 : (a + b) / sqrt 2 ≥ 0 := by
      apply div_nonneg
      · -- Show a + b ≥ 0
        linarith
      · -- Show sqrt 2 ≥ 0
        positivity

    have h5 : sqrt (a^2 + b^2) ^ 2 ≥ ((a + b) / sqrt 2) ^ 2 := by
      have h6 : sqrt (a^2 + b^2) ^ 2 = a^2 + b^2 := by
        rw [Real.sq_sqrt]
        positivity
      have h7 : ((a + b) / sqrt 2) ^ 2 = ((a + b) ^ 2) / 2 := by
        field_simp [Real.sqrt_sq]
        <;> positivity
      rw [h6, h7]
      nlinarith [sq_nonneg (a - b)]
    
    nlinarith [Real.sqrt_nonneg (a^2 + b^2), Real.sq_sqrt (show 0 ≤ (a^2 + b^2) by positivity), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), sq_nonneg (sqrt 2), sq_nonneg (a - b)]
  
  exact h2