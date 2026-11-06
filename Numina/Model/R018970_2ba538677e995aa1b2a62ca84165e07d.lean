import Mathlib

theorem inequalities_258766 (x : ℝ) (hx : 0 < x) :
    Real.sqrt (x^2 - x + 1 / 2) ≥ 1 / (x + 1 / x) := by 
  have h1 : 0 < x := hx
  have h2 : x ^ 2 - x + 1 / 2 ≥ 0 := by 
    nlinarith [sq_nonneg (x - 1 / 2)]
  have h3 : Real.sqrt (x ^ 2 - x + 1 / 2) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h4 : (x + 1 / x) > 0 := by
    have hx1 : x > 0 := hx
    have hx2 : 1 / x > 0 := by 
      apply div_pos 
      norm_num 
      all_goals linarith
    linarith
  have h5 : 1 / (x + 1 / x) > 0 := by
    apply div_pos 
    norm_num 
    linarith [h4]
  have h6 : (Real.sqrt (x^2 - x + 1 / 2)) ^ 2 = x ^ 2 - x + 1 / 2 := by 
    rw [Real.sq_sqrt]
    linarith 
  have h7 : Real.sqrt (x ^ 2 - x + 1 / 2) ≥ 1 / (x + 1 / x) := by 
    have h6' : (Real.sqrt (x ^ 2 - x + 1 / 2)) ^ 2 ≥ (1 / (x + 1 / x)) ^ 2 := by 
      have h8 : (Real.sqrt (x ^ 2 - x + 1 / 2)) ^ 2 = x ^ 2 - x + 1 / 2 := h6
      have h9 : (1 / (x + 1 / x)) ^ 2 = 1 / (x + 1 / x) ^ 2 := by 
        field_simp 
      rw [h8, h9]
      have h10 : x ^ 2 - x + 1 / 2 - (1 / (x + 1 / x) ) ^ 2 ≥ 0 := by 
        have h11 : (x + 1 / x) = (x ^ 2 + 1) / x := by 
          field_simp 
          <;> ring
        have h12 : (1 / (x + 1 / x)) ^ 2 = x ^ 2 / (x ^ 2 + 1) ^ 2 := by 
          rw [h11]
          field_simp 
          <;> ring
        rw [h12]
        have h13 : x ^ 2 - x + 1 / 2 - x ^ 2 / (x ^ 2 + 1) ^ 2 ≥ 0 := by 
          have h14 : x ^ 2 - x + 1 / 2 - x ^ 2 / (x ^ 2 + 1) ^ 2 = ( (x ^ 2 - x + 1 / 2 ) * (x ^ 2 + 1 ) ^ 2 - x ^ 2 ) / ( (x  ^ 2 + 1 ) ^ 2 ) := by
            field_simp 
            <;> ring 
          rw [h14]
          apply div_nonneg 
          · -- Show Numerator is Non-negative 
            have h15 : ( (x ^ 2 - x + 1 / 2 ) * (x ^ 2 + 1 ) ^ 2 - x ^ 2 ) ≥ 0 := by
              nlinarith [ sq_nonneg (x ^ 2 - 1 ), sq_nonneg (x - 1 ), sq_nonneg (x + 1 ), sq_nonneg (x ^ 2 - x ), sq_nonneg (x ^ 2 -1/2), sq_nonneg (x -1/2), mul_pos hx (show 0 < x by linarith ), mul_pos hx (show 0 < x ^ 2 by nlinarith ) ]
            linarith 
          · -- Show Denominator is Positive 
            positivity 
        linarith 
      linarith 
    have h8 : Real.sqrt (x ^ 2 - x + 1 / 2) ≥ 0 := by 
      apply Real.sqrt_nonneg 
    have h9 : (1 / (x + 1 / x)) ≥ 0 := by linarith 
    nlinarith [ Real.sqrt_nonneg (x ^ 2 - x + 1 / 2 ), h6', h5 ]
  exact h7