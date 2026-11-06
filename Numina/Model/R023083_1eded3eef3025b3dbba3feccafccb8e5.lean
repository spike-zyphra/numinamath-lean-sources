import Mathlib

theorem inequalities_601259 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    27 / 10 ≥ 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) + 1 / (1 + c ^ 2) := by

  have h1 : 0 < (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) := by positivity

  have h2 : 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) + 1 / (1 + c ^ 2) ≤ 27 / 10 := by
    have h3 : 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) + 1 / (1 + c ^ 2) - 27 / 10 ≤ 0 := by
      have h4 : 0 < (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) := h1
      have h5 : (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) + 1 / (1 + c ^ 2) - 27 / 10) = (10 * ( (1 + b ^ 2) * (1 + c ^ 2) ) + 10 * ( (1 + a ^ 2) * (1 + c ^ 2) ) + 10 * ( (1 + a ^ 2) * (1 + b ^ 2) ) - 27 * (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)) / ( 10 * (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ) := by
        field_simp
        ring
      rw [h5] at *
      apply div_nonpos_of_nonpos_of_nonneg
      -- Show 10 * ( (1 + b ^ 2) * (1 + c ^ 2) ) + 10 * ( (1 + a ^ 2) * (1 + c ^ 2) ) + 10 * ( (1 + a ^ 2) * (1 + b ^ 2) ) - 27 * (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≤ 0
      -- Show numerator is non-positive 
      have h7 : 10 * ( (1 + b ^ 2) * (1 + c ^ 2) ) + 10 * ( (1 + a ^ 2) * (1 + c ^ 2) ) + 10 * ( (1 + a ^ 2) * (1 + b ^ 2) ) - 27 * (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≤ 0 := by
        rw [show c = 1 - a - b by linarith] 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          sq_nonneg (a * b - a * (1 - a - b)), sq_nonneg (a * b - b * (1 - a - b)), 
          sq_nonneg (a * (1 - a - b) - b * (1 - a - b)), 
          mul_pos ha hb, mul_pos hb (show 0 < 1 - a - b by nlinarith), 
          mul_pos ha (show 0 < 1 - a - b by nlinarith)]
      linarith
      -- Show denominator is non-negative
      all_goals
        positivity

    linarith

  linarith [h2]