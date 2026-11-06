import Mathlib

theorem inequalities_127144 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    ((1 / a ^ 2 - a ^ 3) * (1 / b ^ 2 - b ^ 3)) ≥ (31 / 8) ^ 2 := by 
  have h1 : b = 1 - a := by linarith 
  rw [h1]
  have pos1 : a > 0 := by linarith 
  have pos2 : (1 - a) > 0 := by 
    have h11 : (1 - a) > 0 := by 
      nlinarith 
    nlinarith 
  have h3 : a * (1 - a) > 0 := by 
    apply mul_pos 
    linarith 
    linarith 
  have h4 : ( (1 / a ^ 2 - a ^ 3) * (1 / (1 - a) ^ 2 - (1 - a) ^ 3 ) ) =
      ( (1 - a^5) * (1 - (1 - a)^5) ) / ( a^2 * (1 - a)^2 ) := by 
    field_simp [(show a ≠ 0 by positivity), (show (1 - a) ≠ 0 by 
      nlinarith 
    )] 
    ring 
  have h5 : ( (1 - a^5) * (1 - (1 - a)^5) ) / ( a^2 * (1 - a)^2 ) ≥ (31 / 8) ^ 2 := by 
    have pos2' : a ^ 2 * (1 - a) ^ 2 > 0 := by 
      positivity 
    have h6 : ( (1 - a^5) * (1 - (1 - a)^5) ) ≥ (31 / 8) ^ 2 * ( a^2 * (1 - a)^2 ) := by 
      have h8 : a * (1 - a) > 0 := by 
        apply mul_pos 
        linarith 
        linarith 
      nlinarith [ sq_nonneg (a - 1 / 2), sq_nonneg (a^2 - (1 - a) ^ 2), sq_nonneg (a - (1 - a)), sq_nonneg ((a - (1 - a)) * (a * (1 - a))), sq_nonneg (a^3 - (1 - a) ^ 3), sq_nonneg ((a^2 - (1 - a) ^ 2) * (a - (1 - a))), sq_nonneg (a * (1 - a) - 1 / 4), sq_nonneg (a^2 - (1 - a)^2), sq_nonneg (a^3 - (1 - a) ^3), sq_nonneg (a^4 - (1 - a) ^4), sq_nonneg (a^5 - (1 - a) ^5), 
          mul_pos ha (show 0 < 1 - a by nlinarith), mul_pos (show 0 < a * (1 - a) by nlinarith) (show 0 < a * (1 - a) by nlinarith), mul_pos (show 0 < a by linarith) (show 0 < (1 - a)^2 by nlinarith), mul_pos (show 0 < (1 - a) by nlinarith) (show 0 < a^2 by nlinarith) 
        ]
    have h7 : ( (1 - a^5) * (1 - (1 - a)^5) ) / ( a^2 * (1 - a)^2 ) ≥ (31 / 8) ^ 2 := by 
      apply (le_div_iff₀ (by positivity)).mpr 
      linarith 
    linarith 
  linarith [ h4, h5 ]