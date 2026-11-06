import Mathlib

open Real

theorem inequalities_208824 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ x * y ^ y * z ^ z ≥ (x * y * z) ^ ((x + y + z) / 3) := by
  have h11 : x ^ x * y ^ y * z ^ z = Real.exp (x * Real.log x + y * Real.log y + z * Real.log z) := by
    have h12 : x ^ x * y ^ y * z ^ z = Real.exp (Real.log (x ^ x * y ^ y * z ^ z)) := by
      rw [Real.exp_log]
      positivity
    have h13 : Real.log (x ^ x * y ^ y * z ^ z) = x * Real.log x + y * Real.log y + z * Real.log z := by
      have h14 : Real.log (x ^ x * y ^ y * z ^ z) = Real.log (x ^ x * (y ^ y * z ^ z)) := by
        ring_nf
      rw [h14]
      have h15 : Real.log (x ^ x * (y ^ y * z ^ z)) = Real.log (x^x) + Real.log (y^y * z^z) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      have h16 : Real.log (x^x) = x * Real.log x := by
        rw [Real.log_rpow]
        all_goals linarith
      have h17 : Real.log (y^y * z^z) = Real.log (y^y) + Real.log (z^z) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      have h18 : Real.log (y^y) = y * Real.log y := by
        rw [Real.log_rpow]
        all_goals linarith
      have h19 : Real.log (z^z) = z * Real.log z := by
        rw [Real.log_rpow]
        all_goals linarith
      rw [h15, h16, h17, h18, h19]
      all_goals linarith
    rw [h12, h13]
  have h12 : (x * y * z) ^ ((x + y + z) / 3) = Real.exp ( ( (x + y + z) / 3 ) * (Real.log x + Real.log y + Real.log z) ) := by
    have h13 : (x * y * z) ^ ((x + y + z) / 3) = Real.exp (Real.log ( (x * y * z) ^ ( (x + y + z) / 3 ) ) ) := by
      rw [Real.exp_log]
      positivity
    have h14 : Real.log ( (x * y * z) ^ ( (x + y + z) / 3 ) ) = ( (x + y + z) / 3 ) * (Real.log x + Real.log y + Real.log z) := by
      calc
        Real.log ( (x * y * z) ^ ( (x + y + z) / 3 ) )
          = ( (x + y + z) / 3 ) * Real.log (x * y * z) := by
            rw [Real.log_rpow]
            all_goals
              positivity
        _ = ( (x + y + z) / 3 ) * (Real.log x + Real.log y + Real.log z) := by
            have h7 : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
              simp [Real.log_mul, hx.ne.symm, hy.ne.symm, hz.ne.symm]
            rw [h7]
    rw [h13, h14]
  have h14 : x * Real.log x + y * Real.log y + z * Real.log z ≥ ( (x + y + z) / 3 ) * (Real.log x + Real.log y + Real.log z) := by 
    have h1 : x * Real.log x + y * Real.log y + z * Real.log z - ( (x + y + z ) / 3 ) * (Real.log x + Real.log y + Real.log z ) ≥ 0 := by
      have h3 : (x - y) * (Real.log x - Real.log y) ≥ 0 := by 
        by_cases h : x ≥ y
        · -- Assume x ≥ y. Then Real.log x ≥ Real.log y.
          have h4 : Real.log x ≥ Real.log y := by 
            apply Real.log_le_log
            all_goals linarith
          nlinarith
        · -- Assume ¬(x ≥ y), so y > x. Then Real.log y > Real.log x.
          have h4 : Real.log y > Real.log x := by 
            apply Real.log_lt_log
            all_goals nlinarith
          nlinarith
      have h4 : (y - z) * (Real.log y - Real.log z) ≥ 0 := by
        by_cases h : y ≥ z
        · -- Assume y ≥ z. Then Real.log y ≥ Real.log z.
          have h4 : Real.log y ≥ Real.log z := by 
            apply Real.log_le_log
            all_goals linarith
          nlinarith
        · -- Assume ¬(y ≥ z), so z > y. Then Real.log z > Real.log y.
          have h4 : Real.log z > Real.log y := by 
            apply Real.log_lt_log
            all_goals nlinarith
          nlinarith
      have h5 : (z - x) * (Real.log z - Real.log x) ≥ 0 := by
        by_cases h : z ≥ x
        · -- Assume z ≥ x. Then Real.log z ≥ Real.log x.
          have h4 : Real.log z ≥ Real.log x := by 
            apply Real.log_le_log
            all_goals linarith
          nlinarith
        · -- Assume ¬(z ≥ x), so x > z. Then Real.log x > Real.log z.
          have h4 : Real.log x > Real.log z := by 
            apply Real.log_lt_log
            all_goals nlinarith
          nlinarith
      have h6 : (x - y) * (Real.log x - Real.log y) + (y - z) * (Real.log y - Real.log z) + (z - x) * (Real.log z - Real.log x) ≥ 0 := by
        linarith [h3, h4, h5]
      nlinarith [h6]
    linarith
  have h15 : Real.exp (x * Real.log x + y * Real.log y + z * Real.log z) ≥ Real.exp ( ( (x + y + z ) / 3 ) * (Real.log x + Real.log y + Real.log z) ) := by 
    apply Real.exp_le_exp_of_le 
    linarith [h14]
  rw [h11, h12]
  all_goals linarith [h15]