import Mathlib

theorem inequalities_90918 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x ^ x * y ^ y ≥ x ^ y * y ^ x := by
  have h1 : x ^ x * y ^ y ≥ x ^ y * y ^ x := by
    have h2 : x ^ x * y ^ y = Real.exp (x * Real.log x + y * Real.log y) := by
      have h3 : Real.log (x ^ x * y ^ y) = x * Real.log x + y * Real.log y := by
        have h4 : Real.log (x ^ x * y ^ y) = Real.log (x^x) + Real.log (y^y) := by
          rw [Real.log_mul (by positivity) (by positivity)]
        have h5 : Real.log (x^x) = x * Real.log x := by
          rw [Real.log_rpow]
          all_goals linarith
        have h6 : Real.log (y^y) = y * Real.log y := by
          rw [Real.log_rpow]
          all_goals linarith
        rw [h4, h5, h6]
      have h7 : x ^ x * y ^ y = Real.exp (Real.log (x ^ x * y ^ y)) := by
        rw [Real.exp_log]
        all_goals positivity
      rw [h7, h3]
    have h8 : x ^ y * y ^ x = Real.exp (y * Real.log x + x * Real.log y) := by
      have h9 : Real.log (x ^ y * y ^ x) = y * Real.log x + x * Real.log y := by
        have h10 : Real.log (x ^ y * y ^ x) = Real.log (x^y) + Real.log (y^x) := by
          rw [Real.log_mul (by positivity) (by positivity)]
        have h11 : Real.log (x^y) = y * Real.log x := by
          rw [Real.log_rpow]
          all_goals linarith
        have h12 : Real.log (y^x) = x * Real.log y := by
          rw [Real.log_rpow]
          all_goals linarith
        rw [h10, h11, h12]
      have h13 : x ^ y * y ^ x = Real.exp (Real.log (x ^ y * y ^ x)) := by
        rw [Real.exp_log]
        all_goals positivity
      rw [h13, h9]
    have h10 : x * Real.log x + y * Real.log y ≥ y * Real.log x + x * Real.log y := by
      have h11 : (x - y) * (Real.log x - Real.log y) ≥ 0 := by
        by_cases h : x ≥ y
        · -- If x ≥ y, then Real.log x ≥ Real.log y because Real.log is monotone
          have h12 : Real.log x ≥ Real.log y := by
            apply Real.log_le_log
            all_goals linarith
          have h13 : x - y ≥ 0 := by linarith
          have h14 : Real.log x - Real.log y ≥ 0 := by linarith
          nlinarith
        · -- If x < y, then Real.log x < Real.log y
          have h15 : Real.log x < Real.log y := by
            apply Real.log_lt_log
            all_goals linarith
          have h16 : x - y < 0 := by linarith
          have h17 : Real.log x - Real.log y < 0 := by linarith
          nlinarith 
      linarith
    have h11 : Real.exp (x * Real.log x + y * Real.log y) ≥ Real.exp (y * Real.log x + x * Real.log y) := by
      apply Real.exp_le_exp_of_le
      linarith [h10]
    rw [h2, h8]
    linarith [h11]
  linarith