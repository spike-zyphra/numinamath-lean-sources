import Mathlib

theorem inequalities_143364 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a ^ 2 / b) + Real.sqrt (b ^ 2 / a) ≥ Real.sqrt a + Real.sqrt b := by 
  have h1 : Real.sqrt (a ^ 2 / b) = a / Real.sqrt b := by 
    have h2 : Real.sqrt (a ^ 2 / b) = Real.sqrt (a ^ 2) / Real.sqrt b := by 
      rw [← Real.sqrt_div (by positivity)]
    have h3 : Real.sqrt (a ^ 2) = a := by 
      rw [Real.sqrt_sq (by linarith)]
    rw [h3] at h2 
    linarith 
  have h4 : Real.sqrt (b ^ 2 / a) = b / Real.sqrt a := by 
    have h5 : Real.sqrt (b ^ 2 / a) = Real.sqrt (b ^ 2) / Real.sqrt a := by 
      rw [← Real.sqrt_div (by positivity)]
    have h6 : Real.sqrt (b ^ 2) = b := by 
      rw [Real.sqrt_sq (by linarith)]
    rw [h6] at h5 
    linarith 
  rw [h1, h4]
  have h14 : (a / Real.sqrt b + b / Real.sqrt a) ^ 2 ≥ (Real.sqrt a + Real.sqrt b) ^ 2 := by 
    have h17 : ( (a / Real.sqrt b + b / Real.sqrt a) ) ^ 2 = 
        (a / Real.sqrt b) ^ 2 + (b / Real.sqrt a) ^ 2 + 2 * ((a / Real.sqrt b) * (b / Real.sqrt a)) := by 
        ring
    have h18 : (Real.sqrt a + Real.sqrt b) ^ 2 = Real.sqrt a ^ 2 + Real.sqrt b ^ 2 + 2 * (Real.sqrt a * Real.sqrt b) := by 
      ring 
    rw [h17, h18] 
    have h105 : (a / Real.sqrt b) ^ 2 = a^2 / b := by 
      have h11 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith) 
      field_simp [h11] 
      all_goals nlinarith 
    have h107 : (b / Real.sqrt a) ^ 2 = b^2 / a := by 
      have h11 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith) 
      field_simp [h11] 
      all_goals nlinarith 
    rw [h105, h107] 
    have h18 : a^2 / b + b^2 / a ≥ a + b := by 
      have h181 : a^2 / b + b^2 / a - (a + b) ≥ 0 := by 
        have h181 : a^2 / b + b^2 / a - (a + b) = (a - b) ^ 2 * (a + b) / (a * b) := by 
          field_simp 
          ring 
        rw [h181] 
        have h21 : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b) 
        have h1 : a * b > 0 := mul_pos ha hb 
        have h22 : (a + b) > 0 := by linarith 
        have h23 : (a - b) ^ 2 * (a + b) / (a * b) ≥ 0 := by 
          apply div_nonneg 
          nlinarith 
          positivity 
        linarith 
      linarith 
    have h19 : 2 * ( (a / Real.sqrt b) * (b / Real.sqrt a) ) = 2 * (Real.sqrt a * Real.sqrt b) := by 
      have h13 : ( (a / Real.sqrt b) * (b / Real.sqrt a) ) = Real.sqrt a * Real.sqrt b := by 
        have h121 : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb 
        have h122 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha 
        field_simp 
        <;> 
        have h32 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by positivity) 
        have h41 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by positivity) 
        nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg a, Real.sqrt_nonneg b] 
      nlinarith 
    have h22 : Real.sqrt a ^2 = a := Real.sq_sqrt (by linarith) 
    have h222 : Real.sqrt b ^2 = b := Real.sq_sqrt (by linarith) 
    nlinarith [h18, h19, h22, h222] 
  have h15 : a / Real.sqrt b + b / Real.sqrt a ≥ 0 := by 
    have h16 : Real.sqrt b > 0 := by positivity 
    have h17 : Real.sqrt a > 0 := by positivity 
    have h18 : a / Real.sqrt b ≥ 0 := by positivity 
    have h19 : b / Real.sqrt a ≥ 0 := by positivity 
    linarith 
  have h16 : Real.sqrt a + Real.sqrt b ≥ 0 := by 
    have h17 : Real.sqrt a ≥ 0 := Real.sqrt_nonneg a 
    have h18 : Real.sqrt b ≥ 0 := Real.sqrt_nonneg b 
    linarith 
  nlinarith [h14, h15, h16, Real.sqrt_nonneg a, Real.sqrt_nonneg b]