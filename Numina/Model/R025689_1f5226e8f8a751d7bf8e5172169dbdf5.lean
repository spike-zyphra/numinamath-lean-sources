import Mathlib

theorem algebra_11393 (x : ℝ) (hx : x ≥ 0) :
    Real.sqrt (1 + Real.sqrt (2 + Real.sqrt x)) = (1 + Real.sqrt x) ^ ((1 : ℝ) / 3) ↔ x = 49 := by
  constructor
  · -- Assume $\sqrt{1 + \sqrt{2 + \sqrt{x}}} = \sqrt[3]{1 + \sqrt{x}}$ prove $x = 49$
    intro h_eq
    have h1 : 0 ≤ (1 + Real.sqrt (2 + Real.sqrt x) : ℝ) := by
      have h3 : Real.sqrt (2 + Real.sqrt x) ≥ 0 := Real.sqrt_nonneg (2 + Real.sqrt x)
      linarith
    have h2 : 0 ≤ (1 + Real.sqrt x : ℝ) := by
      have h4 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
      linarith
    have h_eq4 : (Real.sqrt (1 + Real.sqrt (2 + Real.sqrt x)) : ℝ) ^ 6 = ( (1 + Real.sqrt x : ℝ) ^ ((1 : ℝ) / 3) ) ^ 6 := by
      have h12 : (Real.sqrt (1 + Real.sqrt (2 + Real.sqrt x)) : ℝ) = ( (1 + Real.sqrt x : ℝ) ^ ((1 : ℝ) / 3) ) := by
        linarith [h_eq]
      rw [h12]
    have h_eq5 : (Real.sqrt (1 + Real.sqrt (2 + Real.sqrt x)) : ℝ) ^ 6 = (1 + Real.sqrt (2 + Real.sqrt x) ) ^ 3 := by
      have h10 : (Real.sqrt (1 + Real.sqrt (2 + Real.sqrt x)) : ℝ) ^ 2 = 1 + Real.sqrt (2 + Real.sqrt x) := by
        rw [Real.sq_sqrt]
        positivity
      have h11 : ( (Real.sqrt (1 + Real.sqrt (2 + Real.sqrt x)) : ℝ ) ^ 6 ) = ( (Real.sqrt (1 + Real.sqrt (2 + Real.sqrt x)) : ℝ ) ^ 2 ) ^ 3 := by ring
      rw [h11, h10]
    have h_eq6 : ( ( (1 + Real.sqrt x : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 6 = ( (1 + Real.sqrt x : ℝ) ) ^ 2 := by
      have h12 : ( ( (1 + Real.sqrt x : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 3 = (1 + Real.sqrt x : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith [show 0 ≤ (1 + Real.sqrt x : ℝ) by positivity]
      have h13 : ( ( (1 + Real.sqrt x : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 6 = ( ( ( (1 + Real.sqrt x : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 3 ) ^ 2 := by ring
      rw [h13, h12]
    have h_eq7 : (1 + Real.sqrt (2 + Real.sqrt x) ) ^ 3 = ( (1 + Real.sqrt x : ℝ) ) ^ 2 := by
      linarith [h_eq4, h_eq5, h_eq6]
    have h7 : Real.sqrt x = 7 := by 
      nlinarith [sq_nonneg (Real.sqrt (2 + Real.sqrt x) - 3), Real.sqrt_nonneg (2 + Real.sqrt x), 
        Real.sq_sqrt (show (2 + Real.sqrt x) ≥ 0 by positivity), sq_nonneg (Real.sqrt x - 7), 
          Real.sq_sqrt (show x ≥ 0 by assumption), Real.sqrt_nonneg x, Real.sqrt_nonneg (2 + Real.sqrt x), Real.sqrt_nonneg x]
    have h8 : x = 49 := by 
      calc 
        x = (Real.sqrt x) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = 7 ^ 2 := by 
          rw [h7]
        _ = 49 := by
          norm_num
    assumption
  · -- Assume x = 49 prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (1 + Real.sqrt (2 + Real.sqrt (49 : ℝ))) = (2 : ℝ) := by
      have h2 : Real.sqrt (49 : ℝ) = (7 : ℝ) := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3 : Real.sqrt (2 + (7 : ℝ)) = (3 : ℝ) := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h4 : Real.sqrt (1 + (3 : ℝ)) = (2 : ℝ) := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h2, h3, h4]
    have h2 : (1 + Real.sqrt (49 : ℝ) ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
      have h3 : Real.sqrt (49 : ℝ) = (7 : ℝ) := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h3]
      have h4 : (1 + (7 : ℝ) ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by 
        have h5 : (1 + (7 : ℝ) ) ^ ((1 : ℝ) / 3) = (8 : ℝ) ^ ((1 : ℝ) / 3) := by norm_num
        have h6 : (8 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by 
          have h7 : (8 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by 
            have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
            rw [h8]
            rw [← Real.rpow_mul]
            norm_num
            all_goals norm_num
          linarith [h7]
        rw [h5, h6]
      linarith [h4]
    rw [h1, h2]