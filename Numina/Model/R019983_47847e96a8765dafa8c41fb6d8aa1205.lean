import Mathlib

theorem inequalities_31369 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    (a ^ 3 + 1) / (a ^ 2 + 1) + (b ^ 3 + 1) / (b ^ 2 + 1) +
    (c ^ 3 + 1) / (c ^ 2 + 1) ≥
    (1 / 27) * (Real.sqrt (a * b) + Real.sqrt (b * c) + Real.sqrt (c * a)) ^ 4 := by

  have h1 : (a ^ 3 + 1) / (a ^ 2 + 1) ≥ (a + 1) / 2 := by
    apply (le_div_iff₀ (by nlinarith)).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a ^ 2 - 1), sq_nonneg (a + 1), mul_pos ha (show 0 < a by assumption)]
  
  have h2 : (b ^ 3 + 1) / (b ^ 2 + 1) ≥ (b + 1) / 2 := by
    apply (le_div_iff₀ (by nlinarith)).mpr
    nlinarith [sq_nonneg (b - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (b + 1), mul_pos hb (show 0 < b by assumption)]
  
  have h3 : (c ^ 3 + 1) / (c ^ 2 + 1) ≥ (c + 1) / 2 := by
    apply (le_div_iff₀ (by nlinarith)).mpr
    nlinarith [sq_nonneg (c - 1), sq_nonneg (c ^ 2 - 1), sq_nonneg (c + 1), mul_pos hc (show 0 < c by assumption)]

  have h4 : (a ^ 3 + 1) / (a ^ 2 + 1) + (b ^ 3 + 1) / (b ^ 2 + 1) + (c ^ 3 + 1) / (c ^ 2 + 1) ≥ 3 := by
    linarith [h1, h2, h3, h]

  have h5 : (Real.sqrt (a * b) + Real.sqrt (b * c) + Real.sqrt (c * a)) ^ 4 ≤ 81 := by
    have h6 : Real.sqrt (a * b) ≤ (a + b) / 2 := by
      have h7 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
        rw [Real.sqrt_mul (by nlinarith)]
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, sq_nonneg (Real.sqrt a - Real.sqrt b), 
          Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith)]
    
    have h8 : Real.sqrt (b * c) ≤ (b + c) / 2 := by
      have h9 : Real.sqrt (b * c) = Real.sqrt b * Real.sqrt c := by
        rw [Real.sqrt_mul (by nlinarith)]
      nlinarith [Real.sqrt_nonneg b, Real.sqrt_nonneg c, sq_nonneg (Real.sqrt b - Real.sqrt c), 
          Real.sq_sqrt (show 0 ≤ b by linarith), Real.sq_sqrt (show 0 ≤ c by linarith)]
    
    have h10 : Real.sqrt (c * a) ≤ (c + a) / 2 := by
      have h11 : Real.sqrt (c * a) = Real.sqrt c * Real.sqrt a := by
        rw [Real.sqrt_mul (by nlinarith)]
      nlinarith [Real.sqrt_nonneg c, Real.sqrt_nonneg a, sq_nonneg (Real.sqrt c - Real.sqrt a), 
          Real.sq_sqrt (show 0 ≤ c by linarith), Real.sq_sqrt (show 0 ≤ a by linarith)]
    
    have h7 : Real.sqrt (a * b) + Real.sqrt (b * c) + Real.sqrt (c * a) ≤ 3 := by
      nlinarith [h6, h8, h10, h]
    
    have h8 : (Real.sqrt (a * b) + Real.sqrt (b * c) + Real.sqrt (c * a)) ^ 4 ≤ (3 : ℝ) ^ 4 := by
      apply pow_le_pow_left
      all_goals 
        nlinarith [h7, Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (b * c), Real.sqrt_nonneg (c * a)]
    
    nlinarith
  nlinarith [h4, h5, h]