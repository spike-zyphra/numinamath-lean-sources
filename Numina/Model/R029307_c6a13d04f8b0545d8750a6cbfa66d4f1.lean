import Mathlib
theorem algebra_275734 : (√(2 - √3) * (2 - √3) + √(2 + √3) * (2 + √3)) ^ 2 = 54:= by 
  have h1 : (√(2 - √3) * (2 - √3) + √(2 + √3) * (2 + √3)) ^ 2 =
      (√(2 - √3) * (2 - √3)) ^ 2 + (√(2 + √3) * (2 + √3)) ^ 2 + 2 * (√(2 - √3) * (2 - √3) * (√(2 + √3) * (2 + √3))) := by 
    ring 
  have h2 : (√(2 - √3) * (2 - √3)) ^ 2 = (2 - √3) ^ 3 := by
    calc
      (√(2 - √3) * (2 - √3)) ^ 2 = (√(2 - √3)) ^ 2 * ((2 - √3) ^ 2) := by 
        ring 
      _ = (2 - √3) * ((2 - √3) ^ 2) := by 
        have h11 : (√(2 - √3)) ^ 2 = (2 - √3) := by 
          rw [Real.sq_sqrt]
          have h111 : (2 - √3 : ℝ) ≥ 0 := by 
            nlinarith [Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (√3)]
          exact_mod_cast h111
        rw [h11]
      _ = (2 - √3) ^ 3 := by 
        ring 
  have h3 : (√(2 + √3) * (2 + √3)) ^ 2 = (2 + √3) ^ 3 := by 
    calc 
      (√(2 + √3) * (2 + √3)) ^ 2 = (√(2 + √3)) ^ 2 * ((2 + √3) ^ 2) := by 
        ring 
      _ = (2 + √3) * ((2 + √3) ^ 2) := by 
        have h12 : (√(2 + √3)) ^ 2 = (2 + √3) := by 
          rw [Real.sq_sqrt]
          have h111 : (2 + √3 : ℝ) ≥ 0 := by 
            nlinarith [Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (√3)]
          exact_mod_cast h111 
        rw [h12]
      _ = (2 + √3) ^ 3 := by 
        ring
  have h4 : √(2 - √3) * (2 - √3) * (√(2 + √3) * (2 + √3)) = 1 := by
    have h5 : √(2 - √3) * √(2 + √3) = 1 := by 
      have h51 : √(2 - √3) * √(2 + √3) = √((2 - √3) * (2 + √3)) := by 
        have hx1 : (2 - √3 : ℝ) ≥ 0 := by 
          nlinarith [Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (√3)]
        have hx2 : (2 + √3 : ℝ) ≥ 0 := by 
          nlinarith [Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (√3)]
        -- We need the first argument for sqrt_mul `X \ge 0` for `sqrt X`.
        -- `hx1` proves this.
        rw [← Real.sqrt_mul (by 
          exact_mod_cast hx1 
        )]
      rw [h51]
      have h52 : (2 - √3 : ℝ) * (2 + √3 : ℝ) = 1 := by 
        nlinarith [Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      rw [h52]
      norm_num [Real.sqrt_eq_iff_sq_eq]
    calc 
      √(2 - √3) * (2 - √3) * (√(2 + √3) * (2 + √3))
          = (√(2 - √3) * √(2 + √3)) * ((2 - √3) * (2 + √3)) := by 
            ring 
      _ = 1 * ((2 - √3) * (2 + √3)) := by 
        rw [h5] 
      _ = 1 * 1 := by 
        have h6 : (2 - √3 : ℝ) * (2 + √3 : ℝ) = 1 := by 
          nlinarith [Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        rw [h6]
      _ = 1 := by 
        ring
  rw [h1] 
  rw [h2, h3] 
  -- Apply h4's result
  have h6 : (2 - √3) ^ 3 + (2 + √3) ^ 3 + 2 * 1 = 54 := by
    nlinarith [Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (√3)]
  linarith [h6, h4]