import Mathlib

theorem algebra_136499 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h₀ : a * b = 1) (h₁ : a ^ 2 + b ^ 2 = 4) :
    a ^ (-3 : ℤ) + b ^ (-3 : ℤ) = 3 * Real.sqrt 6 := by 
  have h2 : a + b = Real.sqrt 6 := by 
    have h3 : (a + b) ^ 2 = 6 := by 
      nlinarith 
    have h4 : 0 ≤ a + b := by 
      linarith 
    have h9 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have h10 : a + b = Real.sqrt 6 := by 
      nlinarith [Real.sqrt_nonneg 6] 
    linarith 
  have h3 : a ^ 3 + b ^ 3 = 3 * Real.sqrt 6 := by 
    have h4 : a ^ 3 + b ^ 3 = (a + b) ^ 3 - 3 * (a * b) * (a + b) := by 
      ring 
    rw [h4, h2, h₀]
    have h11 : (Real.sqrt 6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have h12 : (Real.sqrt 6 : ℝ) ^ 3 = (Real.sqrt 6) * 6 := by 
      calc 
        (Real.sqrt 6 : ℝ) ^ 3 = (Real.sqrt 6 : ℝ) * (Real.sqrt 6 : ℝ) ^ 2 := by ring
        _ = (Real.sqrt 6 : ℝ) * 6 := by rw [Real.sq_sqrt (by norm_num)]
    nlinarith [Real.sqrt_nonneg 6, Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num)]
  have h4 : a ^ 3 * b ^ 3 = 1 := by 
    calc 
      a ^ 3 * b ^ 3 = (a * b) ^ 3 := by ring 
      _ = (1) ^ 3 := by rw [h₀]
      _ = 1 := by norm_num
  have h5 : a ^ (-3 : ℤ) + b ^ (-3 : ℤ) = (a ^ 3 + b ^ 3) / (a ^ 3 * b ^ 3) := by
    simp [zpow_neg, zpow_ofNat]
    <;> field_simp [ha.ne.symm, hb.ne.symm]
    <;> ring 
  have h5' : a ^ (-3 : ℤ) + b ^ (-3 : ℤ) = 3 * Real.sqrt 6 := by 
    rw [h5] 
    rw [h3, h4]
    <;> ring 
  linarith [h5']