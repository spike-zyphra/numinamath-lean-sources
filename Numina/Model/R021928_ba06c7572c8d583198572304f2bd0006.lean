import Mathlib

theorem algebra_303017 {a : ℝ} (ha : 0 ≤ a) (h : Real.sqrt (1 + Real.sqrt (1 + a)) = a ^ ((1 : ℝ) / 3)) :
    a = 8 := by
  have h1 : Real.sqrt (1 + Real.sqrt (1 + a)) ≥ 0 := by positivity
  have h2 : a ^ ((1 : ℝ) / 3) ≥ 0 := by positivity
  have h_eq1 : (Real.sqrt (1 + Real.sqrt (1 + a))) ^ 2 = 1 + Real.sqrt (1 + a) := Real.sq_sqrt (show 0 ≤ (1 + Real.sqrt (1 + a) : ℝ) by positivity)
  have h_eq2 : (a ^ ((1 : ℝ) / 3)) ^ 3 = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h_eq6 : 1 + Real.sqrt (1 + a) = (a ^ ((1 : ℝ) / 3)) ^ 2 := by
    have h_eq5 : (Real.sqrt (1 + Real.sqrt (1 + a))) ^ 2 = (a ^ ((1 : ℝ) / 3)) ^ 2 := by 
      rw [h]
    nlinarith [h_eq1, h_eq5]
  have h_eq7 : Real.sqrt (1 + a) = (a ^ ((1 : ℝ) / 3)) ^ 2 - 1 := by 
    nlinarith [h_eq6]
  have h_eq9 : 1 + a = ((a ^ ((1 : ℝ) / 3)) ^ 2 - 1) ^ 2 := by
    have h11 : (Real.sqrt (1 + a)) ^ 2 = 1 + a := by 
      rw [Real.sq_sqrt]
      nlinarith
    have h12 : Real.sqrt (1 + a) = (a ^ ((1 : ℝ) / 3)) ^ 2 - 1 := h_eq7
    rw [h12] at h11
    nlinarith [h11]
  have h_eq10 : (a ^ ((1 : ℝ) / 3)) ^ 2 * ( (a ^ ((1 : ℝ) / 3) ) - 2 ) * ( (a ^ ((1 : ℝ) / 3) ) + 1 ) = 0 := by
    nlinarith [sq_nonneg (a ^ ((1 : ℝ) / 3) - 2), sq_nonneg (a ^ ((1 : ℝ) / 3) + 1), sq_nonneg ( (a ^ ((1 : ℝ) / 3)) ^ 2 - 4 ), sq_nonneg ( (a ^ ((1 : ℝ) / 3) ) ^ 3 - 8 ), sq_nonneg ( (a ^ ((1 : ℝ) / 3) ) - 0 ), sq_nonneg ( a - 0 ), Real.rpow_nonneg (show 0 ≤ a by linarith) (1 / 3 : ℝ) ]
  cases' (mul_eq_zero.mp h_eq10) with h_eq11 h_eq12
  · cases' (mul_eq_zero.mp h_eq11) with h_eq13 h_eq14
    · -- If (a ^ (1/3)) ^2 =0, then a =0, which do not satisfy h
      have h03 : (a ^ ((1 : ℝ) / 3)) ^ 2 = 0 := by 
        nlinarith
      have h04 : a ^ ((1 : ℝ) / 3) = 0 := by 
        nlinarith [h03]
      -- This leads to a=0 at which h contradicts positivity of sqrt 2
      have h05 : a = 0 := by
        have h06 : (a ^ ((1 : ℝ) / 3)) ^ 3 = 0 := by 
          rw [show a ^ ((1 : ℝ) / 3) = (0 : ℝ) by nlinarith [h04] ]
          norm_num
        nlinarith [h_eq2, h06]
      -- Original h which is sqrt1+sqrt1= 1=0. This is contradiction
      nlinarith [h, h04, Real.sqrt_nonneg (1 + Real.sqrt (1 + a)), Real.sqrt_nonneg (1 + a), Real.sq_sqrt (show (1 + a : ℝ) ≥ 0 by linarith), Real.sq_sqrt (show (1 + Real.sqrt (1 + a) : ℝ) ≥ 0 by positivity)]
    · -- If ((a ^ (1/3)) ) - 2 = 0, then a =8, which satisfy h
      have h06 : a ^ ((1 : ℝ) / 3) = 2 := by 
        nlinarith
      have h07 : a = 8 := by 
        have h08 : (a ^ ((1 : ℝ) / 3)) ^ 3 = 8 := by 
          rw [h06]
          norm_num
        nlinarith [h_eq2, h08]
      linarith [h07]
  · -- If ((a ^ (1/3)) ) + 1 = 0, then a = -1, which contradicts a≥0 from ha
    have h08 : a ^ ((1 : ℝ) / 3) = -1 := by 
      nlinarith
    have h09 : a = -1 := by 
      have h10 : (a ^ ((1 : ℝ) / 3)) ^ 3 = -1 := by 
        rw [h08]
        norm_num
      nlinarith [h_eq2, h10]
    nlinarith