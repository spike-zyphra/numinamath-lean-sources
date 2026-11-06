import Mathlib

theorem algebra_287409 : (7 + 5 * Real.sqrt 2) ^ ((1 : ℝ) / 3) -
    (5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3) = 2 := by
  have h1 : (7 + 5 * Real.sqrt 2) ^ ((1 : ℝ) / 3) = 1 + Real.sqrt 2 := by
    have h2 : (1 + Real.sqrt 2) ^ 3 = 7 + 5 * Real.sqrt 2 := by
      ring_nf
      have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h4 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
        calc
          Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
          _ = 2 * Real.sqrt 2 := by rw [h3]
      rw [h4]
      <;> nlinarith
      <;> norm_num
      <;> nlinarith [Real.sqrt_nonneg (2 : ℝ)]
    have h5 : (7 + 5 * Real.sqrt 2) = (1 + Real.sqrt 2) ^ 3 := by
      nlinarith [h2]
    rw [h5]
    have h6 : ((1 + Real.sqrt 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (1 + Real.sqrt 2) := by
      have h8 : ((1 + Real.sqrt 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (1 + Real.sqrt 2) := by
        have h11 : ((1 + Real.sqrt 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (1 + Real.sqrt 2) ^ (3 * (1 / 3 : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals nlinarith [Real.sqrt_nonneg 2]
        have h12 : (3 * (1 / 3 : ℝ) ) = (1 : ℝ) := by norm_num
        rw [h11]
        rw [h12]
        all_goals norm_num
        all_goals nlinarith [Real.sqrt_nonneg 2]
      nlinarith [h8]
    linarith [h6]
  have h7 : (5 * Real.sqrt 2 - 7 : ℝ) ^ ((1 : ℝ) / 3) = Real.sqrt 2 - 1 := by
    have h8 : (Real.sqrt 2 - 1) ^ 3 = 5 * Real.sqrt 2 - 7 := by
      ring_nf
      have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h4 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by 
        calc
          Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
          _ = 2 * Real.sqrt 2 := by rw [h3]
      rw [h4]
      <;> nlinarith [Real.sqrt_nonneg 2]
    have h_eq1 : (5 * Real.sqrt 2 - 7 : ℝ) ^ ((1 : ℝ) / 3) = ((Real.sqrt 2 - 1) ^ 3) ^ ((1 : ℝ) / 3) := by 
      have h_eq2_eq_pow : (5 * Real.sqrt 2 - 7 : ℝ) = (Real.sqrt 2 - 1) ^ 3 := by 
        linarith [h8]
      rw [h_eq2_eq_pow]
    have h4_nonneg : 0 ≤ Real.sqrt 2 - 1 := by
      have h5 : 1 < Real.sqrt 2 := by
        rw [Real.lt_sqrt] <;> norm_num
      linarith [h5]
    have h_eq3_eq_base : ((Real.sqrt 2 - 1) ^ 3) ^ ((1 : ℝ) / 3) = Real.sqrt 2 - 1 := by
      have h11 : ((Real.sqrt 2 - 1) ^ 3) ^ ((1 : ℝ) / 3) = (Real.sqrt 2 - 1) ^ (3 * (1 / 3 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf
        all_goals nlinarith [Real.sqrt_nonneg 2, h4_nonneg]
      have h12 : (3 * (1 / 3 : ℝ) ) = (1 : ℝ) := by norm_num
      rw [h11]
      rw [h12]
      all_goals norm_num
      all_goals nlinarith [Real.sqrt_nonneg 2, h4_nonneg]
    rw [h_eq1, h_eq3_eq_base]
    all_goals linarith [Real.sqrt_nonneg 2]
  rw [h1, h7]
  all_goals nlinarith [Real.sqrt_nonneg 2]
  all_goals nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]