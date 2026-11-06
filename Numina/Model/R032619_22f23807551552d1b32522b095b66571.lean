import Mathlib

open Real

theorem algebra_328114 : sqrt (3 + sqrt (5 - sqrt (13 + sqrt (48)))) / (sqrt 6 + sqrt 2) = 1 / 2 := by
  have h1 : sqrt (48) = 4 * sqrt 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h2 : sqrt (13 + sqrt 48) = 2 * sqrt 3 + 1 := by
    rw [h1]
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 3, sq_nonneg (sqrt 3 - 1), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
  
  have h3 : sqrt (5 - sqrt (13 + sqrt 48)) = sqrt 3 - 1 := by
    rw [h2]
    have h6 : 5 - (2 * sqrt 3 + 1) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      all_goals nlinarith
    have h7 : (sqrt 3 - 1) ^ 2 = 4 - 2 * sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      all_goals nlinarith
    have h8 : 5 - (2 * sqrt 3 + 1) = 4 - 2 * sqrt 3 := by
      nlinarith
      all_goals nlinarith
    have h9 : 4 - 2 * sqrt 3 = (sqrt 3 - 1) ^ 2 := by
      linarith [h7]
    rw [h8, h9]
    have h12 : sqrt ((sqrt 3 - 1) ^ 2) = sqrt 3 - 1 := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg]
      have hk2 : sqrt 3 ≥ 1 := by
        have hk1 : sqrt 3 ≥ sqrt 1 := Real.sqrt_le_sqrt (by norm_num)
        have hk3 : sqrt 1 = 1 := Real.sqrt_one
        nlinarith [hk1, hk3]
      nlinarith [Real.sqrt_nonneg 3]
    rw [h12]
    all_goals nlinarith [Real.sqrt_nonneg 3]
  
  have h4 : sqrt (3 + sqrt (5 - sqrt (13 + sqrt 48))) = (1 + sqrt 3) / sqrt 2 := by
    rw [h3]
    have : 3 + (sqrt 3 - 1) = 2 + sqrt 3 := by ring_nf
    rw [this]
    have h5 : sqrt (2 + sqrt 3) = (1 + sqrt 3) / sqrt 2 := by
      have h10 : (1 + sqrt 3) / sqrt 2 ≥ 0 := by positivity
      have h11 : sqrt (2 + sqrt 3) = (1 + sqrt 3) / sqrt 2 := by
        have h14 : ((1 + sqrt 3) / sqrt 2) ^ 2 = 2 + sqrt 3 := by
          have h15 : (1 + sqrt 3) ^ 2 = 4 + 2 * sqrt 3 := by
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          calc
            ((1 + sqrt 3) / sqrt 2) ^ 2 = ((1 + sqrt 3) ^ 2) / (sqrt 2) ^ 2 := by ring_nf
            _ = (4 + 2 * sqrt 3) / (sqrt 2) ^ 2 := by rw [h15]
            _ = (4 + 2 * sqrt 3) / (2 : ℝ) := by
              have h16 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
              rw [h16]
              all_goals linarith
            _ = 2 + sqrt 3 := by
              linarith
              all_goals linarith
        have h17 : sqrt (((1 + sqrt 3) / sqrt 2) ^ 2) = ((1 + sqrt 3) / sqrt 2) := by
          rw [Real.sqrt_sq]
          all_goals linarith [h10]
          all_goals nlinarith
        have h18 : sqrt (2 + sqrt 3) = sqrt (((1 + sqrt 3) / sqrt 2) ^ 2) := by
          rw [h14]
        rw [h18, h17]
      exact h11
    rw [h5]
  
  have h5 : sqrt 6 = sqrt 2 * sqrt 3 := by
    calc
      Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num
      _ = Real.sqrt 2 * Real.sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]
  
  have h6 : sqrt 6 + Real.sqrt 2 = Real.sqrt 2 * (sqrt 3 + 1) := by
    rw [h5]
    ring_nf
  
  rw [h4, h6]
  field_simp
  <;> ring_nf <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  all_goals linarith