import Mathlib

theorem algebra_145852 (x : ℝ) : 0.125 * 4^(2*x - 3) = (Real.sqrt 2 / 8)^(-x) ↔ x = 6 := by
  constructor
  · -- Forward direction: assume 0.125 * 4^(2*x - 3) = (Real.sqrt 2 / 8)^(-x), prove x = 6
    intro h
    have h1 : (4 : ℝ) ^ (2 * x - 3) = (2 : ℝ) ^ (4 * x - 6) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      norm_num
      all_goals linarith
    have h2 : (0.125 : ℝ) * (4 : ℝ) ^ (2 * x - 3) = (2 : ℝ) ^ (4 * x - 9) := by
      rw [h1]
      have h3 : (0.125 : ℝ) = (2 : ℝ) ^ (-3 : ℝ) := by
        norm_num [Real.rpow_intCast]
      rw [h3]
      have h4 : ((2 : ℝ) ^ (-3 : ℝ)) * ((2 : ℝ) ^ (4 * x - 6 : ℝ)) = (2 : ℝ) ^ ((-3 + (4 * x - 6)) : ℝ) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals norm_num
      rw [h4]
      ring_nf
      all_goals norm_num
    have h5 : (Real.sqrt 2 / 8 : ℝ) ^ (-x : ℝ) = (2 : ℝ) ^ ((5 / 2) * x : ℝ) := by
      have h6 : (Real.sqrt 2 / 8 : ℝ) = (2 : ℝ) ^ (-5 / 2 : ℝ) := by
        have h7 : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
        rw [h7]
        have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
        rw [h8]
        have h9 : ((2 : ℝ) ^ (1 / 2 : ℝ)) / ((2 : ℝ) ^ (3 : ℝ)) = (2 : ℝ) ^ ((1 / 2 - 3) : ℝ) := by
          rw [← Real.rpow_sub]
          ring_nf
          all_goals norm_num
        rw [h9]
        ring_nf
        all_goals norm_num
      rw [h6]
      have h10 : ((2 : ℝ) ^ (-5 / 2 : ℝ)) ^ (-x : ℝ) = (2 : ℝ) ^ ((-5 / 2 * (-x)) : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
        all_goals linarith
      rw [h10]
      ring_nf
      all_goals norm_num
      all_goals linarith
    rw [h2] at h
    rw [h5] at h
    have h6 : (4 * x - 9 : ℝ) = (5 / 2 * x : ℝ) := by
      apply_fun (Real.logb (2 : ℝ)) at h
      simp at h ⊢
      all_goals linarith
    linarith
  · -- Reverse direction: assume x = 6, prove 0.125 * 4^(2*x - 3) = (Real.sqrt 2 / 8)^(-x)
    intro h
    rw [h]
    have h1 : (4 : ℝ) ^ (2 * (6 : ℝ) - 3) = (2 : ℝ) ^ (18 : ℝ) := by
      norm_num
      <;> ring_nf <;> norm_num
    have h2 : (0.125 : ℝ) * (4 : ℝ) ^ (2 * (6 : ℝ) - 3) = (2 : ℝ) ^ (15 : ℝ) := by
      rw [h1]
      norm_num
      <;> ring_nf <;> norm_num
    have h3 : (Real.sqrt 2 / 8 : ℝ) ^ (-6 : ℝ) = (2 : ℝ) ^ (15 : ℝ) := by
      have h4 : (Real.sqrt 2 / 8 : ℝ) = (2 : ℝ) ^ (-5 / 2 : ℝ) := by
        have h7 : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
        rw [h7]
        have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
        rw [h8]
        have h9 : ((2 : ℝ) ^ (1 / 2 : ℝ)) / ((2 : ℝ) ^ (3 : ℝ)) = (2 : ℝ) ^ ((1 / 2 - 3) : ℝ) := by
          rw [← Real.rpow_sub]
          ring_nf
          all_goals norm_num
        rw [h9]
        ring_nf
        all_goals norm_num
      rw [h4]
      have h5 : ((2 : ℝ) ^ (-5 / 2 : ℝ)) ^ (-6 : ℝ) = (2 : ℝ) ^ ((-5 / 2 * (-6)) : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
        all_goals linarith
      rw [h5]
      norm_num
      <;> ring_nf <;> norm_num
    rw [h2]
    rw [h3]