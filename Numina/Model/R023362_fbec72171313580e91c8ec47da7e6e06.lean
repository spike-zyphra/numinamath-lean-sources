import Mathlib

theorem algebra_5032 : IsGreatest {x : ℝ | (x + 2) ^ ((1 : ℝ) / 3) = Real.sqrt (x + 11) - 3} 25 := by
  constructor
  · -- Show that 25 is in the set
    show (25 + 2) ^ ((1 : ℝ) / 3) = Real.sqrt (25 + 11) - 3
    have h1 : (25 + 2 : ℝ) ^ ((1 : ℝ) / 3) = 3 := by
      have h2 : (25 + 2 : ℝ) = 27 := by norm_num
      rw [h2]
      have h3 : (27 : ℝ) ^ ((1 : ℝ) / 3) = 3 := by
        rw [show (27 : ℝ) = 3 ^ (3 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      exact h3
    have h4 : Real.sqrt (25 + 11 : ℝ) = 6 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h4]
    all_goals norm_num
  · -- Show that 25 is the greatest
    intro x hx
    have h_eq : (x + 2 : ℝ) ^ ((1 : ℝ) / 3) = Real.sqrt (x + 11) - 3 := by
      simpa using hx
    by_contra h
    push_neg at h
    have h1 : x + 11 ≥ 0 := by
      by_contra h2
      push_neg at h2
      have h3 : x < -11 := by linarith
      have h4 : Real.sqrt (x + 11) = 0 := by
        rw [Real.sqrt_eq_zero']
        all_goals nlinarith
      have h5 : (x + 2 : ℝ) ^ ((1 : ℝ) / 3) = -3 := by
        linarith [h_eq, h4]
      have h6 : (x + 2 : ℝ) = -27 := by
        have h7 : (x + 2 : ℝ) ^ ((1 : ℝ) / 3) = -3 := by
          linarith [h5]
        have h8 : ((x + 2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = ( -3 : ℝ ) ^ 3 := by
          rw [h7]
        have h9 : ((x + 2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (x + 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
        have h10 : ( -3 : ℝ ) ^ 3 = -27 := by norm_num
        nlinarith [h9, h8, h10]
      nlinarith
    have h2 : Real.sqrt (x + 11) = (x + 2 : ℝ) ^ ((1 : ℝ) / 3) + 3 := by
      linarith [h_eq]
    have h3 : ((x + 2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 = x + 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h4 : (Real.sqrt (x + 11) : ℝ) ^ 2 = x + 11 := Real.sq_sqrt (show 0 ≤ x + 11 from by linarith)
    have h5 : ((x + 2 : ℝ) ^ ((1 : ℝ) / 3) + 3) ^ 2 = x + 11 := by
      have h7 : Real.sqrt (x + 11) = (x + 2 : ℝ) ^ ((1 : ℝ) / 3) + 3 := by
        linarith [h_eq]
      have h8 : (Real.sqrt (x + 11) : ℝ) ^ 2 = x + 11 := Real.sq_sqrt (show 0 ≤ x + 11 from by linarith)
      rw [h7] at h8
      linarith
    have h7 : x > (25 : ℝ) := h
    nlinarith [sq_nonneg ( ((x + 2 : ℝ) ^ ((1 : ℝ) / 3) ) - 3 ), sq_nonneg ( ((x + 2 : ℝ) ^ ((1 : ℝ) / 3) ) + 2 ), sq_nonneg ( ((x + 2 : ℝ) ^ ((1 : ℝ) / 3) ) ), sq_nonneg (Real.sqrt (x + 11) - 6), sq_nonneg (x - 25), Real.sqrt_nonneg (x + 11), Real.sq_sqrt (show 0 ≤ (x + 11 : ℝ) by linarith)]