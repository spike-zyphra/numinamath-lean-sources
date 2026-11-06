import Mathlib

theorem algebra_224846 : (2 + (7 : ℝ) ^ ((1 : ℝ) / 3)) < (60 : ℝ) ^ ((1 : ℝ) / 3) := by
  have h1 : (2 + (7 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 < (60 : ℝ) := by
    let a := (7 : ℝ) ^ ((1 : ℝ) / 3)
    have ha1 : a ^ 3 = 7 := by
      rw [show a = (7 : ℝ) ^ ((1 : ℝ) / 3) by rfl]
      have h2 : ((7 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (7 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith
      norm_num at h2 ⊢
      linarith
    have h2 : (2 + a) ^ 3 = 15 + 12 * a + 6 * a ^ 2 := by
      ring_nf
      <;> nlinarith [ha1]
    have h3 : 15 + 12 * a + 6 * a ^ 2 < 60 := by
      nlinarith [sq_nonneg (a - (2 : ℝ)), sq_nonneg (a ^ 2 - (4 : ℝ)), 
        sq_nonneg (a + (1 : ℝ)), 
        show a > 0 by positivity, 
        show a ^ 2 > 0 by positivity, 
        ha1
      ]
    linarith [h2, h3]
  have h3 : (2 + (7 : ℝ) ^ ((1 : ℝ) / 3)) < (60 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h4 : ( (2 + (7 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 < (60 : ℝ) ) := h1
    have h6 : ( (60 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 = (60 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h9 : ( (2 + (7 : ℝ) ^ ((1 : ℝ) / 3) ) ) < ( (60 : ℝ) ^ ((1 : ℝ) / 3) ) := by
      nlinarith [h4, h6, Real.rpow_pos_of_pos (show 0 < (7 : ℝ) by norm_num) (1 / 3), Real.rpow_pos_of_pos (show 0 < (60 : ℝ) by norm_num) (1 / 3), sq_nonneg ( (2 + (7 : ℝ) ^ ((1 : ℝ) / 3) ) - (60 : ℝ) ^ ((1 : ℝ) / 3) ), sq_nonneg ( (2 + (7 : ℝ) ^ ((1 : ℝ) / 3) ) + (60 : ℝ) ^ ((1 : ℝ) / 3) ), sq_nonneg ( (2 + (7 : ℝ) ^ ((1 : ℝ) / 3) ) ), sq_nonneg ( (60 : ℝ) ^ ((1 : ℝ) / 3) ) ]
    linarith
  exact h3