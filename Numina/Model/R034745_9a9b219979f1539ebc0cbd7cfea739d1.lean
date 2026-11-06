import Mathlib

open Real

theorem algebra_211906 : sqrt 2 + (3 / (4 ^ ((1 : ℝ) / 3) - 2 ^ ((1 : ℝ) / 3) + 1) - 1)^3 - sqrt 2 / (2 + sqrt 2) = 3 := by
  have h1 : (4 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith
  have h2 : (4 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
    rw [h1]
    have h3 : (2 : ℝ) ^ ((2 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    linarith [h3]
  have h5 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals norm_num
  have h6 : (4 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 := by
    rw [h2]
  have h8 : 3 / ((4 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1) = (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 := by
    have h9 : (4 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 := h6
    rw [h9]
    have _x : (2: ℝ) ^ ((1 : ℝ) / 3) = (2: ℝ) ^ ((1 : ℝ) / 3) := rfl
    have hx3 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 2 := h5
    have eq1 : 3 / (((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1) = (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 := by
      have eq2 : ((2 : ℝ) ^ ((1 : ℝ) / 3) + 1) * (((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1) = 3 := by
        calc
          ((2 : ℝ) ^ ((1 : ℝ) / 3) + 1) * (((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1)
            = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 1 := by ring
          _ = 2 + 1 := by rw [hx3]
          _ = 3 := by norm_num
      field_simp [(show ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3)  + 1 ≠ 0 by
        by_contra h
        have h0 : ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3)  + 1 = (0 : ℝ) := by nlinarith
        have h8 : ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 = (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 := by linarith
        have hx1 : (2 : ℝ) ^ ((1 : ℝ) / 3) > 0 := by positivity
        nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (1 / 3), sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1), Real.rpow_nonneg (show 0 ≤ (2: ℝ) by norm_num) (1/3)]
      )]
      <;> nlinarith
    exact eq1
  have h9 : (3 / ( (4 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 )) - 1 = (2 : ℝ) ^ ((1 : ℝ) / 3) := by
    linarith [h8]
  have h10 : ((3 / ( (4 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 )) - 1) ^ 3 = (2 : ℝ) := by
    rw [h9]
    rw [show ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) by
      have h11 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals norm_num
      linarith [h11]
    ]
  have h11 : sqrt 2 / (2 + sqrt 2) = sqrt 2 - 1 := by
    have h10 : sqrt 2 > 0 := by
      positivity
    field_simp [(show (2 + sqrt 2 : ℝ) ≠ 0 by positivity), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
  rw [h10, h11]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]