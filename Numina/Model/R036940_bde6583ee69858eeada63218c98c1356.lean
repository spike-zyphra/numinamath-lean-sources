import Mathlib

theorem algebra_224154 : ¬Irrational ((20 + 14 * Real.sqrt 2) ^ ((1 : ℝ) / 3) + (20 - 14 * Real.sqrt 2) ^ ((1 : ℝ) / 3)) := by 
  have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  have h3 : (20 + 14 * Real.sqrt 2 : ℝ) = (Real.sqrt 2 + 2) ^ 3 := by
    ring_nf
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), h1, Real.sqrt_nonneg 2]
  have h4 : (20 - 14 * Real.sqrt 2 : ℝ) = (2 - Real.sqrt 2) ^ 3 := by
    ring_nf
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), h1, Real.sqrt_nonneg 2]
  have h5 : (20 + 14 * Real.sqrt 2 : ℝ) ^ ((1 : ℝ) / 3) = Real.sqrt 2 + 2 := by
    have h6 : (20 + 14 * Real.sqrt 2 : ℝ) = (Real.sqrt 2 + 2) ^ 3 := h3
    rw [h6]
    have h8 : ((Real.sqrt 2 + 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = Real.sqrt 2 + 2 := by
      have h9 : ((Real.sqrt 2 + 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = Real.sqrt 2 + 2 := by
        rw [show ((Real.sqrt 2 + 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (Real.sqrt 2 + 2 : ℝ) by
          have h11 : ((Real.sqrt 2 + 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (Real.sqrt 2 + 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), h1, Real.sqrt_nonneg 2]
          linarith
        ]
      linarith
    linarith
  have h6 : (20 - 14 * Real.sqrt 2 : ℝ) ^ ((1 : ℝ) / 3) = (2 - Real.sqrt 2 : ℝ) := by
    have h7 : (20 - 14 * Real.sqrt 2 : ℝ) = (2 - Real.sqrt 2) ^ 3 := h4
    rw [h7]
    have h10 : ((2 - Real.sqrt 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (2 - Real.sqrt 2 : ℝ) := by 
      have h11 : ((2 - Real.sqrt 2) ^ 3) ^ ((1 : ℝ) / 3) = (2 - Real.sqrt 2 : ℝ) := by
        rw [show ((2 - Real.sqrt 2) ^ 3) ^ ((1 : ℝ) / 3) = (2 - Real.sqrt 2 : ℝ) by
          have h12 : ((2 - Real.sqrt 2) ^ 3) ^ ((1 : ℝ) / 3) = (2 - Real.sqrt 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), h1, Real.sqrt_nonneg 2]
          linarith
        ]
      linarith
    linarith
  have h7 : (20 + 14 * Real.sqrt 2) ^ ((1 : ℝ) / 3) + (20 - 14 * Real.sqrt 2) ^ ((1 : ℝ) / 3) = (4 : ℝ) := by
    rw [h5, h6]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, h1]
  rw [show (20 + 14 * Real.sqrt 2 : ℝ) ^ ((1 : ℝ) / 3) + (20 - 14 * Real.sqrt 2) ^ ((1 : ℝ) / 3) = (4 : ℝ) by linarith [h7]
  ]
  simp