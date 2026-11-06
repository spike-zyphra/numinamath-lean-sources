import Mathlib

theorem algebra_95896 (a b c d : ℝ) (ha : (4 : ℝ) ^ a = 5) (hb : (5 : ℝ) ^ b = 6)
    (hc : (6 : ℝ) ^ c = 7) (hd : (7 : ℝ) ^ d = 8) : a * b * c * d = 3 / 2 := by

  have ha2 : a = Real.logb 4 5 := by
    rw [←ha]
    field_simp [Real.logb_eq_iff_rpow_eq]
    all_goals linarith

  have hb2 : b = Real.logb 5 6 := by
    rw [←hb]
    field_simp [Real.logb_eq_iff_rpow_eq]
    all_goals linarith
  
  have hc2 : c = Real.logb 6 7 := by
    rw [←hc]
    field_simp [Real.logb_eq_iff_rpow_eq]
    all_goals linarith
  
  have hd2 : d = Real.logb 7 8 := by
    rw [←hd]
    field_simp [Real.logb_eq_iff_rpow_eq]
    all_goals linarith
  
  rw [ha2, hb2, hc2, hd2]

  have h1 : Real.logb 4 5 = Real.log 5 / Real.log 4 := by
    field_simp [Real.logb]

  have h2 : Real.logb 5 6 = Real.log 6 / Real.log 5 := by
    field_simp [Real.logb]

  have h3 : Real.logb 6 7 = Real.log 7 / Real.log 6 := by
    field_simp [Real.logb]

  have h4 : Real.logb 7 8 = Real.log 8 / Real.log 7 := by
    field_simp [Real.logb]

  rw [h1, h2, h3, h4]

  have h5 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
    simp [Real.log_pow]
    all_goals linarith

  have h6 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    simp [Real.log_pow]
    all_goals linarith
  
  have h7 : Real.log 5 / Real.log 4 * (Real.log 6 / Real.log 5) = Real.log 6 / Real.log 4 := by
    field_simp [show Real.log 4 ≠ 0 by
      positivity
     , show Real.log 5 ≠ 0 by
        positivity
     ]
    <;> ring

  have h8 : Real.log 6 / Real.log 4 * (Real.log 7 / Real.log 6) = Real.log 7 / Real.log 4 := by
    field_simp [show Real.log 4 ≠ 0 by
      positivity
     , show Real.log 6 ≠ 0 by
        positivity
     ]
    <;> ring

  have h9 : Real.log 7 / Real.log 4 * (Real.log 8 / Real.log 7) = Real.log 8 / Real.log 4 := by
    field_simp [show Real.log 4 ≠ 0 by
      positivity
     , show Real.log 7 ≠ 0 by
        positivity
     ]
    <;> ring

  have h_total : Real.log 5 / Real.log 4 * (Real.log 6 / Real.log 5) * (Real.log 7 / Real.log 6) * (Real.log 8 / Real.log 7) = Real.log 8 / Real.log 4 := by
    calc
      Real.log 5 / Real.log 4 * (Real.log 6 / Real.log 5) * (Real.log 7 / Real.log 6) * (Real.log 8 / Real.log 7)
          = (Real.log 5 / Real.log 4 * (Real.log 6 / Real.log 5)) * (Real.log 7 / Real.log 6) * (Real.log 8 / Real.log 7) := by ring
      _ = (Real.log 6 / Real.log 4) * (Real.log 7 / Real.log 6) * (Real.log 8 / Real.log 7) := by rw [h7]
      _ = (Real.log 6 / Real.log 4 * (Real.log 7 / Real.log 6)) * (Real.log 8 / Real.log 7) := by ring
      _ = (Real.log 7 / Real.log 4) * (Real.log 8 / Real.log 7) := by rw [h8]
      _ = Real.log 8 / Real.log 4 := by rw [h9]

  rw [h_total]

  rw [h5, h6]

  have h8 : Real.log 2 ≠ 0 := by
    positivity
  
  field_simp [h8]
  <;> ring