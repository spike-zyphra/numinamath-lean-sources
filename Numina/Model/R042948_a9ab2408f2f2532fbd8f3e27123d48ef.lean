import Mathlib

theorem algebra_263196 {x : ℝ}
    (hx : x = (7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + 1 / (7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) :
    x^3 - 3 * x = 14 := by
  have h1 : 0 < (7 + 4 * Real.sqrt 3 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h2 : (7 + 4 * Real.sqrt 3 : ℝ) = ((2 + Real.sqrt 3) ^ 2 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h55 : ((7 + 4 * Real.sqrt 3 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 = (7 + 4 * Real.sqrt 3) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    norm_num
    all_goals positivity
  have h66 : ((7 + 4 * Real.sqrt 3 : ℝ) ^ (-(1 : ℝ) / 3) ) = 1 / ((7 + 4 * Real.sqrt 3 : ℝ) ^ ((1 : ℝ) / 3) ) := by
    rw [show ((7 + 4 * Real.sqrt 3) ^ (-(1 : ℝ) / 3) ) = ((7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) )⁻¹ by 
      rw [← Real.rpow_neg]
      norm_num
      all_goals positivity
    ]
    field_simp
  have h88 : (1 / ((7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) ) ) ^ 3 = (1 / (7 + 4 * Real.sqrt 3) ) := by
    calc
      (1 / (7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) ) ^ 3 = 1 / ( (7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) ) ^ 3 := by field_simp
      _ = 1 / (7 + 4 * Real.sqrt 3) := by 
        rw [h55] 
        <;> field_simp
        <;> positivity
  have h99 : (1 / (7 + 4 * Real.sqrt 3) ) = (7 - 4 * Real.sqrt 3 ) := by 
    have h999 : (7 + 4 * Real.sqrt 3 : ℝ) ≠ 0 := by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    field_simp [h999]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  rw [hx]
  have h776 : (((7 + 4 * Real.sqrt 3 : ℝ) ^ ((1 : ℝ) / 3) ) + (1 / ((7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) ) ) ) ^ 3 = ((7 + 4 * Real.sqrt 3 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 + (1 / ((7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) ) ) ^ 3 + 3 * (((7 + 4 * Real.sqrt 3 : ℝ) ^ ((1 : ℝ) / 3) ) * (1 / ((7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) ) ) * (((7 + 4 * Real.sqrt 3 : ℝ) ^ ((1 : ℝ) / 3) ) + (1 / ((7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) ) ) ) ) := by
    ring
  have h444 : ((7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) ) * (1 / ((7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) ) ) = 1 := by
    field_simp [show ((7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) ) ≠ 0 by positivity]
  rw [h776]
  rw [show ((7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) ) ^ 3 = (7 + 4 * Real.sqrt 3) by 
    linarith [h55]
  ]
  rw [show (1 / ((7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 3) ) ) ^ 3 = (7 - 4 * Real.sqrt 3) by 
      rw [h88, h99]
  ]
  rw [h444]
  nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]