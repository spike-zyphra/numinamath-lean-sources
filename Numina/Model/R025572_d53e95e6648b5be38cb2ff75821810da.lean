import Mathlib

theorem algebra_184914 : ((2 / (Real.sqrt 3 - 1) + 3 / (Real.sqrt 3 - 2) + 15 / (3 - Real.sqrt 3)) * (Real.sqrt 3 + 5)⁻¹) = 1 / 2 := by
  have h1 : Real.sqrt 3 > 0 := by
    apply Real.sqrt_pos.mpr
    all_goals norm_num

  have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

  have h3 : Real.sqrt 3 - 1 ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]

  have h4 : Real.sqrt 3 - 2 ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]

  have h5 : (3 : ℝ) - Real.sqrt 3 ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]

  have eq1 : (2 / (Real.sqrt 3 - 1) : ℝ) = Real.sqrt 3 + 1 := by
    field_simp [(show Real.sqrt 3 - 1 ≠ 0 by assumption)]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]

  have eq2 : (3 / (Real.sqrt 3 - 2) : ℝ) = -3 * (Real.sqrt 3 + 2) := by
    field_simp [(show Real.sqrt 3 - 2 ≠ 0 by assumption)]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]

  have eq3 : (15 / (3 - Real.sqrt 3) : ℝ) = (15 + 5 * Real.sqrt 3) / 2 := by
    have h5' : (3 - Real.sqrt 3 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
    field_simp [h5']
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]

  have eq4 : (2 / (Real.sqrt 3 - 1) + 3 / (Real.sqrt 3 - 2) + 15 / (3 - Real.sqrt 3) : ℝ) = (Real.sqrt 3 + 5) / 2 := by
    rw [eq1, eq2, eq3]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]

  rw [eq4]
  field_simp [(show Real.sqrt 3 + 5 ≠ 0 by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
  )
  ]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
  all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]