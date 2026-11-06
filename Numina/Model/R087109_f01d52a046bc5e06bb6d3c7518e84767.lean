import Mathlib

theorem algebra_218318 : 1 / Real.tan (Real.arctan (1 / 2) + Real.arctan (1 / 3) + Real.arctan (1 / 4) + Real.arctan (1 / 5)) = 5 / 14 := by
  have h1 : Real.arctan (1 / 2) + Real.arctan (1 / 3) = Real.pi / 4 := by
    have h2 : Real.arctan (1 / 2) + Real.arctan (1 / 3) = Real.arctan (1) := by
      rw [Real.arctan_add]
      norm_num
      all_goals norm_num
    rw [h2]
    norm_num [Real.arctan_one]
  have h3 : Real.pi / 4 + Real.arctan (1 / 4) = Real.arctan (5 / 3) := by
    have h4 : Real.pi / 4 = Real.arctan (1 : ℝ) := by
      norm_num [Real.arctan_one]
    rw [h4]
    rw [Real.arctan_add]
    norm_num
    all_goals norm_num
  have h5 : Real.arctan (5 / 3) + Real.arctan (1 / 5) = Real.arctan (14 / 5 : ℝ) := by
    rw [Real.arctan_add]
    norm_num
    all_goals norm_num
  have h6 : Real.arctan (1 / 2) + Real.arctan (1 / 3) + Real.arctan (1 / 4) + Real.arctan (1 / 5) = Real.arctan (14 / 5 : ℝ) := by
    linarith [h1, h3, h5]
  rw [h6]
  have h7 : Real.tan (Real.arctan (14 / 5 : ℝ)) = (14 / 5 : ℝ) := by
    rw [Real.tan_arctan]
  rw [h7]
  all_goals norm_num