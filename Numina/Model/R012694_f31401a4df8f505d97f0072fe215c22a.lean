import Mathlib

theorem algebra_148244 (m : ℝ) (hm : m > 1) :
    (m ^ (0.5 : ℝ)) / (Real.sqrt (m ^ (-3 / 4 : ℝ))) * (m ^ (1 / 8 : ℝ)) = m := by
  have h1 : Real.sqrt (m ^ (-3 / 4 : ℝ)) = m ^ (-3 / 8 : ℝ) := by
    have h2 : Real.sqrt (m ^ (-3 / 4 : ℝ)) = (m ^ (-3 / 4 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    rw [h2]
    rw [← Real.rpow_mul]
    norm_num
    all_goals linarith
  rw [h1]
  have h3 : (m ^ (0.5 : ℝ)) / (m ^ (-3 / 8 : ℝ)) * (m ^ (1 / 8 : ℝ)) = m := by
    have h4 : (m ^ (0.5 : ℝ)) / (m ^ (-3 / 8 : ℝ)) = m ^ (7 / 8 : ℝ) := by
      have h5 : (m ^ (0.5 : ℝ)) / (m ^ (-3 / 8 : ℝ)) = m ^ (0.5 : ℝ) * (m ^ (-3 / 8 : ℝ))⁻¹ := by
        field_simp
      rw [h5]
      have h6 : m ^ (0.5 : ℝ) * (m ^ (-3 / 8 : ℝ))⁻¹ = m ^ (0.5 : ℝ) * m ^ (3 / 8 : ℝ) := by
        have h7 : (m ^ (-3 / 8 : ℝ))⁻¹ = m ^ (3 / 8 : ℝ) := by
          rw [← Real.rpow_neg]
          norm_num
          all_goals linarith
        rw [h7]
      rw [h6]
      have h8 : m ^ (0.5 : ℝ) * m ^ (3 / 8 : ℝ) = m ^ (7 / 8 : ℝ) := by
        rw [← Real.rpow_add]
        norm_num
        all_goals linarith
      linarith
    rw [h4]
    have h5 : (m ^ (7 / 8 : ℝ)) * (m ^ (1 / 8 : ℝ)) = m ^ (1 : ℝ) := by
      rw [← Real.rpow_add]
      norm_num
      all_goals linarith
    rw [h5]
    norm_num
  exact h3