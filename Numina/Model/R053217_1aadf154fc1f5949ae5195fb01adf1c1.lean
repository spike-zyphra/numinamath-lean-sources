import Mathlib

theorem algebra_297195
    (a b : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (h1 : Real.logb 8 a + Real.logb 4 (b ^ 2) = 5)
    (h2 : Real.logb 8 b + Real.logb 4 (a ^ 2) = 7) :
    Real.logb 4 a + Real.logb 8 b = 4 := by

  have h1' : Real.logb 8 a = Real.logb 2 a / 3 := by
    have h1a : Real.logb 8 a = Real.logb 2 a / Real.logb 2 8 := by
      field_simp [Real.logb]
    have h1b : Real.logb 2 8 = 3 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
      <;> linarith
    rw [h1a, h1b]

  have h1'' : Real.logb 4 (b ^ 2) = Real.logb 2 b := by
    have h4a : Real.logb 4 (b ^ 2) = (Real.logb 2 (b ^ 2)) / Real.logb 2 4 := by
      field_simp [Real.logb]
    have h4b : Real.logb 2 (b ^ 2) = 2 * Real.logb 2 b := by
      simp [Real.logb_pow]
    have h4c : Real.logb 2 4 = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
      <;> linarith
    rw [h4a, h4b, h4c]
    all_goals linarith

  have h2' : Real.logb 8 b = Real.logb 2 b / 3 := by
    have h2a : Real.logb 8 b = Real.logb 2 b / Real.logb 2 8 := by
      field_simp [Real.logb]
    have h2b : Real.logb 2 8 = 3 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
      <;> linarith
    rw [h2a, h2b]

  have h2'' : Real.logb 4 (a ^ 2) = Real.logb 2 a := by
    have h4a : Real.logb 4 (a ^ 2) = (Real.logb 2 (a ^ 2)) / Real.logb 2 4 := by
      field_simp [Real.logb]
    have h4b : Real.logb 2 (a ^ 2) = 2 * Real.logb 2 a := by
      simp [Real.logb_pow]
    have h4c : Real.logb 2 4 = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
      <;> linarith
    rw [h4a, h4b, h4c]
    all_goals linarith

  have eq1 : Real.logb 2 a / 3 + Real.logb 2 b = 5 := by
    rw [h1', h1''] at h1
    linarith

  have eq2 : Real.logb 2 a + Real.logb 2 b / 3 = 7 := by
    rw [h2', h2''] at h2
    linarith

  have h3 : Real.logb 2 a + 3 * Real.logb 2 b = 15 := by
    linarith [eq1]

  have h4 : 3 * Real.logb 2 a + Real.logb 2 b = 21 := by
    linarith [eq2]

  have h5 : Real.logb 2 a + Real.logb 2 b = 9 := by
    linarith [h3, h4]

  have hlog2b : Real.logb 2 b = 3 := by
    linarith [h3, h5]

  have hlog2a : Real.logb 2 a = 6 := by
    linarith [h5, hlog2b]

  have h3a : Real.logb 4 a = Real.logb 2 a / 2 := by
    have h4a : Real.logb 4 a = Real.logb 2 a / Real.logb 2 4 := by
      field_simp [Real.logb]
    have h4b : Real.logb 2 4 = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
      <;> linarith
    rw [h4a, h4b]

  have h1b : Real.logb 8 b = Real.logb 2 b / 3 := by
    have h2a : Real.logb 8 b = Real.logb 2 b / Real.logb 2 8 := by
      field_simp [Real.logb]
    have h2b : Real.logb 2 8 = 3 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
      <;> linarith
    rw [h2a, h2b]

  calc
    Real.logb 4 a + Real.logb 8 b = (Real.logb 2 a / 2) + (Real.logb 2 b / 3) := by
      rw [h3a, h1b]
    _ = (6 / 2) + (3 / 3) := by
      rw [hlog2a, hlog2b]
    _ = 3 + 1 := by norm_num
    _ = 4 := by norm_num