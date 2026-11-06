import Mathlib

theorem algebra_183552 {a b : ℝ} (ha : 0 < b) (hb : b < a)
    (h : a^2 + b^2 = 6 * a * b) : (a + b) / (a - b) = Real.sqrt 2 := by
  have ha_pos : 0 < a := by nlinarith
  have h1 : 0 < a - b := by nlinarith
  have h2 : (a + b) ^ 2 = 8 * a * b := by
    nlinarith
  have h3 : (a - b) ^ 2 = 4 * a * b := by
    nlinarith
  have h4 : a + b = Real.sqrt (8 * a * b) := by
    rw [←h2]
    field_simp [ha_pos, ha, h1]
  have h5 : a - b = Real.sqrt (4 * a * b) := by
    rw [←h3]
    field_simp [ha_pos, ha, h1]
  calc
    (a + b) / (a - b)
        = Real.sqrt (8 * a * b) / Real.sqrt (4 * a * b) := by rw [h4, h5]
    _ = Real.sqrt (8 * a * b / (4 * a * b)) := by 
      rw [Real.sqrt_div]
      all_goals nlinarith
    _ = Real.sqrt (8 / 4) := by
      field_simp [ha_pos, ha, h1]
      all_goals nlinarith
    _ = Real.sqrt 2 := by norm_num