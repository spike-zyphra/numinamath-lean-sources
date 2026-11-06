import Mathlib

theorem inequalities_307767 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b = 1) :
    a ^ (b - 1) * b ^ (a - 1) ≤ 2 := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : a + b = 1 := h
  
  have h4 : a ^ (b - 1) * b ^ (a - 1) = (a ^ b * b ^ a) / (a * b) := by
    have ha_pos : 0 < a := ha
    have hb_pos : 0 < b := hb
    have h5 : a ^ (b - 1) = a ^ b / a := by
      field_simp [←Real.rpow_sub_one]
      all_goals linarith
    have h6 : b ^ (a - 1) = b ^ a / b := by
      field_simp [←Real.rpow_sub_one]
      all_goals linarith
    rw [h5, h6]
    field_simp [mul_ne_zero (ne_of_gt ha_pos) (ne_of_gt hb_pos)]
    all_goals linarith
  
  have h8 : a ^ b * b ^ a ≤ 2 * a * b := by
    have hw : b + a = 1 := by linarith [h3]
    have h9 : a ^ b * b ^ a ≤ b * a + a * b := by
      have h12 : a ^ b * b ^ a ≤ b * a + a * b := by
        apply Real.geom_mean_le_arith_mean2_weighted
        all_goals nlinarith [hw, Real.log_pos (show 1 < a + 1 by linarith), Real.log_pos (show 1 < b + 1 by linarith)]
      linarith 
    have h14 : b * a + a * b = 2 * a * b := by nlinarith
    linarith [h14, h9]

  rw [h4]
  have ha_pos : 0 < a * b := mul_pos ha hb
  apply (div_le_iff₀' (by positivity)).mpr
  linarith [h8]