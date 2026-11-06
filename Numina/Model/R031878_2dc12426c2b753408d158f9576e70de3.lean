import Mathlib

theorem algebra_2147 {a b : ℝ} (h : 2 * a + b = 0) (hab : a ≠ 0 ∧ b ≠ 0) : |a / |b| - 1| + |(|a| / b) - 2| = 3 := by
  have h1 : b = -2 * a := by linarith
  have ha : a ≠ 0 := hab.1
  have hb : b ≠ 0 := hab.2
  have h2 : |b| = 2 * |a| := by 
    rw [h1]
    have h3 : |-2 * a| = 2 * |a| := by
      calc
        |-2 * a| = |(-2 : ℝ)| * |a| := by rw [abs_mul]
        _ = |(-2 : ℝ)| * |a| := by ring
        _ = (2 : ℝ) * |a| := by norm_num
        _ = 2 * |a| := by ring
    linarith [h3]
  by_cases h3 : a > 0
  · -- Case a > 0
    have ha_pos : a > 0 := h3
    have h4 : |a| = a := abs_of_pos ha_pos
    have h5 : |b| = 2 * a := by 
      linarith [h2, h4]
    have h6 : a / |b| = 1 / 2 := by
      rw [h5]
      field_simp [show a ≠ 0 by exact ha]
      <;> nlinarith
    have h7 : |a| / b = -1 / 2 := by
      have ha_pos : a > 0 := h3
      have h8 : |a| = a := by linarith [h4]
      have h9 : b = -2 * a := by linarith [h1]
      rw [h8, h9]
      field_simp [show a ≠ 0 by exact ha]
      <;> nlinarith 
    have h8 : |a / |b| - 1| = 1 / 2 := by
      have h6' : a / |b| = 1 / 2 := h6
      rw [h6']
      norm_num [abs]
    have h9 : |(|a| / b) - 2| = 5 / 2 := by
      have h7' : |a| / b = -1 / 2 := h7
      rw [h7']
      norm_num [abs]
    rw [h8, h9]
    norm_num 
  · -- Case a ≤ 0 
    have h3' : a < 0 := by 
      by_contra h 
      push_neg at h 
      have : a = 0 := by linarith 
      contradiction 
    have ha_neg : a < 0 := h3' 
    have h4 : |a| = -a := abs_of_neg ha_neg 
    have h5 : |b| = -2 * a := by 
      have h6 : |b| = 2 * |a| := by linarith [h2] 
      rw [h6, h4] 
      all_goals nlinarith 
    have h6 : a / |b| = -1 / 2 := by 
      rw [h5] 
      field_simp [show a ≠ 0 by exact ha] 
      <;> nlinarith 
    have h7 : |a| / b = 1 / 2 := by 
      have h8 : |a| = -a := by linarith [h4] 
      have h9 : b = -2 * a := by linarith [h1] 
      rw [h8, h9] 
      field_simp [show a ≠ 0 by exact ha] 
      <;> nlinarith 
    have h8 : |a / |b| - 1| = 3 / 2 := by 
      have h6' : a / |b| = -1 / 2 := h6 
      rw [h6'] 
      norm_num [abs] 
    have h9 : |(|a| / b) - 2| = 3 / 2 := by 
      have h7' : |a| / b = 1 / 2 := h7 
      rw [h7'] 
      norm_num [abs] 
    rw [h8, h9] 
    norm_num