import Mathlib

theorem algebra_297124 {a b : ℝ} (ha : a ≠ -b) (h : 1 / a + 1 / b = 5 / (a + b)) :
    b ^ 2 / a ^ 2 + a ^ 2 / b ^ 2 = 7 := by 
  have ha1 : a ≠ 0 := by 
    by_contra h1
    have ha0 : a = (0 : ℝ) := by linarith 
    rw [ha0] at h 
    have h2 : b ≠ 0 := by 
      by_contra h3
      have hb0 : b = 0 := by linarith 
      have : a = -b := by 
        simp [ha0, hb0]
      contradiction 
    have h3 : (1 / b : ℝ) = (5 / b : ℝ) := by 
      field_simp [(show b ≠ 0 by exact h2), (show b ≠ 0 by exact h2)] at h ⊢
      all_goals linarith 
    have h4 : (1 : ℝ) = (5 : ℝ) := by 
      have h5 : b ≠ 0 := h2 
      field_simp [h5] at h3 ⊢ 
      all_goals linarith 
    linarith 
  have hb1 : b ≠ 0 := by 
    by_contra h2
    have hb0 : b = (0 : ℝ) := by linarith 
    rw [hb0] at h 
    have h2 : a ≠ 0 := ha1 
    have h3 : (1 / a : ℝ) = (5 / a : ℝ) := by 
      field_simp [(show a ≠ 0 by exact h2), (show a ≠ 0 by exact h2)] at h ⊢ 
      all_goals linarith 
    have h4 : (1 : ℝ) = (5 : ℝ) := by 
      have h5 : a ≠ 0 := h2 
      field_simp [h5] at h3 ⊢ 
      all_goals linarith 
    linarith 
  have h3 : a + b ≠ 0 := by 
    intro h4
    have h4' : a = -b := by linarith
    contradiction 
  have h4 : a ^ 2 + 2 * a * b + b ^ 2 = 5 * (a * b) := by
    have h5 : a + b ≠ 0 := h3 
    have h6 : 1 / a + 1 / b = (a + b) / (a * b) := by 
      field_simp [ha1, hb1]
      <;> ring
    rw [h6] at h 
    have h7 : (a + b : ℝ) ^ 2 = 5 * (a * b : ℝ) := by
      have hb1' : a * b ≠ 0 := by 
        apply mul_ne_zero 
        exact_mod_cast ha1
        exact_mod_cast hb1 
      have hb2 : a + b ≠ 0 := h3 
      field_simp [hb1', hb2] at h ⊢ 
      nlinarith 
    nlinarith 
  have h8 : a ^ 2 + b ^ 2 = 3 * (a * b) := by
    nlinarith 
  have h9 : b ^ 2 / a ^ 2 + a ^ 2 / b ^ 2 = 7 := by 
    have h10 : b ^ 2 / a ^ 2 + a ^ 2 / b ^ 2 = (b ^ 4 + a ^ 4) / (a ^ 2 * b ^ 2) := by 
      field_simp [ha1, hb1]
      <;> ring 
    rw [h10]
    have h11 : a ^ 4 + b ^ 4 = 7 * (a ^ 2 * b ^ 2) := by 
      have h14 : a^2 + b^2 = 3 * (a * b) := h8 
      have h15 : (a^2 + b^2) ^ 2 = 9 * (a * b) ^ 2 := by 
        rw [h14]
        ring 
      have h16 : (a^2 + b^2) ^ 2 = a ^ 4 + 2 * (a ^ 2 * b ^ 2) + b ^ 4 := by 
        ring 
      nlinarith 
    have h12 : a ^ 2 * b ^ 2 ≠ 0 := by 
      apply mul_ne_zero 
      · -- a^2 ≠ 0
        apply pow_ne_zero 2 
        exact_mod_cast ha1 
      · -- b^2 ≠ 0
        apply pow_ne_zero 2 
        exact_mod_cast hb1 
    have h13 : (b ^ 4 + a ^ 4 : ℝ) / (a ^ 2 * b ^ 2 : ℝ) = 7 := by 
      have h14 : b ^ 4 + a ^ 4 = 7 * (a ^ 2 * b ^ 2) := by 
        linarith [h11] 
      have h12' : (a ^ 2 * b ^ 2 : ℝ) ≠ 0 := h12 
      field_simp [h12'] 
      all_goals nlinarith 
    linarith [h13] 
  exact h9