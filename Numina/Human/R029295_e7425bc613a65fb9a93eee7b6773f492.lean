import Mathlib

theorem inequalities_68274 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h₀ : a + b + c = 0) (h₁ : a * b * c < 0) :
    (a ^ 2 + b ^ 2) / c + (b ^ 2 + c ^ 2) / a + (c ^ 2 + a ^ 2) / b > 0 := by
  have h2 : (a ^ 2 + b ^ 2) / c + (b ^ 2 + c ^ 2) / a + (c ^ 2 + a ^ 2) / b = -2 * (a * b / c + b * c / a + c * a / b) := by
    have h1 : a + b + c = 0 := h₀
    have h2 : (a ^ 2 + b ^ 2) / c = c - 2 * (a * b / c) := by 
      have hc' : c ≠ 0 := hc
      have h1 : a + b + c = 0 := h₀
      have h2 : a + b = -c := by linarith
      have h3 : a ^ 2 + b ^ 2 = c ^ 2 - 2 * (a * b) := by 
        have h2 : a + b = -c := by linarith 
        have h : (a + b) ^ 2 = c ^ 2 := by 
          rw [h2]
          ring
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (c)]
      field_simp [hc']
      linarith
    have h3 : (b ^ 2 + c ^ 2) / a = a - 2 * (b * c / a) := by 
      have ha' : a ≠ 0 := ha
      have h1 : a + b + c = 0 := h₀
      have h2 : b + c = -a := by linarith
      have h3 : b ^ 2 + c ^ 2 = a ^ 2 - 2 * (b * c) := by
        have h2 : b + c = -a := by linarith 
        have h : (b + c) ^ 2 = a ^ 2 := by 
          rw [h2]
          ring
        nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (a)]
      field_simp [ha']
      linarith
    have h4 : (c ^ 2 + a ^ 2) / b = b - 2 * (c * a / b) := by 
      have hb' : b ≠ 0 := hb
      have h1 : a + b + c = 0 := h₀
      have h2 : c + a = -b := by linarith
      have h3 : c ^ 2 + a ^ 2 = b ^ 2 - 2 * (c * a) := by
        have h2 : c + a = -b := by linarith
        have h : (c + a) ^ 2 = b ^ 2 := by 
          rw [h2]
          ring
        nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (b)]
      field_simp [hb']
      linarith
    linarith [h2, h3, h4]
  rw [h2]
  have h3 : a * b / c + b * c / a + c * a / b < 0 := by
    have h3 : a * b / c + b * c / a + c * a / b = (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) / (a * b * c) := by
      have h1 : a ≠ 0 := ha
      have h2 : b ≠ 0 := hb
      have h3 : c ≠ 0 := hc
      field_simp [h1, h2, h3]
      ring
    rw [h3]
    have h4 : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 > 0 := by
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, 
        sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a)]
    have h5 : a * b * c < 0 := h₁
    apply div_neg_of_pos_of_neg
    all_goals linarith
  linarith