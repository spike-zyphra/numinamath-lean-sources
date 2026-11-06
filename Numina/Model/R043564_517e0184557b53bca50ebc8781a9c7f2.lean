import Mathlib

theorem inequalities_149345 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b = 1) :
    (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
  have h₀ : a ^ 2 + b ^ 2 ≥ 1 / 2 := by
    nlinarith [sq_nonneg (a - b), h]
  have h₁ : a * b ≤ 1 / 4 := by
    have h1 : (a + b) ^ 2 = 1 := by
      nlinarith
    nlinarith [sq_nonneg (a - b), h]
  have h₃ : 0 < a * b := by
    apply mul_pos ha hb
  -- Show that 1/(a * b) >= 4
  have h₄ : 1 / (a * b) ≥ 4 := by
    have h11 : a * b ≤ 1 / 4 := h₁
    have h12 : 0 < a * b := h₃
    have h13 : 1 / (a * b) ≥ 4 := by 
      apply (le_div_iff₀ (by linarith)).mpr 
      nlinarith
    linarith
  -- Show that the given expression is ≥ 25/2
  have h8 : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
    have h22 : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 = (a ^ 2 + b ^ 2) + 4 + (1 / a ^ 2 + 1 / b ^ 2) := by
      field_simp
      <;> nlinarith
    have h10 : 1 / a ^ 2 + 1 / b ^ 2 ≥ 8 := by 
      have h13 : 1 / a ^ 2 + 1 / b ^ 2 = (a ^ 2 + b ^ 2) / (a * b) ^ 2 := by 
        field_simp
        <;> nlinarith
      rw [h13]
      have h15 : a^2 + b^2 ≥ 1/2 := h₀
      have h16 : (a * b) ^ 2 ≤ (1 / 4) ^ 2 := by
        have h17 : a * b ≤ 1 / 4 := h₁
        have h18 : 0 < a * b := by positivity
        nlinarith [sq_nonneg (a * b - 1 / 4)]
      have h16' : (a * b) ^ 2 ≤ 1 / 16 := by
        linarith 
      have h15' : a^2 + b^2 ≥ 1/2 := h₀ 
      apply (le_div_iff₀ (by positivity)).mpr 
      nlinarith
    have h23 : (a ^ 2 + b ^ 2) + (1 / a ^ 2 + 1 / b ^ 2) ≥ 17 / 2 := by
      linarith [h₀, h10]
    linarith [h22, h23]
  linarith [h8]