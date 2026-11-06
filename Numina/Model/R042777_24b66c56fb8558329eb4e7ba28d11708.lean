import Mathlib

theorem inequalities_599110 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) :
    1 ≤ b / (1 + a ^ 3) + a / (1 + b ^ 3) := by 
  have h2 : 0 < 1 + a ^ 3 := by 
    nlinarith [sq_nonneg (a), sq_nonneg (a - 1)]
  have h3 : 0 < 1 + b ^ 3 := by
    nlinarith [sq_nonneg (b), sq_nonneg (b - 1)]
  have h6 : b / (1 + a ^ 3) + a / (1 + b ^ 3) - 1 ≥ 0 := by 
    have h71 : b / (1 + a ^ 3) + a / (1 + b ^ 3) - 1 = (b * (1 + b^3) + a * (1 + a^3) - (1 + a^3) * (1 + b^3)) / ((1 + a^3) * (1 + b^3)) := by 
      field_simp 
    rw [h71] at *
    apply div_nonneg 
    · -- Show that b * (1 + b^3) + a * (1 + a^3) - (1 + a^3) * (1 + b^3) ≥ 0 
      have h10 : b * (1 + b^3) + a * (1 + a^3) - (1 + a^3) * (1 + b^3) ≥ 0 := by
        have h41 : a * b = 1 := hab
        have h21 : a + b ≥ 2 := by
          nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a * b - 1), hab, mul_pos ha hb]
        have h31 : a ^ 2 + b ^ 2 ≥ 2 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), hab, mul_pos ha hb]
        have h42 : a ^ 3 + b ^ 3 ≥ 2 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), hab, mul_pos ha hb, sq_nonneg (a + b - 2)]
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a * b - 1), mul_pos ha hb, hab, sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1)]
      linarith 
    · -- Show denominator > 0 
      positivity 
  linarith