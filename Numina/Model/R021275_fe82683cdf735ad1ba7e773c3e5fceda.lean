import Mathlib

theorem inequalities_307949 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : a + b = 1 := h
  have h4 : b = 1 - a := by linarith [h3]
  have h5 : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
    rw [show b = 1 - a by linarith [h3]]
    have h6 : 0 < a := ha
    have h7 : 0 < (1 - a) := by nlinarith
    have ha1 : 0 < a := ha
    have hb1 : 0 < (1 - a) := by nlinarith
    have h9 : (a + 1 / a) ^ 2 + ((1 - a) + 1 / (1 - a)) ^ 2 - 25 / 2 ≥ 0 := by
      have h11 : a ≠ 0 := by linarith
      have h12 : (1 - a) ≠ 0 := by nlinarith
      have h13 : a ^ 2 * (1 - a) ^ 2 > 0 := by positivity
      have h14 : (a + 1 / a) ^ 2 + ((1 - a) + 1 / (1 - a)) ^ 2 - 25 / 2 =
          ( ((a^2 + 1)^2 * (1 - a)^2 + ((1 - a)^2 + 1)^2 * a^2 - (25 / 2) * a^2 * (1 - a)^2) ) / (a^2 * (1 - a)^2) := by 
          field_simp 
          ring
      rw [h14] at *
      apply div_nonneg
      · -- Show the numerator is non-negative
        nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2), 
            sq_nonneg (a * (1 - a) - 1 / 4), sq_nonneg (a - (1 - a)), 
            mul_pos ha hb1, 
            sq_nonneg (a^2 - (1 - a)^2), 
            sq_nonneg (a * (a - 1 / 2)), sq_nonneg ((1 - a) * ((1 - a) - 1 / 2)), 
            mul_pos (show a ^ 2 > 0 by positivity) (show (1 - a) ^ 2 > 0 by positivity) 
            ]
      · -- Show the denominator is non-negative
        positivity
    linarith 
  linarith