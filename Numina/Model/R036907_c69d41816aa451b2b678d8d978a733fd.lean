import Mathlib

theorem inequalities_44460 (a : ℝ) (ha : 0 < a) (h : a^3 = 6 * (a + 1)) :
    ¬∃ x : ℝ, x^2 + a * x + a^2 - 6 = 0 := by
  -- First we need to show a^2 > 8
  have h2 : a ^ 2 > 8 := by
    nlinarith [sq_nonneg (a ^ 2 - 8), sq_nonneg (a - 2), sq_nonneg (a + 2), sq_nonneg (a - 3),
      sq_pos_of_pos ha, mul_pos ha ha, mul_pos ha (show 0 < a ^ 2 by nlinarith), sq_nonneg (a ^ 2 - 4)]
  rintro ⟨x, hx⟩
  have h4 : (24 - 3 * (a ^ 2)) < 0 := by 
    nlinarith
  have h5 : x ^ 2 + a * x + (a^2 - 6) = 0 := by
    linarith [hx]
  nlinarith [sq_nonneg (x + a / 2), sq_nonneg (a), sq_nonneg (x * a), sq_nonneg (a - 3), sq_nonneg (a + 2), mul_pos ha ha]