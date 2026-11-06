import Mathlib

theorem algebra_101921 (a : ℝ) (ha : 0 < a) (h : a^3 = 6 * (a + 1)) :
    ¬∃ x, x^2 + a * x + a^2 - 6 = 0 := by
  rintro ⟨x, hx⟩
  have h3 : (x + a / 2) ^ 2 = 6 - 3 * a^2 / 4 := by 
    nlinarith
  have h4 : a^2 > 8 := by
    nlinarith [sq_nonneg (a^2 - 8), sq_nonneg (a - 2), sq_nonneg (a + 2), h, mul_pos ha (show 0 < a by linarith)]
  have h5 : 6 - 3 * a^2 / 4 < (0 : ℝ) := by 
    nlinarith
  have h6 : (x + a / 2) ^ 2 ≥ 0 := by
    apply sq_nonneg
  nlinarith