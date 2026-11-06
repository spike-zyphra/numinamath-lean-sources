import Mathlib

theorem inequalities_599035 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b = 1) :
    (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
  have hb1 : b = 1 - a := by
    linarith
  rw [hb1]
  have ha1 : 0 < a := ha
  have hb1' : 0 < 1 - a := by
    nlinarith
  have h1 : (a + 1 / a) ^ 2 + ((1 - a) + 1 / (1 - a)) ^ 2 - 25 / 2 ≥ 0 := by
    have h2 : 0 < a := ha
    have h3 : 0 < 1 - a := by
      nlinarith
    have pos4 : a * (1 - a) > 0 := by
      nlinarith
    have h14 : (a + 1 / a) ^ 2 + ((1 - a) + 1 / (1 - a)) ^ 2 - 25 / 2 ≥ 0 := by
      have pos1 : 0 < a := h2
      have pos2 : 0 < 1 - a := h3
      have h17 : (a + 1 / a) ^ 2 + ((1 - a) + 1 / (1 - a)) ^ 2 - 25 / 2 =
          (a^4 * (1 - a)^2 + 2 * a^2 * (1 - a)^2 + a^2 + a^2 * (1 - a)^4 + 2 * a^2 * (1 - a)^2 + (1 - a)^2 - 25 / 2 * a^2 * (1 - a)^2) / (a^2 * (1 - a)^2) := by
        field_simp
        ring
      rw [h17]
      apply div_nonneg
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2), sq_nonneg (a - (1 - a)), sq_nonneg (a * (1 - a) - 1 / 4), sq_nonneg (a ^ 2 - (1 - a) ^ 2), sq_nonneg (a - 1 + a), sq_nonneg (a ^ 2 - 1 / 4), sq_nonneg ((1 - a) ^ 2 - 1 / 4), mul_pos h2 h3]
      positivity
    linarith
  linarith