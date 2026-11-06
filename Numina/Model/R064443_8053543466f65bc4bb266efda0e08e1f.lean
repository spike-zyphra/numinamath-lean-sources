import Mathlib

theorem inequalities_600128
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) := by
  have h1 : 0 < (1 + 2 * a) := by linarith
  have h11 : 0 < (1 + 2 * b) := by linarith
  have h12 : 0 < (1 + 2 * c) := by linarith
  have h2 : 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1 ≥ 0 := by
    have pos1 : 0 < (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) := by positivity
    have h3 : (1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1) =
      ( (1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) - (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) ) / ((1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) := by 
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
       sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
       mul_pos ha hb, mul_pos hb hc, mul_pos ha hc ]
    positivity
  linarith