import Mathlib

theorem inequalities_107200 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) := by
  have h1 : 1 + 2 * a > 0 := by nlinarith
  have h2 : 1 + 2 * b > 0 := by nlinarith
  have h3 : 1 + 2 * c > 0 := by nlinarith
  have h4 : 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1 ≥ 0 := by
    have h1' : a * b * c = 1 := habc
    have h5 : 0 < (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) := by positivity
    have h6 : 0 < (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) := by positivity
    have h9 : (1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1) =
        ( (1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) - (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) ) / ((1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) := by
      field_simp
      ring
    rw [h9]
    apply div_nonneg 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]
    positivity
  linarith