import Mathlib

theorem inequalities_129023 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    69 / 4 ≤ (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have h3 : 0 < 1 + c := by linarith
  have h4 : 0 < (1 + a) * (1 + b) * (1 + c) := by
    positivity
  have h5 : (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) - 69 / 4 ≥ 0 := by
    have h6 : (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) - 69 / 4 =
      ((7 + 2 * b) * (1 + b) * (1 + c) + (7 + 2 * c) * (1 + a) * (1 + c) + (7 + 2 * a) * (1 + a) * (1 + b) - 69 / 4 * ((1 + a) * (1 + b) * (1 + c))) / ((1 + a) * (1 + b) * (1 + c)) := by
      field_simp
      ring
    rw [h6]
    have h7 : (7 + 2 * b) * (1 + b) * (1 + c) + (7 + 2 * c) * (1 + a) * (1 + c) + (7 + 2 * a) * (1 + a) * (1 + b) - 69 / 4 * ((1 + a) * (1 + b) * (1 + c)) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
                  sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3), 
                  h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply div_nonneg
    · linarith
    · positivity
  linarith