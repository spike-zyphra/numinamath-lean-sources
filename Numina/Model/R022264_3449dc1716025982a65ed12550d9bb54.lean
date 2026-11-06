import Mathlib

theorem inequalities_180403 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    9 / 4 ≥ 1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) + 1 / (c ^ 2 + 1) := by
  have h2 : 1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) + 1 / (c ^ 2 + 1) - 9 / 4 ≤ 0 := by
    have h3 : 0 < (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) := by positivity
    have h4 : (1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) + 1 / (c ^ 2 + 1) - 9 / 4) = ((b ^ 2 + 1) * (c ^ 2 + 1) + (a ^ 2 + 1) * (c ^ 2 + 1) + (a ^ 2 + 1) * (b ^ 2 + 1) - (9 / 4) * (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) / ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) := by 
      field_simp 
      ring
    rw [h4] at *
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b - 1 / 3), sq_nonneg (b * c - 1 / 3), sq_nonneg (c * a - 1 / 3),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    positivity
  linarith