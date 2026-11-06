import Mathlib

theorem inequalities_123251 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 ≤ (a ^ 2 + 1) / (b + c) + (b ^ 2 + 1) / (c + a) + (c ^ 2 + 1) / (a + b) := by
  have h1 : 0 < b + c := by nlinarith
  have h2 : 0 < c + a := by nlinarith
  have h3 : 0 < a + b := by nlinarith
  have h4 : (a ^ 2 + 1) / (b + c) + (b ^ 2 + 1) / (c + a) + (c ^ 2 + 1) / (a + b) - (3 : ℝ) ≥ 0 := by
    have h5 : 0 < (b + c) * (c + a) * (a + b) := by
      positivity
    have h6 : (a ^ 2 + 1) / (b + c) + (b ^ 2 + 1) / (c + a) + (c ^ 2 + 1) / (a + b) - (3 : ℝ) =
        ((a ^ 2 + 1) * (c + a) * (a + b) + (b ^ 2 + 1) * (b + c) * (a + b) + (c ^ 2 + 1) * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h6]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    positivity
  linarith