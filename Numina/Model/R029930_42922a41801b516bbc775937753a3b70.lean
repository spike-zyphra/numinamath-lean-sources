import Mathlib

theorem inequalities_91700 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 + 3 / (a + b + c) ≥ 6 / (a * b + b * c + c * a) := by
  have h6 : 0 < a + b + c := by
    positivity
  have h7 : 0 < a * b + b * c + c * a := by
    positivity
  have h11 : 1 + 3 / (a + b + c) - 6 / (a * b + b * c + c * a) ≥ 0 := by
    have h6' : (1 + 3 / (a + b + c) - 6 / (a * b + b * c + c * a)) =
        ((a + b + c) * (a * b + b * c + c * a) + 3 * (a * b + b * c + c * a) - 6 * (a + b + c)) / ((a + b + c) * (a * b + b * c + c * a)) := by
      field_simp
      <;> ring_nf <;> nlinarith [habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    rw [h6']
    have h9 : ((a + b + c) * (a * b + b * c + c * a) + 3 * (a * b + b * c + c * a) - 6 * (a + b + c)) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        sq_nonneg (a * b + b * c + c * a - 3), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        habc]
    have h9' : ((a + b + c) * (a * b + b * c + c * a) + 3 * (a * b + b * c + c * a) - 6 * (a + b + c)) / ((a + b + c) * (a * b + b * c + c * a)) ≥ 0 := by
      apply div_nonneg
      linarith [h9]
      positivity
    linarith [h9']
  linarith [show (1 + 3 / (a + b + c) - 6 / (a * b + b * c + c * a)) ≥ 0 from by
    linarith [h11]]