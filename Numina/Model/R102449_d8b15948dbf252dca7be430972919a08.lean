import Mathlib

theorem inequalities_598411 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  have h1 : (b + c) > 0 := by positivity
  have h2 : (c + a) > 0 := by positivity
  have h3 : (a + b) > 0 := by positivity
  
  have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h5 : (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2) =
        (2 * a * (a + b) * (c + a) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (a + b) * (b + c) * (c + a)) /
        (2 * (a + b) * (b + c) * (c + a)) := by 
      field_simp
      ring
    rw [h5]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    positivity

  linarith