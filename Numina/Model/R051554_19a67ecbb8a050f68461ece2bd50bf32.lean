import Mathlib

theorem inequalities_170353 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b + c - 2 * a) / (a^2 + b * c) + (c + a - 2 * b) / (b^2 + c * a) +
    (a + b - 2 * c) / (c^2 + a * b) ≥ 0 := by 
  have h₁ : 0 < a^2 + b * c := by 
    positivity 
  have h₂ : 0 < b^2 + c * a := by 
    positivity 
  have h₃ : 0 < c^2 + a * b := by 
    positivity 
  have h4 : (b + c - 2 * a) / (a^2 + b * c) + (c + a - 2 * b) / (b^2 + c * a) + (a + b - 2 * c) / (c^2 + a * b) =
      ((b + c - 2 * a) * (b^2 + c * a) * (c^2 + a * b)
          + (c + a - 2 * b) * (a^2 + b * c) * (c^2 + a * b)
          + (a + b - 2 * c) * (a^2 + b * c) * (b^2 + c * a)
        ) / ((a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b)) := by 
    field_simp 
    ring 
  rw [h4]
  apply div_nonneg 
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
    sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
    sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  positivity