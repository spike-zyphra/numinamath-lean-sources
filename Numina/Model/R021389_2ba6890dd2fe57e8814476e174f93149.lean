import Mathlib

theorem inequalities_2822
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1) ≤ 1 := by
  have h1 : a * b + a + 1 > 0 := by
    positivity 
  have h2 : b * c + b + 1 > 0 := by
    positivity 
  have h3 : c * a + c + 1 > 0 := by
    positivity 
  have h4 : a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1) - 1 ≤ 0 := by
    have h5 : a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1) - 1 =
        ( (a * (b * c + b + 1) * (c * a + c + 1) + b * (a * b + a + 1) * (c * a + c + 1) + c * (a * b + a + 1) * (b * c + b + 1) - (a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1)) / ( (a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1) ) ) := by
      field_simp [h1, h2, h3]
      ring 
    rw [h5] 
    have h6 : a * (b * c + b + 1) * (c * a + c + 1) + b * (a * b + a + 1) * (c * a + c + 1) + c * (a * b + a + 1) * (b * c + b + 1) - (a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1) = - (a * b * c - 1) ^ 2 := by 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
    rw [h6] 
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that - (a * b * c - 1) ^ 2 ≤ 0
      have h7 : (a * b * c - 1) ^ 2 ≥ 0 := by 
        apply sq_nonneg
      linarith [h7]
    · -- Show that (a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1) ≥ 0
      positivity
  linarith