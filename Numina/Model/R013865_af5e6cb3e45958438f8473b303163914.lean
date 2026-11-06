import Mathlib

theorem inequalities_603739
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    ((2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) +
     (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) +
     (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2)) ≤ 8 := by 
  have h1 : 0 < 2 * a^2 + (b + c) ^ 2 := by 
    positivity
  have h2 : 0 < 2 * b^2 + (c + a) ^ 2 := by 
    positivity
  have h3 : 0 < 2 * c^2 + (a + b) ^ 2 := by 
    positivity
  have h4 : (2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) - 8 ≤ 0 := by 
    have h5 : (2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) - 8 =
        ((2 * a + b + c) ^ 2 * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2) + (a + 2 * b + c) ^ 2 * (2 * a^2 + (b + c) ^ 2) * (2 * c^2 + (a + b) ^ 2) + (a + b + 2 * c) ^ 2 * (2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) - 8 * (2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2)) / ((2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2)) := by 
      field_simp [h1, h2, h3]
      ring 
    rw [h5]
    apply div_nonpos_of_nonpos_of_nonneg 
    · -- Show that the numerator is ≤ 0
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (c - a)), 
        sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (c - a)), 
        sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (c - a)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    · -- Show that the denominator is ≥ 0
      positivity
  linarith