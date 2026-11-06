import Mathlib

theorem inequalities_597651
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
     (a + 2 * b + c)^2 / (2 * b^2 + (c + a)^2) +
     (a + b + 2 * c)^2 / (2 * c^2 + (a + b)^2)) ≤ 8 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    assumption
    assumption
    assumption
  have h2 : 2 * a^2 + (b + c)^2 > 0 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h3 : 2 * b^2 + (c + a)^2 > 0 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h4 : 2 * c^2 + (a + b)^2 > 0 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h5 : (2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) + (a + 2 * b + c)^2 / (2 * b^2 + (c + a)^2) + (a + b + 2 * c)^2 / (2 * c^2 + (a + b)^2) - 8 ≤ 0 := by
    have h6 : 0 < (2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2) := by
      positivity
    have h7 : (2 * a + b + c) ^ 2 / (2 * a^2 + (b + c)^2) + (a + 2 * b + c) ^ 2 / (2 * b^2 + (c + a)^2) + (a + b + 2 * c)^2 / (2 * c^2 + (a + b)^2) - 8 =
        ((2 * a + b + c)^2 * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2) + (a + 2 * b + c)^2 * (2 * a^2 + (b + c)^2) * (2 * c^2 + (a + b)^2) + (a + b + 2 * c)^2 * (2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) - 8 * ((2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2)) ) / ((2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2)) := by
      field_simp
      ring
    rw [h7] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is nonpositive.
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a), 
              sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)),
              sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)),
              sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
              sq_nonneg (a*b - b*c), sq_nonneg (a*b - a*c), sq_nonneg (a*c - b*c)
            ]
    · -- Show that the denominator is nonnegative.
      positivity
  linarith [h5]