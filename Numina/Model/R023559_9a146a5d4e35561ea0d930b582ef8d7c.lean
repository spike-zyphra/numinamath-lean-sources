import Mathlib
open Real

theorem inequalities_8142
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d) :
    a * b / (a + b) + b * c / (b + c) + c * d / (c + d) + d * a / (d + a) ≤
    2 * (a * b + b * c + c * d + d * a) / (a + b + c + d) := by
  have h1 : a + b > 0 := by nlinarith
  have h2 : b + c > 0 := by nlinarith
  have h3 : c + d > 0 := by nlinarith
  have h4 : d + a > 0 := by nlinarith
  have h5 : a + b + c + d > 0 := by linarith
  have h6 : a * b / (a + b) + b * c / (b + c) + c * d / (c + d) + d * a / (d + a) - 2 * (a * b + b * c + c * d + d * a) / (a + b + c + d) ≤ 0 := by 
    have h7 : a * b / (a + b) + b * c / (b + c) + c * d / (c + d) + d * a / (d + a) - 2 * (a * b + b * c + c * d + d * a) / (a + b + c + d) =
        (a * b * (b + c) * (c + d) * (d + a) * (a + b + c + d) +
        b * c * (a + b) * (c + d) * (d + a) * (a + b + c + d) +
        c * d * (a + b) * (b + c) * (d + a) * (a + b + c + d) +
        d * a * (a + b) * (b + c) * (c + d) * (a + b + c + d) - 2 * (a * b + b * c + c * d + d * a) * (a + b) * (b + c) * (c + d) * (d + a)) / ((a + b) * (b + c) * (c + d) * (d + a) * (a + b + c + d)) := by
      field_simp
      ring
    rw [h7] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is non-positive
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * d), sq_nonneg (c * d - d * a), sq_nonneg (d * a - a * b), 
        sq_nonneg (a - c), sq_nonneg (b - d), 
        sq_nonneg (a + c - (b + d)), 
        sq_nonneg (a + b - c - d), 
        sq_nonneg (a * b - c * d), sq_nonneg (b * c - d * a), 
        mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
        mul_pos hb hc, mul_pos hb hd, 
        mul_pos hc hd
      ]
    · -- Show that the denominator is non-negative
      positivity
  linarith