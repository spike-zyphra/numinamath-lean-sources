import Mathlib

theorem inequalities_245905 (a b c d e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    (a * b / (a + b) + c * d / (c + d) + e * f / (e + f)) ≤
    ((a + c + e) * (b + d + f)) / (a + b + c + d + e + f) := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < c + d := by linarith
  have h3 : 0 < e + f := by linarith
  have h4 : 0 < a + b + c + d + e + f := by linarith
  have pos1 : 0 < (a + b) := by linarith
  have pos2 : 0 < (c + d) := by linarith
  have pos3 : 0 < (e + f) := by linarith
  have pos4 : 0 < (a + b + c + d + e + f) := by linarith
  have h8 : ( (a * b / (a + b) + c * d / (c + d) + e * f / (e + f)) - ((a + c + e) * (b + d + f) / (a + b + c + d + e + f)) ) ≤ 0 := by
    have h9 : ( (a * b / (a + b) + c * d / (c + d) + e * f / (e + f)) - ((a + c + e) * (b + d + f) / (a + b + c + d + e + f)) ) =
        ( (a * b) * (c + d) * (e + f) * (a + b + c + d + e + f) +
          (c * d) * (a + b) * (e + f) * (a + b + c + d + e + f) +
          (e * f) * (a + b) * (c + d) * (a + b + c + d + e + f) - (a + c + e) * (b + d + f) * (a + b) * (c + d) * (e + f) ) / ( (a + b) * (c + d) * (e + f) * (a + b + c + d + e + f) ) := by
      field_simp
      ring
    rw [h9] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is non-positive
      have h10 : (a * b) * (c + d) * (e + f) * (a + b + c + d + e + f) + (c * d) * (a + b) * (e + f) * (a + b + c + d + e + f) + (e * f) * (a + b) * (c + d) * (a + b + c + d + e + f) - (a + c + e) * (b + d + f) * (a + b) * (c + d) * (e + f) ≤ 0 := by
        have h101 : 0 < a * b * c * d * e * f := by
          positivity
        nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (a * b - e * f), sq_nonneg (c * d - e * f), 
          sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (e - f),
          sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c),
          sq_nonneg (a * e - b * f), sq_nonneg (a * f - b * e),
          sq_nonneg (c * e - d * f), sq_nonneg (c * f - d * e),
          sq_nonneg (a + b - c - d), sq_nonneg (a + b - e - f), sq_nonneg (c + d - e - f),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos ha he, mul_pos ha hf, 
          mul_pos hb hc, mul_pos hb hd, mul_pos hb he, mul_pos hb hf, 
          mul_pos hc hd, mul_pos hc he, mul_pos hc hf, mul_pos hd he, mul_pos hd hf, 
          mul_pos he hf ]
      linarith
    · -- Show that the denominator is non-negative
      positivity
  linarith