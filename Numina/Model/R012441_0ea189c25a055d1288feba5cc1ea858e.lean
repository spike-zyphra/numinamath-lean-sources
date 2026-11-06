import Mathlib

theorem inequalities_46909 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a * b / (3 * a + 4 * b + 5 * c) + b * c / (3 * b + 4 * c + 5 * a) +
     c * a / (3 * c + 4 * a + 5 * b)) ≤ (a + b + c) / 12 := by
  have h1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have h2 : 0 < 3 * a + 4 * b + 5 * c := by positivity
  have h3 : 0 < 3 * b + 4 * c + 5 * a := by positivity
  have h4 : 0 < 3 * c + 4 * a + 5 * b := by positivity
  have h5 : (a * b / (3 * a + 4 * b + 5 * c) + b * c / (3 * b + 4 * c + 5 * a) +
       c * a / (3 * c + 4 * a + 5 * b)) - (a + b + c) / 12 ≤ 0 := by
    have h6 : 0 < (3 * a + 4 * b + 5 * c) * (3 * b + 4 * c + 5 * a) * (3 * c + 4 * a + 5 * b) := by positivity
    have h7 : (a * b / (3 * a + 4 * b + 5 * c) + b * c / (3 * b + 4 * c + 5 * a) +
         c * a / (3 * c + 4 * a + 5 * b)) - (a + b + c) / 12 =
        ( (a * b * (3 * b + 4 * c + 5 * a) * (3 * c + 4 * a + 5 * b) * 12 +
            b * c * (3 * a + 4 * b + 5 * c) * (3 * c + 4 * a + 5 * b) * 12 +
            c * a * (3 * a + 4 * b + 5 * c) * (3 * b + 4 * c + 5 * a) * 12 - 
            (a + b + c) * (3 * a + 4 * b + 5 * c) * (3 * b + 4 * c + 5 * a) * (3 * c + 4 * a + 5 * b) ) / 
          ( (3 * a + 4 * b + 5 * c) * (3 * b + 4 * c + 5 * a) * (3 * c + 4 * a + 5 * b) * 12 ) ) := by 
      field_simp
      ring
    rw [h7] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- To show the numerator is non-positive
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a)]
    · -- Show that the denominator is non-negative
      positivity
  linarith