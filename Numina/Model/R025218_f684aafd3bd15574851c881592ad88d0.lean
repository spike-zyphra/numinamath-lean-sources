import Mathlib

theorem inequalities_2632 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1/(2*a+b+c) + 1/(a+2*b+c) + 1/(a+b+2*c) ≤ 1/(a+3*b) + 1/(b+3*c) + 1/(c+3*a) := by
  have h1 : 0 < a := by linarith
  have h2 : 0 < b := by linarith
  have h3 : 0 < c := by linarith
  have h4 : 0 < (2 * a + b + c) := by positivity
  have h5 : 0 < (a + 2 * b + c) := by positivity
  have h6 : 0 < (a + b + 2 * c) := by positivity
  have h7 : 0 < (a + 3 * b) := by positivity
  have h8 : 0 < (b + 3 * c) := by positivity
  have h9 : 0 < (c + 3 * a) := by positivity
  have h10 : 1/(2*a+b+c) + 1/(a+2*b+c) + 1/(a+b+2*c) - (1/(a+3*b) + 1/(b+3*c) + 1/(c+3*a)) ≤ 0 := by
    have h11 : 0 < (2 * a + b + c) * (a + 2 * b + c) * (a + b + 2 * c) * (a + 3 * b) * (b + 3 * c) * (c + 3 * a) := by positivity
    have h12 : 1/(2*a+b+c) + 1/(a+2*b+c) + 1/(a+b+2*c) - (1/(a+3*b) + 1/(b+3*c) + 1/(c+3*a)) =
        ( 
          ( 
            (a + 2 * b + c) * (a + b + 2 * c) * (a + 3 * b) * (b + 3 * c) * (c + 3 * a) +
            (2 * a + b + c) * (a + b + 2 * c) * (a + 3 * b) * (b + 3 * c) * (c + 3 * a) + 
            (2 * a + b + c) * (a + 2 * b + c) * (a + 3 * b) * (b + 3 * c) * (c + 3 * a) - 
            ( (2 * a + b + c) * (a + 2 * b + c) * (a + b + 2 * c) * (b + 3 * c) * (c + 3 * a) ) - 
            ( (2 * a + b + c) * (a + 2 * b + c) * (a + b + 2 * c) * (a + 3 * b) * (c + 3 * a) ) - 
            ( (2 * a + b + c) * (a + 2 * b + c) * (a + b + 2 * c) * (a + 3 * b) * (b + 3 * c) ) 
          ) / ( (2 * a + b + c) * (a + 2 * b + c) * (a + b + 2 * c) * (a + 3 * b) * (b + 3 * c) * (c + 3 * a) ) 
        ) := by 
      field_simp
      ring
    rw [h12] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show the numerator is non-positive
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
        sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    · -- Show the denominator is non-negative
      positivity
  linarith