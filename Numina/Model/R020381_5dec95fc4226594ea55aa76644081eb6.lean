import Mathlib

open Real

theorem inequalities_78989 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
    1 / a + 1 / b + 1 / c ≤ 1 / (a + b - c) + 1 / (c + a - b) + 1 / (b + c - a) := by
  have h1 : 0 < a + b - c := by linarith
  have h2 : 0 < c + a - b := by linarith
  have h3 : 0 < b + c - a := by linarith
  have h5 : (1 / (a) + 1 / (b) + 1 / (c) ) - (1 / (a + b - c) + 1 / (c + a - b) + 1 / (b + c - a) ) ≤ 0 := by
    have h5a : 0 < a * b * c * (a + b - c) * (c + a - b) * (b + c - a) := by
      positivity
    have h11 : ( (1 / (a) + 1 / (b) + 1 / (c) ) - (1 / (a + b - c) + 1 / (c + a - b) + 1 / (b + c - a) ) ) =
      ( ( b * c * (a + b - c) * (c + a - b) * (b + c - a ) +
          a * c * (a + b - c) * (c + a - b) * (b + c - a ) +
          a * b * (a + b - c) * (c + a - b) * (b + c - a ) - 
          a * b * c * ( (c + a - b) * (b + c - a) + (a + b - c) * (b + c - a) + (a + b - c) * (c + a - b) ) ) / ( a * b * c * (a + b - c) * (c + a - b) * (b + c - a) ) ) := by
      field_simp
      ring
    rw [h11] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show the numerator is nonpositive.
      have hx : b * c * (a + b - c) * (c + a - b) * (b + c - a ) + a * c * (a + b - c) * (c + a - b) * (b + c - a ) + a * b * (a + b - c) * (c + a - b) * (b + c - a ) - a * b * c * ( (c + a - b) * (b + c - a) + (a + b - c) * (b + c - a) + (a + b - c) * (c + a - b) ) ≤ 0 := by
        nlinarith [ sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            mul_pos h1 h2, mul_pos h2 h3, mul_pos h1 h3,
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
            mul_pos h1 (show 0 < a * b by nlinarith),
            mul_pos h1 (show 0 < a * c by nlinarith),
            mul_pos h1 (show 0 < b * c by nlinarith),
            mul_pos h2 (show 0 < a * b by nlinarith),
            mul_pos h2 (show 0 < a * c by nlinarith),
            mul_pos h2 (show 0 < b * c by nlinarith),
            mul_pos h3 (show 0 < a * b by nlinarith),
            mul_pos h3 (show 0 < a * c by nlinarith),
            mul_pos h3 (show 0 < b * c by nlinarith)
              ]
      linarith
    · -- Show the denominator is nonnegative.
      positivity
  linarith [h5]