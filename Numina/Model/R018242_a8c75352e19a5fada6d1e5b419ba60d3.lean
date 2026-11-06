import Mathlib

open Real
open scoped BigOperators

theorem inequalities_86542 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h1 : a + b > c) (h2 : b + c > a) (h3 : c + a > b) :
  3 / 2 < (a * b + 1) / (a ^ 2 + c * a + 1) +
  (b * c + 1) / (b ^ 2 + a * b + 1) +
  (c * a + 1) / (c ^ 2 + b * c + 1) := by

  have h4 : 0 < a * b := mul_pos ha hb
  have h5 : 0 < b * c := mul_pos hb hc
  have h6 : 0 < c * a := mul_pos hc ha

  have h7 : 0 < a ^ 2 + c * a + 1 := by
    nlinarith [sq_pos_of_pos ha, mul_pos hc ha]

  have h8 : 0 < b ^ 2 + a * b + 1 := by
    nlinarith [sq_pos_of_pos hb, mul_pos ha hb]

  have h9 : 0 < c ^ 2 + b * c + 1 := by
    nlinarith [sq_pos_of_pos hc, mul_pos hb hc]

  have h10 : (a * b + 1) / (a ^ 2 + c * a + 1) + (b * c + 1) / (b ^ 2 + a * b + 1) + (c * a + 1) / (c ^ 2 + b * c + 1) - 3 / 2 > 0 := by
    have h11 : (a * b + 1) / (a ^ 2 + c * a + 1) + (b * c + 1) / (b ^ 2 + a * b + 1) + (c * a + 1) / (c ^ 2 + b * c + 1) - 3 / 2 =
        ( (a * b + 1) * (b ^ 2 + a * b + 1) * (c ^ 2 + b * c + 1) + (b * c + 1) * (a ^ 2 + c * a + 1) * (c ^ 2 + b * c + 1) + (c * a + 1) * (a ^ 2 + c * a + 1) * (b ^ 2 + a * b + 1) - 3 / 2 * (a ^ 2 + c * a + 1) * (b ^ 2 + a * b + 1) * (c ^ 2 + b * c + 1) ) / ( (a ^ 2 + c * a + 1) * (b ^ 2 + a * b + 1) * (c ^ 2 + b * c + 1) ) := by
      field_simp
      ring
    rw [h11] at *
    apply div_pos
    -- Show the numerator is positive
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
      sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith), 
      mul_pos (show 0 < a + b - c by linarith) (show 0 < c + a - b by linarith), 
      mul_pos (show 0 < b + c - a by linarith) (show 0 < c + a - b by linarith)
      ]
    all_goals positivity
  
  linarith