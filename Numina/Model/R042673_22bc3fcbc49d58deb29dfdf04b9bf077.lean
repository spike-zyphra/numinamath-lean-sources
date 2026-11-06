import Mathlib
theorem algebra_605989 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + a * c + c ^ 2) * (1 / (a + b + c) + 1 / (a + c)) +
    b ^ 2 * (1 / (b + c) + 1 / (a + b)) > a + b + c := by
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have hc1 : 0 < c := hc
  have h1 : 0 < a + b + c := by linarith
  have h2 : 0 < a + c := by nlinarith
  have h3 : 0 < b + c := by nlinarith
  have h4 : 0 < a + b := by nlinarith
  have h5 : (a ^ 2 + a * c + c ^ 2) * (1 / (a + b + c) + 1 / (a + c)) +
    b ^ 2 * (1 / (b + c) + 1 / (a + b)) - (a + b + c) > 0 := by
    have h6 : 0 < (a + b + c) * (a + c) * (b + c) * (a + b) := by positivity
    have h7 : (a ^ 2 + a * c + c ^ 2) * (1 / (a + b + c) + 1 / (a + c)) +
        b ^ 2 * (1 / (b + c) + 1 / (a + b)) - (a + b + c) =
        ((a ^ 2 + a * c + c ^ 2) * ((a + c) * (b + c) * (a + b) + (a + b + c) * (b + c) * (a + b)) + b ^ 2 * ((a + b + c) * (a + c) * (a + b) + (a + b + c) * (a + c) * (b + c)) - (a + b + c) * ((a + b + c) * (a + c) * (b + c) * (a + b)) ) / ((a + b + c) * (a + c) * (b + c) * (a + b)) := by
      field_simp
      ring
    rw [h7] at *
    apply div_pos
    · -- To prove that the numerator is positive
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        mul_pos (show 0 < a + b + c by linarith) (show 0 < a + c by nlinarith), 
        mul_pos (show 0 < a + b + c by linarith) (show 0 < b + c by nlinarith), 
        mul_pos (show 0 < a + b + c by linarith) (show 0 < a + b by nlinarith), 
        mul_pos (show 0 < a + c by nlinarith) (show 0 < b + c by nlinarith), 
        mul_pos (show 0 < a + c by nlinarith) (show 0 < a + b by nlinarith), 
        mul_pos (show 0 < b + c by nlinarith) (show 0 < a + b by nlinarith)
      ]
    · -- To prove that the denominator is positive
      positivity
  linarith