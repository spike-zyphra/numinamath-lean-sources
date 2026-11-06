import Mathlib

theorem inequalities_223049
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h1 : a + b > c)
    (h2 : a + c > b)
    (h3 : b + c > a) :
    a * b * c ≥ (a + b - c) * (b + c - a) * (c + a - b) := by
  have h4 : 0 < a + b - c := by linarith
  have h5 : 0 < b + c - a := by linarith
  have h6 : 0 < c + a - b := by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos h4 h5, mul_pos h5 h6, mul_pos h4 h6
        ]