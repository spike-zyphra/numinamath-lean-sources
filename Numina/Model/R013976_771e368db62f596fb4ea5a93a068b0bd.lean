import Mathlib

theorem inequalities_70188 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 1 / (a + b + c) ^ 2 ≥
    7 / 25 * (1 / a + 1 / b + 1 / c + 1 / (a + b + c)) ^ 2 := by
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have hc1 : 0 < c := hc
  have h1 : 0 < a * b * c * (a + b + c) := by positivity
  have h2 : 0 < a ^ 2 * b ^ 2 * c ^ 2 * (a + b + c) ^ 2 := by positivity
  have h3 : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 1 / (a + b + c) ^ 2 -
      7 / 25 * (1 / a + 1 / b + 1 / c + 1 / (a + b + c)) ^ 2 ≥ 0 := by
    have h5 : 0 < a ^ 2 * b ^ 2 * c ^ 2 * (a + b + c) ^ 2 := by positivity
    have h5' : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 1 / (a + b + c) ^ 2 -
        7 / 25 * (1 / a + 1 / b + 1 / c + 1 / (a + b + c)) ^ 2 =
        ( (b^2 * c^2 * (a + b + c) ^ 2 + a^2 * c^2 * (a + b + c) ^ 2 + a^2 * b^2 * (a + b + c) ^ 2 + a^2 * b^2 * c^2 ) - 7 / 25 * ( (b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) + a * b * c ) ^ 2 ) ) / (a^2 * b^2 * c^2 * (a + b + c) ^ 2) := by
      field_simp
      ring
    rw [h5']
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a * (a - b) ), sq_nonneg (a * (a - c) ), sq_nonneg (b * (b - a) ), sq_nonneg (b * (b - c) ), sq_nonneg (c * (c - a) ), sq_nonneg (c * (c - b) ), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (show 0 < a * b by positivity) (show 0 < a * c by positivity), 
            mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
            mul_pos (show 0 < a * c by positivity) (show 0 < b * c by positivity) ]
    all_goals positivity
  linarith
  all_goals positivity