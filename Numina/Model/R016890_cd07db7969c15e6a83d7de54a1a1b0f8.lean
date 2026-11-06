import Mathlib

theorem inequalities_313275 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3/5 ≤ (b + c - a)^2/(a^2 + (b + c)^2) + (c + a - b)^2/(b^2 + (c + a)^2) +
    (a + b - c)^2/(c^2 + (a + b)^2) := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : 0 < a ^ 2 + (b + c) ^ 2 := by
    positivity
  have h3 : 0 < b ^ 2 + (c + a) ^ 2 := by
    positivity
  have h4 : 0 < c ^ 2 + (a + b) ^ 2 := by
    positivity
  have h5 : (b + c - a)^2/(a^2 + (b + c)^2) + (c + a - b)^2/(b^2 + (c + a)^2) +
      (a + b - c)^2/(c^2 + (a + b)^2) - 3/5 ≥ 0 := by
    have h6 : (b + c - a)^2/(a^2 + (b + c)^2) + (c + a - b)^2/(b^2 + (c + a)^2) +
        (a + b - c)^2/(c^2 + (a + b)^2) - 3/5 =
        (5 * ((b + c - a) ^ 2 * (b ^ 2 + (c + a) ^ 2) * (c ^ 2 + (a + b) ^ 2) ) + 5 * ((c + a - b) ^ 2 * (a ^ 2 + (b + c) ^ 2) * (c ^ 2 + (a + b) ^ 2) ) + 5 * ((a + b - c) ^ 2 * (a ^ 2 + (b + c) ^ 2) * (b ^ 2 + (c + a) ^ 2) ) - 3 * (a ^ 2 + (b + c) ^ 2) * (b ^ 2 + (c + a) ^ 2) * (c ^ 2 + (a + b) ^ 2) ) / (5 * (a ^ 2 + (b + c) ^ 2) * (b ^ 2 + (c + a) ^ 2) * (c ^ 2 + (a + b) ^ 2) ) := by
      field_simp
      ring
    rw [h6]
    have h7 : 5 * ((b + c - a) ^ 2 * (b ^ 2 + (c + a) ^ 2) * (c ^ 2 + (a + b) ^ 2) ) + 5 * ((c + a - b) ^ 2 * (a ^ 2 + (b + c) ^ 2) * (c ^ 2 + (a + b) ^ 2) ) + 5 * ((a + b - c) ^ 2 * (a ^ 2 + (b + c) ^ 2) * (b ^ 2 + (c + a) ^ 2) ) - 3 * (a ^ 2 + (b + c) ^ 2) * (b ^ 2 + (c + a) ^ 2) * (c ^ 2 + (a + b) ^ 2) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)), 
          sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc
      ]
    have h8 : (5 * ((b + c - a) ^ 2 * (b ^ 2 + (c + a) ^ 2) * (c ^ 2 + (a + b) ^ 2) ) + 5 * ((c + a - b) ^ 2 * (a ^ 2 + (b + c) ^ 2) * (c ^ 2 + (a + b) ^ 2) ) + 5 * ((a + b - c) ^ 2 * (a ^ 2 + (b + c) ^ 2) * (b ^ 2 + (c + a) ^ 2) ) - 3 * (a ^ 2 + (b + c) ^ 2) * (b ^ 2 + (c + a) ^ 2) * (c ^ 2 + (a + b) ^ 2) ) / (5 * (a ^ 2 + (b + c) ^ 2) * (b ^ 2 + (c + a) ^ 2) * (c ^ 2 + (a + b) ^ 2) ) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith