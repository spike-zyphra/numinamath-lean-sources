import Mathlib

theorem inequalities_152855 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
    3 / 2 ≤ 1 / (a ^ 2 * (b + c)) + 1 / (b ^ 2 * (c + a)) + 1 / (c ^ 2 * (a + b)) := by
  have ha2 : 0 < a ^ 2 * (b + c) := by positivity
  have hb2 : 0 < b ^ 2 * (c + a) := by positivity
  have hc2 : 0 < c ^ 2 * (a + b) := by positivity
  have h3 : 1 / (a ^ 2 * (b + c)) + 1 / (b ^ 2 * (c + a)) + 1 / (c ^ 2 * (a + b)) - 3 / 2 ≥ 0 := by
    have h4 : 1 / (a ^ 2 * (b + c)) + 1 / (b ^ 2 * (c + a)) + 1 / (c ^ 2 * (a + b)) - 3 / 2 =
        (2 * (b ^ 2 * (c + a) * c ^ 2 * (a + b) ) + 2 * (a ^ 2 * (b + c) * c ^ 2 * (a + b) ) + 2 * (a ^ 2 * (b + c) * b ^ 2 * (c + a) ) - 3 * (a ^ 2 * (b + c) * b ^ 2 * (c + a) * c ^ 2 * (a + b) ) ) / (2 * (a ^ 2 * (b + c) * b ^ 2 * (c + a) * c ^ 2 * (a + b)) ) := by
      field_simp
      ring
    rw [h4]
    have h5 : 2 * (b ^ 2 * (c + a) * c ^ 2 * (a + b) ) + 2 * (a ^ 2 * (b + c) * c ^ 2 * (a + b) ) + 2 * (a ^ 2 * (b + c) * b ^ 2 * (c + a) ) - 3 * (a ^ 2 * (b + c) * b ^ 2 * (c + a) * c ^ 2 * (a + b) ) ≥ 0 := by
      have h5 : a * b * c = 1 := habc
      have h8 : 3 * (a ^ 2 * (b + c) * b ^ 2 * (c + a) * c ^ 2 * (a + b) ) = 3 * (a * b * c) ^ 2 * ((b + c) * (c + a) * (a + b)) := by 
        ring
      rw [h8]
      rw [show a * b * c = 1 by linarith [habc] ]
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (b - c)), sq_nonneg (b * (c - a)), sq_nonneg (c * (a - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (show 0 < b + c by positivity) (show 0 < c + a by positivity),
          mul_pos (show 0 < c + a by positivity) (show 0 < a + b by positivity),
          mul_pos (show 0 < a + b by positivity) (show 0 < b + c by positivity),
          mul_pos (mul_pos ha hb) hc
      ]
    have h8 : (2 * (b ^ 2 * (c + a) * c ^ 2 * (a + b) ) + 2 * (a ^ 2 * (b + c) * c ^ 2 * (a + b) ) + 2 * (a ^ 2 * (b + c) * b ^ 2 * (c + a) ) - 3 * (a ^ 2 * (b + c) * b ^ 2 * (c + a) * c ^ 2 * (a + b) ) ) / (2 * (a ^ 2 * (b + c) * b ^ 2 * (c + a) * c ^ 2 * (a + b)) ) ≥ 0 := by
      apply div_nonneg 
      linarith [h5]
      positivity
    linarith 
  linarith