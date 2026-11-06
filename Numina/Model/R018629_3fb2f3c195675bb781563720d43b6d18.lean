import Mathlib

open Real

theorem inequalities_2684 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + 2 * b * c) / ((a + 2 * b) ^ 2 + (a + 2 * c) ^ 2) +
    (b ^ 2 + 2 * c * a) / ((b + 2 * c) ^ 2 + (b + 2 * a) ^ 2) +
    (c ^ 2 + 2 * a * b) / ((c + 2 * a) ^ 2 + (c + 2 * b) ^ 2) ≤ 1 / 2 := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h2 : 0 < (a + 2 * b) ^ 2 + (a + 2 * c) ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]

  have h3 : 0 < (b + 2 * c) ^ 2 + (b + 2 * a) ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]

  have h4 : 0 < (c + 2 * a) ^ 2 + (c + 2 * b) ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]

  have h5 : (a ^ 2 + 2 * b * c) / ((a + 2 * b) ^ 2 + (a + 2 * c) ^ 2) + (b ^ 2 + 2 * c * a) / ((b + 2 * c) ^ 2 + (b + 2 * a) ^ 2) + (c ^ 2 + 2 * a * b) / ((c + 2 * a) ^ 2 + (c + 2 * b) ^ 2) - 1 / 2 ≤ 0 := by
    have h6 : (a ^ 2 + 2 * b * c) / ((a + 2 * b) ^ 2 + (a + 2 * c) ^ 2) + (b ^ 2 + 2 * c * a) / ((b + 2 * c) ^ 2 + (b + 2 * a) ^ 2) + (c ^ 2 + 2 * a * b) / ((c + 2 * a) ^ 2 + (c + 2 * b) ^ 2) - 1 / 2 =
        (2 * ((a ^ 2 + 2 * b * c) * ((b + 2 * c) ^ 2 + (b + 2 * a) ^ 2) * ((c + 2 * a) ^ 2 + (c + 2 * b) ^ 2) ) +
          2 * ((b ^ 2 + 2 * c * a) * ((a + 2 * b) ^ 2 + (a + 2 * c) ^ 2) * ((c + 2 * a) ^ 2 + (c + 2 * b) ^ 2) ) + 
          2 * ((c ^ 2 + 2 * a * b) * ((a + 2 * b) ^ 2 + (a + 2 * c) ^ 2) * ((b + 2 * c) ^ 2 + (b + 2 * a) ^ 2) ) - 
          ((a + 2 * b) ^ 2 + (a + 2 * c) ^ 2) * ((b + 2 * c) ^ 2 + (b + 2 * a) ^ 2) * ((c + 2 * a) ^ 2 + (c + 2 * b) ^ 2) ) / (2 * ((a + 2 * b) ^ 2 + (a + 2 * c) ^ 2) * ((b + 2 * c) ^ 2 + (b + 2 * a) ^ 2) * ((c + 2 * a) ^ 2 + (c + 2 * b) ^ 2) ) := by
      field_simp
      ring
    rw [h6]

    have h77 : 2 * ((a + 2 * b) ^ 2 + (a + 2 * c) ^ 2) * ((b + 2 * c) ^ 2 + (b + 2 * a) ^ 2) * ((c + 2 * a) ^ 2 + (c + 2 * b) ^ 2) > 0 := by positivity

    have h7 : 2 * ((a ^ 2 + 2 * b * c) * ((b + 2 * c) ^ 2 + (b + 2 * a) ^ 2) * ((c + 2 * a) ^ 2 + (c + 2 * b) ^ 2) ) + 
          2 * ((b ^ 2 + 2 * c * a) * ((a + 2 * b) ^ 2 + (a + 2 * c) ^ 2) * ((c + 2 * a) ^ 2 + (c + 2 * b) ^ 2) ) + 
          2 * ((c ^ 2 + 2 * a * b) * ((a + 2 * b) ^ 2 + (a + 2 * c) ^ 2) * ((b + 2 * c) ^ 2 + (b + 2 * a) ^ 2) ) - 
          ((a + 2 * b) ^ 2 + (a + 2 * c) ^ 2) * ((b + 2 * c) ^ 2 + (b + 2 * a) ^ 2) * ((c + 2 * a) ^ 2 + (c + 2 * b) ^ 2) ≤ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (mul_pos ha hb) hc
      ]
    apply div_nonpos_of_nonpos_of_nonneg h7 (by positivity)
  
  linarith