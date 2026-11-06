import Mathlib

theorem inequalities_601143
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d) :
    4 / 3 ≤ c / (a + 2 * b) + d / (b + 2 * c) + a / (c + 2 * d) + b / (d + 2 * a) := by
  have h1 : 0 < (a + 2 * b) * (b + 2 * c) * (c + 2 * d) * (d + 2 * a) := by
    positivity
  have h2 : c / (a + 2 * b) + d / (b + 2 * c) + a / (c + 2 * d) + b / (d + 2 * a) - 4 / 3 ≥ 0 := by
    have pos1 : 0 < (a + 2 * b) * (b + 2 * c) * (c + 2 * d) * (d + 2 * a) := by positivity 
    have h3 : c / (a + 2 * b) + d / (b + 2 * c) + a / (c + 2 * d) + b / (d + 2 * a) - 4 / 3 =
        (c * (b + 2 * c) * (c + 2 * d) * (d + 2 * a) +
        d * (a + 2 * b) * (c + 2 * d) * (d + 2 * a) +
        a * (a + 2 * b) * (b + 2 * c) * (d + 2 * a) +
        b * (a + 2 * b) * (b + 2 * c) * (c + 2 * d) - 4 / 3 * ( (a + 2 * b) * (b + 2 * c) * (c + 2 * d) * (d + 2 * a) ) ) / ( (a + 2 * b) * (b + 2 * c) * (c + 2 * d) * (d + 2 * a) ) := by
      field_simp
      ring
    rw [h3]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          sq_nonneg (a + 2 * b - (c + 2 * d)), sq_nonneg (b + 2 * c - (d + 2 * a)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd,
          mul_pos (show 0 < a + 2 * b from by linarith) (show 0 < b + 2 * c from by linarith), 
          mul_pos (show 0 < b + 2 * c from by linarith) (show 0 < c + 2 * d from by linarith), 
          mul_pos (show 0 < c + 2 * d from by linarith) (show 0 < d + 2 * a from by linarith), 
          mul_pos (show 0 < d + 2 * a from by linarith) (show 0 < a + 2 * b from by linarith)
          ]
    all_goals positivity
  linarith [h2]