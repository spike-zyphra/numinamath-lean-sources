import Mathlib

theorem algebra_605563 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 2 / 3) :
    a * b / (a + b) + b * c / (b + c) + c * a / (c + a) ≥
    (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) := by

  have h2 : 0 < a * b := by positivity
  have h3 : 0 < b * c := by positivity
  have h4 : 0 < c * a := by positivity

  have h5 : 0 < a + b := by linarith
  have h6 : 0 < b + c := by linarith
  have h7 : 0 < c + a := by linarith
  have h8 : 0 < a ^ 3 + b ^ 3 + c ^ 3 := by positivity
  have h9 : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) - (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) ≥ 0 := by
    have pos1 : 0 < (a + b) * (b + c) * (c + a) := by positivity
    have pos2 : 0 < a ^ 3 + b ^ 3 + c ^ 3 := by positivity
    have pos3 : 0 < (a + b) * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3) := by positivity
    have h10 : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) - (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) =
          ( (a * b) * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3 ) +
            (b * c) * (a + b) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3 ) +
            (c * a) * (a + b) * (b + c) * (a ^ 3 + b ^ 3 + c ^ 3 ) -
            (a + b + c) * (a + b) * (b + c) * (c + a)
          ) / ( (a + b) * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3 ) ) := by
      field_simp
      ring
    rw [h10] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, 
          mul_pos hb hc, mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
          mul_pos (show 0 < a * b by positivity) (show 0 < c * a by positivity), 
          mul_pos (show 0 < b * c by positivity) (show 0 < c * a by positivity), 
          sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
    all_goals positivity
  linarith