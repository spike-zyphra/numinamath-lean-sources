import Mathlib

theorem inequalities_193997 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a + b) + 1 / (b + c) + 1 / (c + a) > 3 / (a + b + c) := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b + c := by linarith
  have h3 : 0 < c + a := by linarith
  have h4 : 0 < a + b + c := by linarith
  have h5 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - 3 / (a + b + c) > 0 := by
    have pos1 : 0 < (a + b) * (b + c) * (c + a) * (a + b + c) := by positivity
    have h6 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - 3 / (a + b + c) =
      ((a + b + c) * ((b + c) * (c + a) + (a + b) * (c + a) + (a + b) * (b + c)) - 3 * (a + b) * (b + c) * (c + a)) /
      ((a + b) * (b + c) * (c + a) * (a + b + c)) := by
      field_simp
      ring
    rw [h6]
    have h7 : (a + b + c) * ((b + c) * (c + a) + (a + b) * (c + a) + (a + b) * (b + c)) - 3 * (a + b) * (b + c) * (c + a) > 0 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
    apply div_pos h7 (by positivity)
  linarith