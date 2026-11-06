import Mathlib

theorem inequalities_601281
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d) :
    (a - b) / (b + c) + (b - c) / (c + d) + (c - d) / (d + a) + (d - a) / (a + b) ≥ 0 := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + d := by linarith
  have h3 : 0 < d + a := by linarith
  have h4 : 0 < a + b := by linarith
  have h5 : (a - b) / (b + c) + (b - c) / (c + d) + (c - d) / (d + a) + (d - a) / (a + b) =
      ((a - b) * (c + d) * (d + a) * (a + b) + (b - c) * (b + c) * (d + a) * (a + b) + (c - d) * (b + c) * (c + d) * (a + b) + (d - a) * (b + c) * (c + d) * (d + a)) / ((b + c) * (c + d) * (d + a) * (a + b)) := by
    field_simp
    <;> ring
  rw [h5] at *
  apply div_nonneg
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
            sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
            sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c),
            mul_pos ha hb, mul_pos ha hc, mul_pos ha hd,
            mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
            mul_pos (show 0 < b + c by linarith) (show 0 < c + d by linarith),
            mul_pos (show 0 < b + c by linarith) (show 0 < d + a by linarith),
            mul_pos (show 0 < b + c by linarith) (show 0 < a + b by linarith),
            mul_pos (show 0 < c + d by linarith) (show 0 < d + a by linarith),
            mul_pos (show 0 < c + d by linarith) (show 0 < a + b by linarith),
            mul_pos (show 0 < d + a by linarith) (show 0 < a + b by linarith)
          ]
  positivity