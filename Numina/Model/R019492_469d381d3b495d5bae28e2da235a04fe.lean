import Mathlib

theorem inequalities_169306 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a - b) / (b + c) + (b - c) / (c + d) + (c - d) / (d + a) + (d - a) / (a + b) ≥ 0 := by
  have hb' : 0 < b + c := by linarith
  have hc' : 0 < c + d := by linarith
  have hd' : 0 < d + a := by linarith
  have ha' : 0 < a + b := by linarith
  have h1 : (a - b) / (b + c) + (b - c) / (c + d) + (c - d) / (d + a) + (d - a) / (a + b) =
      ((a - b) * (c + d) * (d + a) * (a + b) + 
       (b - c) * (b + c) * (d + a) * (a + b) + 
       (c - d) * (b + c) * (c + d) * (a + b) + 
       (d - a) * (b + c) * (c + d) * (d + a)) / ((b + c) * (c + d) * (d + a) * (a + b)) := by
    field_simp
    <;> ring_nf
  rw [h1]
  have h2 : (b + c) * (c + d) * (d + a) * (a + b) > 0 := by
    positivity
  have num_pos : ((a - b) * (c + d) * (d + a) * (a + b) + 
          (b - c) * (b + c) * (d + a) * (a + b) + 
          (c - d) * (b + c) * (c + d) * (a + b) + 
          (d - a) * (b + c) * (c + d) * (d + a)) ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
            sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c),
            mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
  apply div_nonneg
  linarith
  all_goals linarith