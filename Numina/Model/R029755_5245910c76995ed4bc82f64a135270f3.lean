import Mathlib

theorem inequalities_227098 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    2 / 3 ≤ a / (b + 2 * c + 3 * d) + b / (c + 2 * d + 3 * a) +
    c / (d + 2 * a + 3 * b) + d / (a + 2 * b + 3 * c) := by 
  have h1 : 0 < b + 2 * c + 3 * d := by positivity
  have h2 : 0 < c + 2 * d + 3 * a := by positivity
  have h3 : 0 < d + 2 * a + 3 * b := by positivity
  have h4 : 0 < a + 2 * b + 3 * c := by positivity
  
  have h6 : a / (b + 2 * c + 3 * d) + b / (c + 2 * d + 3 * a) + 
    c / (d + 2 * a + 3 * b) + d / (a + 2 * b + 3 * c) - 2 / 3 ≥ 0 := by 
    have h7 : a / (b + 2 * c + 3 * d) + b / (c + 2 * d + 3 * a) + 
      c / (d + 2 * a + 3 * b) + d / (a + 2 * b + 3 * c) - 2 / 3 =
      (a * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c) + 
      b * (b + 2 * c + 3 * d) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c) + 
      c * (b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (a + 2 * b + 3 * c) + 
      d * (b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) - 2 / 3 * (b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c)) / ((b + 2 * c + 3 * d) * (c + 2 * d + 3 * a) * (d + 2 * a + 3 * b) * (a + 2 * b + 3 * c)) := by 
      field_simp 
      ring 
    rw [h7] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (a - d)), 
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - d)), 
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), sq_nonneg (c * (c - d)),
      sq_nonneg (d * (d - a)), sq_nonneg (d * (d - b)), sq_nonneg (d * (d - c)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
      mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
      mul_pos (show 0 < b + 2 * c + 3 * d by positivity) (show 0 < c + 2 * d + 3 * a by positivity), 
      mul_pos (show 0 < b + 2 * c + 3 * d by positivity) (show 0 < d + 2 * a + 3 * b by positivity), 
      mul_pos (show 0 < b + 2 * c + 3 * d by positivity) (show 0 < a + 2 * b + 3 * c by positivity), 
      mul_pos (show 0 < c + 2 * d + 3 * a by positivity) (show 0 < d + 2 * a + 3 * b by positivity), 
      mul_pos (show 0 < c + 2 * d + 3 * a by positivity) (show 0 < a + 2 * b + 3 * c by positivity), 
      mul_pos (show 0 < d + 2 * a + 3 * b by positivity) (show 0 < a + 2 * b + 3 * c by positivity)
    ]
    positivity
  linarith