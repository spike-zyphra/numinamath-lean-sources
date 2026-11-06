import Mathlib

theorem inequalities_597101 (a b c d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a) :
    (1 + c / (a + b)) * (1 + d / (b + c)) * (1 + a / (c + d)) * (1 + b / (d + a)) ≥ 3 / 2 := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b + c := by linarith
  have h3 : 0 < c + d := by linarith
  have h4 : 0 < d + a := by linarith
  have h5 : 0 < a := ha
  have h6 : 0 < b := by linarith
  have h7 : 0 < c := by linarith
  have h8 : 0 < d := hd
  have h10 : 0 < (a + b) * (b + c) * (c + d) * (d + a) := by positivity
  have h11 : (1 + c / (a + b)) * (1 + d / (b + c)) * (1 + a / (c + d)) * (1 + b / (d + a)) - 3 / 2 ≥ 0 := by
    have h12 : 0 < (a + b) * (b + c) * (c + d) * (d + a) := h10
    have h13 : (1 + c / (a + b)) * (1 + d / (b + c)) * (1 + a / (c + d)) * (1 + b / (d + a)) - 3 / 2 =
        ((a + b + c) * (b + c + d) * (c + d + a) * (d + a + b) - 3 / 2 * ((a + b) * (b + c) * (c + d) * (d + a))) / ((a + b) * (b + c) * (c + d) * (d + a)) := by
      field_simp
      ring
    rw [h13]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c),
          mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ b - c by linarith), 
          mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ c - d by linarith), 
          mul_nonneg (show 0 ≤ b - c by linarith) (show 0 ≤ c - d by linarith), 
          mul_pos ha (show 0 < b by linarith), 
          mul_pos ha (show 0 < c by linarith), 
          mul_pos ha (show 0 < d by linarith), 
          mul_pos (show 0 < b by linarith) (show 0 < c by linarith), 
          mul_pos (show 0 < b by linarith) (show 0 < d by linarith), 
          mul_pos (show 0 < c by linarith) (show 0 < d by linarith)
        ]
    all_goals positivity
  linarith