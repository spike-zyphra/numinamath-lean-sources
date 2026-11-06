import Mathlib

theorem inequalities_598335 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 ≤ (1 + a * b) / (1 + a) + (1 + b * c) / (1 + b) + (1 + c * a) / (1 + c) := by
  have h1 : (1 + a * b) / (1 + a) + (1 + b * c) / (1 + b) + (1 + c * a) / (1 + c) - 3 ≥ 0 := by
    have h2 : 0 < a * b * c := by
      have hab1 : a * b > 0 := mul_pos ha hb
      have habc1 : a * b * c > 0 := mul_pos hab1 hc
      linarith
    have h3 : a * b * c = 1 := habc
    have h4 : (1 + a * b) / (1 + a) + (1 + b * c) / (1 + b) + (1 + c * a) / (1 + c) - 3 =
        ((1 + a * b) * (1 + b) * (1 + c) + (1 + b * c) * (1 + a) * (1 + c) + (1 + c * a) * (1 + a) * (1 + b) - 3 * (1 + a) * (1 + b) * (1 + c)) / ((1 + a) * (1 + b) * (1 + c)) := by 
      field_simp
      ring
    rw [h4]
    have pos1 : 0 < (1 + a) * (1 + b) * (1 + c) := by 
      positivity
    have nonneg1 : ((1 + a * b) * (1 + b) * (1 + c) + (1 + b * c) * (1 + a) * (1 + c) + (1 + c * a) * (1 + a) * (1 + b) - 3 * (1 + a) * (1 + b) * (1 + c)) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          habc, mul_pos (show 0 < a * b from by nlinarith) (show 0 < c from hc), 
          sq_nonneg (a * b * c - 1), 
          mul_pos (show 0 < a by linarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < b by linarith) (show 0 < a * c by nlinarith)
        ]
    apply div_nonneg
    linarith [nonneg1]
    all_goals
      positivity
  linarith [h1]