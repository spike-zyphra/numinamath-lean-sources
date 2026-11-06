import Mathlib

theorem inequalities_597136 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a < 1) (h2 : b < 1) :
    a / (1 - a ^ 2) + b / (1 - b ^ 2) ≥ (a + b) / (1 - a * b) +
    (a + b) / (1 - a * b) * ((a - b) / (1 + a * b)) ^ 2 := by
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  have h1c : 0 < 1 - a ^ 2 := by nlinarith
  have h1d : 0 < 1 - b ^ 2 := by nlinarith
  have h1e : 0 < 1 - a * b := by nlinarith
  have h1f : 0 < 1 + a * b := by nlinarith
  have h1g : 0 < (1 - a^2) * (1 - b^2) * (1 - a * b) * (1 + a * b) ^ 2 := by positivity
  have h3 : a / (1 - a ^ 2) + b / (1 - b ^ 2) - ((a + b) / (1 - a * b) +
      (a + b) / (1 - a * b) * ((a - b) / (1 + a * b)) ^ 2) ≥ 0 := by
    have h11 : 0 < (1 - a^2) * (1 - b^2) * (1 - a * b) * (1 + a * b) ^ 2 := h1g
    have h3' : a / (1 - a ^ 2) + b / (1 - b ^ 2) - ((a + b) / (1 - a * b) +
        (a + b) / (1 - a * b) * ((a - b) / (1 + a * b)) ^ 2) =
        ( a * (1 - b^2) * (1 - a * b) * (1 + a * b) ^ 2 + b * (1 - a^2) * (1 - a * b) * (1 + a * b) ^ 2
          - ( (a + b) * (1 - a^2) * (1 - b^2) * (1 + a * b) ^ 2 + (a + b) * (1 - a^2) * (1 - b^2) * (a - b)^2 ) ) / ( (1 - a^2) * (1 - b^2) * (1 - a * b) * (1 + a * b) ^ 2 ) := by
      field_simp
      ring
    rw [h3']
    apply div_nonneg
    nlinarith [mul_pos ha hb, mul_pos ha (show 0 < 1 - a by linarith), 
          mul_pos hb (show 0 < 1 - b by linarith), 
          mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - b by linarith), 
          mul_pos (show 0 < 1 - a ^ 2 by nlinarith) (show 0 < 1 - b ^ 2 by nlinarith), 
          mul_pos (show 0 < 1 - a * b by nlinarith) (show 0 < 1 + a * b by nlinarith), 
          sq_nonneg (a - b), sq_nonneg (a * b - a * a), sq_nonneg (a * b - b * b), 
          sq_nonneg (a - 0.5), sq_nonneg (b - 0.5), 
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith) ]
    all_goals positivity
  linarith