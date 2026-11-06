import Mathlib

theorem inequalities_116041
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 ≤ (1 + a * b) / (1 + a) + (1 + b * c) / (1 + b) + (1 + c * a) / (1 + c) := by
  have pos1 : 0 < (1 + a) := by linarith
  have pos2 : 0 < (1 + b) := by linarith
  have pos3 : 0 < (1 + c) := by linarith
  have h4 : (1 + a * b) / (1 + a) + (1 + b * c) / (1 + b) + (1 + c * a) / (1 + c) - 3 ≥ 0 := by
    have h5 : (1 + a * b) / (1 + a) + (1 + b * c) / (1 + b) + (1 + c * a) / (1 + c) - 3 =
        ( (1 + a * b) * (1 + b) * (1 + c) + (1 + b * c) * (1 + a) * (1 + c) + (1 + c * a) * (1 + a) * (1 + b) - 3 * (1 + a) * (1 + b) * (1 + c) ) / ( (1 + a) * (1 + b) * (1 + c) ) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    have h11 : 0 ≤ ( (1 + a * b) * (1 + b) * (1 + c) + (1 + b * c) * (1 + a) * (1 + c) + (1 + c * a) * (1 + a) * (1 + b) - 3 * (1 + a) * (1 + b) * (1 + c) ) := by
      have h21 : a * b * c = 1 := habc
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < a * b * c by nlinarith), 
      sq_nonneg (a * b * c - 1), 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith)
      ]
    linarith
    positivity
  linarith