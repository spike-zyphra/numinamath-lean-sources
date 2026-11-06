import Mathlib

theorem inequalities_103042 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 2 / 3) :
    a * b / (a + b) + b * c / (b + c) + c * a / (c + a) ≥
    (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) := by

  have hb1 : 0 < b := hb
  have ha1 : 0 < a := ha
  have hc1 : 0 < c := hc

  have h1 : 0 < (a + b) * (b + c) * (c + a) := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h2 : 0 < a ^ 3 + b ^ 3 + c ^ 3 := by 
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h3 : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) - (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) ≥ 0 := by
    have h4 : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) - (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) =
        ( (a * b * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3) + 
            b * c * (a + b) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3) + 
            c * a * (a + b) * (b + c) * (a ^ 3 + b ^ 3 + c ^ 3) - 
            (a + b + c) * (a + b) * (b + c) * (c + a) ) / 
              ( (a + b) * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3) ) ) := by 
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith), mul_pos (show 0 < c * a by nlinarith) (show 0 < a * b by nlinarith), sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2), mul_pos (show 0 < a * b * c by nlinarith [habc]) ha, mul_pos (show 0 < a * b * c by nlinarith [habc]) hb, mul_pos (show 0 < a * b * c by nlinarith [habc]) hc, habc]
    all_goals
      positivity

  linarith