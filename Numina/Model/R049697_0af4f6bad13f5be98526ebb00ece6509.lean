import Mathlib
open Real

theorem inequalities_3328
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a + b + c = 7) :
    2 * c / (a + b) + 2 * a / (b + c) + 2 * b / (c + a) ≥ 3 := by
  have h1 : a + b + c = 7 := h

  have ha1 : 0 < a + b := by linarith
  have hb1 : 0 < b + c := by linarith
  have hc1 : 0 < c + a := by linarith
  
  have hle1 : 2 * c / (a + b) + 2 * a / (b + c) + 2 * b / (c + a) - 3 ≥ 0 := by
    have hle1 : 2 * c / (a + b) + 2 * a / (b + c) + 2 * b / (c + a) - 3 = 
      (2 * c * (b + c) * (c + a) + 2 * a * (a + b) * (c + a) + 2 * b * (a + b) * (b + c) - 3 * (a + b) * (b + c) * (c + a)) / ((a + b) * (b + c) * (c + a)) := by
      field_simp
      <;> ring_nf <;> linarith [h]
    rw [hle1]
    
    have hdenom_pos : 0 < (a + b) * (b + c) * (c + a) := by positivity
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
                sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (a + c - b),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
                ]
    all_goals linarith

  linarith