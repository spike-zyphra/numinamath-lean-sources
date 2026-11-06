import Mathlib

theorem inequalities_318329 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) := by 
  have ha1 : 0 < 1 + 2 * a := by linarith
  have hb1 : 0 < 1 + 2 * b := by linarith
  have hc1 : 0 < 1 + 2 * c := by linarith
  
  have h : 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1 ≥ 0 := by
    have h1 : (1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1) =
        ((1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) - (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) / ((1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) := by 
      field_simp 
      ring
    rw [h1] at *
    have num_nonneg : (1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) - (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) ≥ 0 := by 
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc
        ]
    have denom_pos : (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) > 0 := by 
      positivity 
    apply div_nonneg 
    linarith 
    linarith 
  linarith