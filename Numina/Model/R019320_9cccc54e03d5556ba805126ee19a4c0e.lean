import Mathlib

theorem inequalities_1808 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) :
    3 ≤ 1 / (a * b) + 1 / (b * c) + 1 / (c * a) := by

  have h1 : 0 < a * b := by nlinarith
  have h2 : 0 < b * c := by nlinarith
  have h3 : 0 < c * a := by nlinarith

  have h4 : 1 / (a * b) + 1 / (b * c) + 1 / (c * a) - 3 ≥ 0 := by 
    have h5 : 1 / (a * b) + 1 / (b * c) + 1 / (c * a) - 3 =
        ( (c + a + b) - 3 * (a * b * c) ) / (a * b * c) := by 
      field_simp 
      ring 
    rw [h5]
    have h6 : (c + a + b) - 3 * (a * b * c) ≥ 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h
      ]
    have h7 : a * b * c > 0 := by 
      positivity 
    apply div_nonneg 
    all_goals 
      linarith 
  linarith