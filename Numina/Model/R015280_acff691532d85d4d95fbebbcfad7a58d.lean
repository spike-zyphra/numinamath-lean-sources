import Mathlib

theorem inequalities_598217 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    36 ≤ 1 / a + 4 / b + 9 / c := by
  have h1 : 1 / a + 4 / b + 9 / c - 36 ≥ 0 := by
    have ha1 : 0 < a * b * c := by
      positivity
    have h2 : 1 / a + 4 / b + 9 / c - 36 = (b * c + 4 * a * c + 9 * a * b - 36 * (a * b * c)) / (a * b * c) := by
      field_simp 
      ring 
    rw [h2] 
    have h3 : b * c + 4 * a * c + 9 * a * b - 36 * (a * b * c) ≥ 0 := by 
      have h4 : c = 1 - a - b := by
        linarith 
      rw [h4]
      nlinarith [sq_nonneg (a - 1 / 6), sq_nonneg (b - 1 / 3), sq_nonneg ((1 - a - b) - 1 / 2),
          mul_pos ha hb, mul_pos hb (show (0 : ℝ) < (1 - a - b) by nlinarith), 
          mul_pos ha (show (0 : ℝ) < (1 - a - b) by nlinarith)]
    apply div_nonneg 
    linarith [h3]
    positivity
  linarith