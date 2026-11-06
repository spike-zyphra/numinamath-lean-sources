import Mathlib

theorem inequalities_38909 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = a + b + c + 2) :
    a / (b + 1) + b / (c + 1) + c / (a + 1) ≥ 2 := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h2 : 0 < b + 1 := by linarith [hb]
  have h3 : 0 < c + 1 := by linarith [hc];
  have h4 : 0 < a + 1 := by linarith [ha];
  have h5 : a / (b + 1) + b / (c + 1) + c / (a + 1) - 2 ≥ 0 := by
    have h6 : a/(b + 1) + b/(c + 1) + c/(a + 1) - 2 =
        (a * (c + 1) * (a + 1) + b * (b + 1) * (a + 1) + c * (b + 1) * (c + 1) - 2 * (b + 1) * (c + 1) * (a + 1)) / ((b + 1) * (c + 1) * (a + 1)) := by 
      field_simp 
      ring 
    rw [h6]
    have h7 : (b + 1) * (c + 1) * (a + 1) > 0 := by positivity
    have h8 : a * (c + 1) * (a + 1) + b * (b + 1) * (a + 1) + c * (b + 1) * (c + 1) - 2 * (b + 1) * (c + 1) * (a + 1) ≥ 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply div_nonneg 
    linarith 
    linarith 
  linarith