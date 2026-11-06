import Mathlib

theorem inequalities_600882 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 + b * c) / (b + 3 * c) + (b^2 + c * a) / (c + 3 * a) +
    (c^2 + a * b) / (a + 3 * b) ≥
    (a + b + c) / 2 := by 
  have hb1 : 0 < b := hb
  have hc1 : 0 < c := hc
  have ha1 : 0 < a := ha
  have hb2 : 0 < b + 3 * c := by
    nlinarith
  have hc2 : 0 < c + 3 * a := by
    nlinarith
  have ha2 : 0 < a + 3 * b := by 
    nlinarith
  have h1 : (a^2 + b * c) / (b + 3 * c) + (b^2 + c * a) / (c + 3 * a) + (c^2 + a * b) / (a + 3 * b) - (a + b + c) / 2 ≥ 0 := by
    have h2 : 0 < (b + 3 * c) * (c + 3 * a) * (a + 3 * b) := by
      positivity
    have h3 : (a^2 + b * c) / (b + 3 * c) + (b^2 + c * a) / (c + 3 * a) + (c^2 + a * b) / (a + 3 * b) - (a + b + c) / 2 =
          ((a^2 + b * c) * (c + 3 * a) * (a + 3 * b) + (b^2 + c * a) * (b + 3 * c) * (a + 3 * b) + (c^2 + a * b) * (b + 3 * c) * (c + 3 * a) - (a + b + c) / 2 * ((b + 3 * c) * (c + 3 * a) * (a + 3 * b)) ) / ((b + 3 * c) * (c + 3 * a) * (a + 3 * b)) := by 
      field_simp 
      ring
    rw [h3] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
              sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
              sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
              sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
              mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
              mul_pos ha (show 0 < a * b by nlinarith), 
              mul_pos hb (show 0 < a * c by nlinarith), 
              mul_pos hc (show 0 < b * a by nlinarith)]
    all_goals 
      positivity 
  linarith 
  all_goals 
    positivity