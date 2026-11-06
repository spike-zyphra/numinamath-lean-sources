import Mathlib

open Real

theorem inequalities_309486 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    27 / 4 ≤ 1 / (a * (1 + b)) + 1 / (b * (1 + c)) + 1 / (c * (1 + a)) := by 
  have h1 : 0 < a * (1 + b) := by positivity
  have h2 : 0 < b * (1 + c) := by positivity
  have h3 : 0 < c * (1 + a) := by positivity

  have h4 : 1 / (a * (1 + b)) + 1 / (b * (1 + c)) + 1 / (c * (1 + a)) - 27 / 4 ≥ 0 := by 
    have h6 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h7 : 1 / (a * (1 + b)) + 1 / (b * (1 + c)) + 1 / (c * (1 + a)) - 27 / 4 =
        (4 * (b * (1 + c) * c * (1 + a)) + 4 * (a * (1 + b) * c * (1 + a)) + 4 * (a * (1 + b) * b * (1 + c)) - 27 * (a * (1 + b) * b * (1 + c) * c * (1 + a))) / (4 * (a * (1 + b) * b * (1 + c) * c * (1 + a))) := by 
      field_simp 
      ring
    rw [h7] at *
    have h8 : 4 * (b * (1 + c) * c * (1 + a)) + 4 * (a * (1 + b) * c * (1 + a)) + 4 * (a * (1 + b) * b * (1 + c)) - 27 * (a * (1 + b) * b * (1 + c) * c * (1 + a)) ≥ 0 := by
      have h9 : c = 1 - a - b := by linarith 
      rw [h9] 
      nlinarith [sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (b * (1 - a - b) - (1 - a - b) * a), sq_nonneg ( (1 - a - b) * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (b - (1 - a - b)), sq_nonneg ( (1 - a - b) - a), 
        mul_pos ha hb, mul_pos hb (show 0 < 1 - a - b by nlinarith [h, ha, hb, hc]), mul_pos ha (show 0 < 1 - a - b by nlinarith [h, ha, hb, hc]), 
        mul_nonneg (mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)) (show 0 ≤ (1 - a - b) by nlinarith [h, ha, hb, hc]), 
        mul_nonneg (mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ (1 - a - b) by nlinarith [h, ha, hb, hc])) (show 0 ≤ a by linarith), 
        mul_nonneg (mul_nonneg (show 0 ≤ (1 - a - b) by nlinarith [h, ha, hb, hc]) (show 0 ≤ a by linarith)) (show 0 ≤ b by linarith)
      ]
    have h10 : (4 * (b * (1 + c) * c * (1 + a)) + 4 * (a * (1 + b) * c * (1 + a)) + 4 * (a * (1 + b) * b * (1 + c)) - 27 * (a * (1 + b) * b * (1 + c) * c * (1 + a))) / (4 * (a * (1 + b) * b * (1 + c) * c * (1 + a))) ≥ 0 := by 
      apply div_nonneg 
      linarith 
      positivity 
    linarith 
  linarith