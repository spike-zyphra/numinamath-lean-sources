import Mathlib
theorem inequalities_597888 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 2) :
a * b / (1 + c ^ 2) + b * c / (1 + a ^ 2) + c * a / (1 + b ^ 2) ≤ 1:= by
  have h1 : c = 2 - a - b := by linarith
  rw [h1]
  have hc1 : 0 ≤ 2 - a - b := by nlinarith [show 0 ≤ c by linarith [hc]]
  have h2 : 0 < 1 + (2 - a - b) ^ 2 := by nlinarith [hc1]
  have h3 : 0 < 1 + a ^ 2 := by nlinarith [ha]
  have h4 : 0 < 1 + b ^ 2 := by nlinarith [hb]
  have h7 : a * b / (1 + (2 - a - b) ^ 2) + b * (2 - a - b) / (1 + a ^ 2) + (2 - a - b) * a / (1 + b ^ 2) - 1 ≤ 0 := by
    have h12 : a * b / (1 + (2 - a - b) ^ 2) + b * (2 - a - b) / (1 + a ^ 2) + (2 - a - b) * a / (1 + b ^ 2) - 1 =
        (a * b * (1 + a ^ 2) * (1 + b ^ 2) + b * (2 - a - b) * (1 + (2 - a - b) ^ 2) * (1 + b ^ 2) + (2 - a - b) * a * (1 + (2 - a - b) ^ 2) * (1 + a ^ 2) - (1 + (2 - a - b) ^ 2) * (1 + a ^ 2) * (1 + b ^ 2)) / ((1 + (2 - a - b) ^ 2) * (1 + a ^ 2) * (1 + b ^ 2)) := by 
      field_simp 
      ring
    rw [h12]
    have h13 : (a * b * (1 + a ^ 2) * (1 + b ^ 2) + b * (2 - a - b) * (1 + (2 - a - b) ^ 2) * (1 + b ^ 2) + (2 - a - b) * a * (1 + (2 - a - b) ^ 2) * (1 + a ^ 2) - (1 + (2 - a - b) ^ 2) * (1 + a ^ 2) * (1 + b ^ 2)) ≤ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), 
          sq_nonneg (a * b - b * (2 - a - b)), sq_nonneg (b * (2 - a - b) - (2 - a - b) * a), sq_nonneg ((2 - a - b) * a - a * b),
          mul_nonneg ha hb, mul_nonneg ha (show 0 ≤ (2 - a - b) by linarith), 
          mul_nonneg (show 0 ≤ (2 - a - b) by linarith) hb, 
          sq_nonneg (a + b - (2 - a - b)), sq_nonneg (a * b), sq_nonneg (a * (2 - a - b)), sq_nonneg (b * (2 - a - b)), 
          mul_nonneg (sq_nonneg (a - 1)) (sq_nonneg (b - 1)), 
          mul_nonneg (sq_nonneg (b - 1)) (sq_nonneg ((2 - a - b) - 1)), 
          mul_nonneg (sq_nonneg (a - 1)) (sq_nonneg ((2 - a - b) - 1))]
    apply div_nonpos_of_nonpos_of_nonneg 
    linarith
    positivity
  linarith