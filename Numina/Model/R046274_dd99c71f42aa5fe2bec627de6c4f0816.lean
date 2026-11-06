import Mathlib

theorem inequalities_86438 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    4 ≤ (3 - b) / (a + 1) + (a + 1) / (b + 1) + (b + 1) / (c + 1) := by

  have h1 : c = 1 - a - b := by linarith
  rw [show c = 1 - a - b by linarith] 
  have h2 : a + 1 > 0 := by linarith 
  have h3 : b + 1 > 0 := by linarith 
  have h4 : (1 - a - b) + 1 > 0 := by nlinarith 
  have h5 : (3 - b) / (a + 1) + (a + 1) / (b + 1) + (b + 1) / ((1 - a - b) + 1) - 4 ≥ 0 := by
    have pos1 : a + 1 > 0 := by linarith 
    have pos2 : b + 1 > 0 := by linarith 
    have pos3 : (1 - a - b) + 1 > 0 := by nlinarith 
    have h6 : (3 - b) / (a + 1) + (a + 1) / (b + 1) + (b + 1) / ((1 - a - b) + 1) - 4 =
        ( (3 - b) * (b + 1) * ((1 - a - b) + 1) + (a + 1) ^ 2 * ((1 - a - b) + 1) + (b + 1) ^ 2 * (a + 1) - 4 * (a + 1) * (b + 1) * ((1 - a - b) + 1) ) / ( (a + 1) * (b + 1) * ((1 - a - b) + 1) ) := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - (1 - a - b)), sq_nonneg (a - (1 - a - b)), 
                  sq_nonneg (a + b - (1 - a - b)), 
                  mul_nonneg ha hb, 
                  mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), 
                  mul_nonneg ha (show 0 ≤ 1 - a - b by nlinarith), 
                  hsum, mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)
                ]
    positivity
  linarith