import Mathlib

theorem inequalities_598494 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≥ 1) :
    a + b + c ≥ a * b + b * c + c * a := by
  have h1 : 0 < a + b + 1 := by nlinarith
  have h2 : 0 < b + c + 1 := by nlinarith
  have h3 : 0 < c + a + 1 := by nlinarith
  have h4 : (a + b + 1) * (b + c + 1) * (c + a + 1) > 0 := by
    positivity
  -- Derive the inequality without denominators
  have h6 : (b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) ≥ (a + b + 1) * (b + c + 1) * (c + a + 1) := by 
    have h7 : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1 ≥ 0 := by linarith
    have h8 : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1 =
        ((b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (c + a + 1)) / ((a + b + 1) * (b + c + 1) * (c + a + 1)) := by 
      field_simp
      ring
    rw [h8] at h7
    have h9 : (b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (c + a + 1) ≥ 0 := by 
      have pos1 : (a + b + 1) * (b + c + 1) * (c + a + 1) > 0 := by positivity 
      apply (div_nonneg_iff).mp at h7 
      cases h7 with 
      | inl h1 =>
        nlinarith 
      | inr h2 =>
        nlinarith 
    linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
          mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith)]