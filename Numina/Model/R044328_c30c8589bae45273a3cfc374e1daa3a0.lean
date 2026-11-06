import Mathlib
set_option maxHeartbeats 800000
theorem inequalities_597547 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 ≤ 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1)) :
    a + b + c ≥ a * b + a * c + b * c := by 
  have h1 : 0 < a + b + 1 := by
    nlinarith
  have h2 : 0 < b + c + 1 := by
    nlinarith
  have h3 : 0 < c + a + 1 := by
    nlinarith
  have h6 : (b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) ≥ (a + b + 1) * (b + c + 1) * (c + a + 1) := by 
    have h7 : (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1) ≥ 0 := by linarith
    have h8 : (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1) =
      ((b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (c + a + 1)) / ((a + b + 1) * (b + c + 1) * (c + a + 1)) := by
      field_simp
      ring
    have h9 : ((b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (c + a + 1)) / ((a + b + 1) * (b + c + 1) * (c + a + 1)) ≥ 0 := by 
      linarith [h7, h8]
    have h10 : (b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (c + a + 1) ≥ 0 := by 
      have pos1 : (a + b + 1) * (b + c + 1) * (c + a + 1) > 0 := by positivity
      apply (div_nonneg_iff).mp at h9
      cases h9 with
      | inl h11 => 
        nlinarith
      | inr h12 => 
        nlinarith
    linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
  ]