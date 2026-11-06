import Mathlib


theorem inequalities_87628 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 1 / c ≥ 3 / (a * b * c)) :
    2 ≤ (a ^ 2 + b ^ 2) / (a ^ 2 + b ^ 2 + 1) +
        (b ^ 2 + c ^ 2) / (b ^ 2 + c ^ 2 + 1) +
        (c ^ 2 + a ^ 2) / (c ^ 2 + a ^ 2 + 1) := by 
  have h1 : a * b + b * c + c * a ≥ 3 := by
    have pos1 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h2 : (1 / a + 1 / b + 1 / c) - 3 / (a * b * c) ≥ 0 := by linarith
    have h3 : (1 / a + 1 / b + 1 / c) - 3 / (a * b * c) = (a * b + b * c + c * a - 3) / (a * b * c) := by 
      field_simp
      ring
    rw [h3] at h2
    have h4 : a * b + b * c + c * a - 3 ≥ 0 := by
      by_contra h5
      push_neg at h5
      have h6 : (a * b + b * c + c * a - 3) / (a * b * c) < 0 := by
        apply div_neg_of_neg_of_pos
        all_goals linarith
      linarith
    linarith

  have h2 : (a ^ 2 + b ^ 2) / (a ^ 2 + b ^ 2 + 1) + (b ^ 2 + c ^ 2) / (b ^ 2 + c ^ 2 + 1) + (c ^ 2 + a ^ 2) / (c ^ 2 + a ^ 2 + 1) - 2 ≥ 0 := by
    have h3 : (a ^ 2 + b ^ 2) / (a ^ 2 + b ^ 2 + 1) + (b ^ 2 + c ^ 2) / (b ^ 2 + c ^ 2 + 1) + (c ^ 2 + a ^ 2) / (c ^ 2 + a ^ 2 + 1) - 2 =
        (1 - (1 / (a ^ 2 + b ^ 2 + 1) + 1 / (b ^ 2 + c ^ 2 + 1) + 1 / (c ^ 2 + a ^ 2 + 1))) := by
      field_simp
      nlinarith
    rw [h3]
    have h4 : 1 / (a ^ 2 + b ^ 2 + 1) + 1 / (b ^ 2 + c ^ 2 + 1) + 1 / (c ^ 2 + a ^ 2 + 1) ≤ 1 := by
      have h4a : 0 < a ^ 2 + b ^ 2 + 1 := by nlinarith
      have h4b : 0 < b ^ 2 + c ^ 2 + 1 := by nlinarith
      have h4c : 0 < c ^ 2 + a ^ 2 + 1 := by nlinarith
      have h5 : 1 / (a ^ 2 + b ^ 2 + 1) + 1 / (b ^ 2 + c ^ 2 + 1) + 1 / (c ^ 2 + a ^ 2 + 1) - 1 ≤ 0 := by
        have pos1 : 0 < (a ^ 2 + b ^ 2 + 1) * (b ^ 2 + c ^ 2 + 1) * (c ^ 2 + a ^ 2 + 1) := by positivity
        have h6 : (1 / (a ^ 2 + b ^ 2 + 1) + 1 / (b ^ 2 + c ^ 2 + 1) + 1 / (c ^ 2 + a ^ 2 + 1) - 1) =
            ((b ^ 2 + c ^ 2 + 1) * (c ^ 2 + a ^ 2 + 1) + (a ^ 2 + b ^ 2 + 1) * (c ^ 2 + a ^ 2 + 1) + (a ^ 2 + b ^ 2 + 1) * (b ^ 2 + c ^ 2 + 1) - (a ^ 2 + b ^ 2 + 1) * (b ^ 2 + c ^ 2 + 1) * (c ^ 2 + a ^ 2 + 1)) / ((a ^ 2 + b ^ 2 + 1) * (b ^ 2 + c ^ 2 + 1) * (c ^ 2 + a ^ 2 + 1)) := by
          field_simp
          ring
        rw [h6]
        have h7 : (b ^ 2 + c ^ 2 + 1) * (c ^ 2 + a ^ 2 + 1) + (a ^ 2 + b ^ 2 + 1) * (c ^ 2 + a ^ 2 + 1) + (a ^ 2 + b ^ 2 + 1) * (b ^ 2 + c ^ 2 + 1) - (a ^ 2 + b ^ 2 + 1) * (b ^ 2 + c ^ 2 + 1) * (c ^ 2 + a ^ 2 + 1) ≤ 0 := by
          nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * b + b * c + c * a - 3), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
        apply div_nonpos_of_nonpos_of_nonneg h7 (show 0 ≤ (a ^ 2 + b ^ 2 + 1) * (b ^ 2 + c ^ 2 + 1) * (c ^ 2 + a ^ 2 + 1) by positivity)
      linarith
    linarith
  linarith