import Mathlib


theorem inequalities_55386 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    |(4 * (b ^ 3 - c ^ 3)) / (b + c) + (4 * (c ^ 3 - a ^ 3)) / (c + a) +
      (4 * (a ^ 3 - b ^ 3)) / (a + b)| ≤ (b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2 := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h2 : (b + c) ≠ 0 := by linarith
  have h3 : (c + a) ≠ 0 := by linarith
  have h4 : (a + b) ≠ 0 := by linarith

  have h5 : - ((b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2) ≤ (4 * (b ^ 3 - c ^ 3)) / (b + c) + (4 * (c ^ 3 - a ^ 3)) / (c + a) + (4 * (a ^ 3 - b ^ 3)) / (a + b) := by
    have h6 : (4 * (b ^ 3 - c ^ 3)) / (b + c) + (4 * (c ^ 3 - a ^ 3)) / (c + a) + (4 * (a ^ 3 - b ^ 3)) / (a + b) + ((b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2) ≥ 0 := by
      have h7 : (4 * (b ^ 3 - c ^ 3)) / (b + c) + (4 * (c ^ 3 - a ^ 3)) / (c + a) + (4 * (a ^ 3 - b ^ 3)) / (a + b) + ((b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2) =
          ((4 * (b ^ 3 - c ^ 3)) * (c + a) * (a + b) + (4 * (c ^ 3 - a ^ 3)) * (b + c) * (a + b) + (4 * (a ^ 3 - b ^ 3)) * (b + c) * (c + a) + ((b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2) * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
        field_simp [h2, h3, h4]
        all_goals ring
      rw [h7]
      apply div_nonneg
      have h11 : (4 * (b ^ 3 - c ^ 3)) * (c + a) * (a + b) + (4 * (c ^ 3 - a ^ 3)) * (b + c) * (a + b) + (4 * (a ^ 3 - b ^ 3)) * (b + c) * (c + a) + ((b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2) * (b + c) * (c + a) * (a + b) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (mul_pos ha hb) hc ]
      linarith
      all_goals
        positivity
    linarith

  have h6 : (4 * (b ^ 3 - c ^ 3)) / (b + c) + (4 * (c ^ 3 - a ^ 3)) / (c + a) + (4 * (a ^ 3 - b ^ 3)) / (a + b) ≤ (b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2 := by
    have h7 : (b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2 - ((4 * (b ^ 3 - c ^ 3)) / (b + c) + (4 * (c ^ 3 - a ^ 3)) / (c + a) + (4 * (a ^ 3 - b ^ 3)) / (a + b)) ≥ 0 := by
      have h8 : (b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2 - ((4 * (b ^ 3 - c ^ 3)) / (b + c) + (4 * (c ^ 3 - a ^ 3)) / (c + a) + (4 * (a ^ 3 - b ^ 3)) / (a + b)) =
          (( (b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2) * (b + c) * (c + a) * (a + b) - ((4 * (b ^ 3 - c ^ 3)) * (c + a) * (a + b) + (4 * (c ^ 3 - a ^ 3)) * (b + c) * (a + b) + (4 * (a ^ 3 - b ^ 3)) * (b + c) * (c + a)) ) / ((b + c) * (c + a) * (a + b)) := by
        field_simp [h2, h3, h4]
        all_goals ring
      rw [h8]
      apply div_nonneg
      have h11 : ( (b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2) * (b + c) * (c + a) * (a + b) - ((4 * (b ^ 3 - c ^ 3)) * (c + a) * (a + b) + (4 * (c ^ 3 - a ^ 3)) * (b + c) * (a + b) + (4 * (a ^ 3 - b ^ 3)) * (b + c) * (c + a)) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (mul_pos ha hb) hc ]
      linarith
      all_goals
        positivity
    linarith

  apply abs_le.mpr
  constructor <;> linarith