import Mathlib

theorem inequalities_55215 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a ^ 3 / (a ^ 3 + 2) + b ^ 3 / (b ^ 3 + 2) + c ^ 3 / (c ^ 3 + 2) ≥ 1 ∧
    1 / (a ^ 3 + 2) + 1 / (b ^ 3 + 2) + 1 / (c ^ 3 + 2) ≤ 1 := by
  have h1 : a ^ 3 / (a ^ 3 + 2) + b ^ 3 / (b ^ 3 + 2) + c ^ 3 / (c ^ 3 + 2) ≥ 1 := by 
    have h4 : a ^ 3 / (a ^ 3 + 2) + b ^ 3 / (b ^ 3 + 2) + c ^ 3 / (c ^ 3 + 2) - 1 ≥ 0 := by 
      have h5 : a ^ 3 * (b ^ 3 + 2) * (c ^ 3 + 2) + b ^ 3 * (a ^ 3 + 2) * (c ^ 3 + 2) + c ^ 3 * (a ^ 3 + 2) * (b ^ 3 + 2) - (a ^ 3 + 2) * (b ^ 3 + 2) * (c ^ 3 + 2) ≥ 0 := by 
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                  sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a * b * c - 1), habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h4 : a ^ 3 / (a ^ 3 + 2) + b ^ 3 / (b ^ 3 + 2) + c ^ 3 / (c ^ 3 + 2) - 1 = 
        (a ^ 3 * (b ^ 3 + 2) * (c ^ 3 + 2) + b ^ 3 * (a ^ 3 + 2) * (c ^ 3 + 2) + c ^ 3 * (a ^ 3 + 2) * (b ^ 3 + 2) - (a ^ 3 + 2) * (b ^ 3 + 2) * (c ^ 3 + 2)) / ((a ^ 3 + 2) * (b ^ 3 + 2) * (c ^ 3 + 2)) := by 
        field_simp 
        ring 
      rw [h4] 
      apply div_nonneg 
      linarith 
      positivity 
    linarith 
  have h2 : 1 / (a ^ 3 + 2) + 1 / (b ^ 3 + 2) + 1 / (c ^ 3 + 2) ≤ 1 := by 
    have h7 : 1 / (a ^ 3 + 2) + 1 / (b ^ 3 + 2) + 1 / (c ^ 3 + 2) - 1 ≤ 0 := by 
      have h9 : (b ^ 3 + 2) * (c ^ 3 + 2) + (a ^ 3 + 2) * (c ^ 3 + 2) + (a ^ 3 + 2) * (b ^ 3 + 2) - (a ^ 3 + 2) * (b ^ 3 + 2) * (c ^ 3 + 2) ≤ 0 := by 
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                  sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a * b * c - 1), habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h8 : 1 / (a ^ 3 + 2) + 1 / (b ^ 3 + 2) + 1 / (c ^ 3 + 2) - 1 = ( (b ^ 3 + 2) * (c ^ 3 + 2) + (a ^ 3 + 2) * (c ^ 3 + 2) + (a ^ 3 + 2) * (b ^ 3 + 2) - (a ^ 3 + 2) * (b ^ 3 + 2) * (c ^ 3 + 2) ) / ((a ^ 3 + 2) * (b ^ 3 + 2) * (c ^ 3 + 2)) := by 
        field_simp 
        ring 
      rw [h8] 
      apply div_nonpos_of_nonpos_of_nonneg 
      linarith 
      positivity 
    linarith 
  constructor 
  · linarith 
  · linarith