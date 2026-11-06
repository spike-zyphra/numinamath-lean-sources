import Mathlib

open Real

theorem inequalities_140446 (a b c u v : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hu : u = a / b + b / c + c / a) (hv : v = a / c + b / a + c / b) :
    u + v ≥ 6 ∧ u * v ≥ 9 ∧ u ^ 2 + v ^ 2 ≥ 18 := by

  have h1 : u + v ≥ 6 := by
    rw [hu, hv]
    have h2 : a / b + b / a ≥ 2 := by
      have h3 : a / b + b / a - 2 ≥ 0 := by
        have h4 : a / b + b / a - 2 = (a ^ 2 + b ^ 2 - 2 * a * b) / (a * b) := by
          field_simp
          ring
        rw [h4]
        have h5 : a ^ 2 + b ^ 2 - 2 * a * b ≥ 0 := by
          have h7 : a ^ 2 + b ^ 2 - 2 * a * b = (a - b) ^ 2 := by
            linarith
          rw [h7]
          apply sq_nonneg
        have h8 : (a ^ 2 + b ^ 2 - 2 * a * b : ℝ) / (a * b) ≥ 0 := by
          apply div_nonneg
          linarith
          positivity
        linarith
      linarith
    have h3 : a / c + c / a ≥ 2 := by
      have h4 : a / c + c / a - 2 ≥ 0 := by
        have h5 : a / c + c / a - 2 = (a ^ 2 + c ^ 2 - 2 * a * c) / (a * c) := by
          field_simp
          ring
        rw [h5]
        have h6 : a ^ 2 + c ^ 2 - 2 * a * c ≥ 0 := by
          have h7 : a ^ 2 + c ^ 2 - 2 * a * c = (a - c) ^ 2 := by
            linarith
          rw [h7]
          apply sq_nonneg
        have h8 : (a ^ 2 + c ^ 2 - 2 * a * c : ℝ) / (a * c) ≥ 0 := by
          apply div_nonneg
          linarith
          positivity
        linarith
      linarith
    have h4 : b / c + c / b ≥ 2 := by
      have h5 : b / c + c / b - 2 ≥ 0 := by
        have h6 : b / c + c / b - 2 = (b ^ 2 + c ^ 2 - 2 * b * c) / (b * c) := by
          field_simp
          ring
        rw [h6]
        have h7 : b ^ 2 + c ^ 2 - 2 * b * c ≥ 0 := by
          have h8 : b ^ 2 + c ^ 2 - 2 * b * c = (b - c) ^ 2 := by
            linarith
          rw [h8]
          apply sq_nonneg
        have h9 : (b ^ 2 + c ^ 2 - 2 * b * c : ℝ) / (b * c) ≥ 0 := by
          apply div_nonneg
          linarith
          positivity
        linarith
      linarith
    linarith

  have h2 : u * v ≥ 9 := by
    rw [hu, hv]
    have h3 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h4 : (a / b + b / c + c / a) * (a / c + b / a + c / b) ≥ 9 := by
      have h6 : (a / b + b / c + c / a) * (a / c + b / a + c / b) - 9 ≥ 0 := by
        have h7 : (a / b + b / c + c / a) * (a / c + b / a + c / b) - 9 =
            ( (a^2 * c + b^2 * a + c^2 * b) * (a^2 * b + b^2 * c + c^2 * a) - 9 * (a * b * c)^2 ) / ( (a * b * c) ^ 2 ) := by
          field_simp
          ring
        rw [h7]
        have h8 : (a^2 * c + b^2 * a + c^2 * b) * (a^2 * b + b^2 * c + c^2 * a) - 9 * (a * b * c)^2 ≥ 0 := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
                sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        have h9 : ( (a^2 * c + b^2 * a + c^2 * b) * (a^2 * b + b^2 * c + c^2 * a) - 9 * (a * b * c)^2 ) / ( (a * b * c) ^ 2 ) ≥ 0 := by
          apply div_nonneg
          linarith
          positivity
        linarith
      linarith
    linarith

  have h3 : u ^ 2 + v ^ 2 ≥ 18 := by
    have h4 : u + v ≥ 6 := h1
    have h5 : u * v ≥ 9 := h2
    nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), sq_nonneg (u * v - 9)]

  constructor
  · exact h1
  constructor
  · exact h2
  · exact h3