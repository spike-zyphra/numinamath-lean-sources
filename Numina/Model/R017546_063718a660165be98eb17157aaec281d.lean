import Mathlib

open Real

theorem inequalities_319581 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    b^2 / a + c^2 / b + a^2 / c ≥ sqrt (3 * (a^2 + b^2 + c^2)) := by
  have h1 : b^2 / a + c^2 / b + a^2 / c ≥ 0 := by
    positivity

  have h2 : sqrt (3 * (a^2 + b^2 + c^2)) ≥ 0 := by positivity
  have h3 : b^2 / a + c^2 / b + a^2 / c ≥ sqrt (3 * (a^2 + b^2 + c^2)) := by
    have h4 : b^2 / a + c^2 / b + a^2 / c ≥ sqrt (3 * (a^2 + b^2 + c^2)) := by
      have h5 : b^2 / a + c^2 / b + a^2 / c ≥ 0 := h1
      have h6 : sqrt (3 * (a^2 + b^2 + c^2)) ≥ 0 := h2
      have h7 : (b^2 / a + c^2 / b + a^2 / c) ^ 2 ≥ 3 * (a^2 + b^2 + c^2) := by
        have h8 : b^2 / a + c^2 / b + a^2 / c ≥ 0 := by positivity
        have h9 : 0 < a * b * c := by
          positivity
        have h10 : (b^2 / a + c^2 / b + a^2 / c) ^ 2 = 
            ( (b^2 * b * c + c^2 * a * c + a^2 * a * b) / (a * b * c) ) ^ 2 := by
          field_simp
          <;> ring_nf
          <;> field_simp
          <;> ring
        have h40 : 0 < (a * b * c : ℝ) := h9
        rw [h10] at *
        have h40 : 0 < (a * b * c : ℝ) := h9
        have h41 : ((b^2 * b * c + c^2 * a * c + a^2 * a * b) / (a * b * c)) ^ 2 =
            (b^2 * b * c + c^2 * a * c + a^2 * a * b) ^ 2 / ((a * b * c) ^ 2) := by
          field_simp
          <;> ring_nf
          <;> field_simp
        rw [h41] at *
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a),
            sq_nonneg (a^2 * b - b^2 * c), sq_nonneg (b^2 * c - c^2 * a), sq_nonneg (c^2 * a - a^2 * b),
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
            sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
            sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
            mul_pos (show 0 < a * b by positivity) (show 0 < a * c by positivity), 
            mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
            mul_pos (show 0 < a * c by positivity) (show 0 < b * c by positivity)
            ]
      have h8 : sqrt (3 * (a^2 + b^2 + c^2)) ≥ 0 := by positivity
      have h9 : (b^2 / a + c^2 / b + a^2 / c) ≥ 0 := h1
      have h10 : (b^2 / a + c^2 / b + a^2 / c) ≥ sqrt (3 * (a^2 + b^2 + c^2)) := by
        have h11 : sqrt (3 * (a^2 + b^2 + c^2)) ≥ 0 := h2
        have h12 : (sqrt (3 * (a^2 + b^2 + c^2)) ) ^ 2 = 3 * (a^2 + b^2 + c^2) := by
          rw [Real.sq_sqrt]
          positivity
        nlinarith [Real.sqrt_nonneg (3 * (a ^ 2 + b ^ 2 + c ^ 2)), Real.sq_sqrt (show (0 : ℝ) ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) by positivity), sq_nonneg (b^2 / a + c^2 / b + a^2 / c - sqrt (3 * (a^2 + b^2 + c^2)) ) ]
      linarith
    linarith
  linarith
  all_goals linarith
  all_goals linarith