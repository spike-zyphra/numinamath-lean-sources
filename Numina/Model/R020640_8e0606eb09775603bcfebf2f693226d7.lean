import Mathlib

theorem inequalities_327582 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 2 * a ^ 2 + b ^ 2 = 9 * c ^ 2) :
    2 * c / a + c / b ≥ Real.sqrt 3 := by

  have h1 : 2 * c / a + c / b ≥ Real.sqrt 3 := by
    have h2 : (2 * c / a + c / b) ^ 2 ≥ 3 := by
      have h3 : 0 < a * b := mul_pos ha hb
      have h4 : (2 * c / a + c / b) ^ 2 = 4 * c ^ 2 / a ^ 2 + c ^ 2 / b ^ 2 + 4 * c ^ 2 / (a * b) := by
        field_simp
        <;> ring
      rw [h4] at *
      have h5 : 4 * c ^ 2 * b ^ 2 + c ^ 2 * a ^ 2 + 4 * c ^ 2 * (a * b) ≥ 3 * (a * b) ^ 2 := by
        nlinarith [sq_nonneg (2 * c * b - a * c), sq_nonneg (2 * c - a), sq_nonneg (2 * c - b), sq_nonneg (a - b), sq_nonneg (a * (2 * c) - b * c), sq_nonneg (a * b - c * (2 * a + b)), sq_nonneg (2 * a^2 + b^2 - 9 * c^2), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
      have h6 : 4 * c ^ 2 / a ^ 2 + c ^ 2 / b ^ 2 + 4 * c ^ 2 / (a * b) ≥ 3 := by
        have h7 : 0 < a ^ 2 := by positivity
        have h8 : 0 < b ^ 2 := by positivity
        have h9 : 0 < a * b := by positivity
        have h10 : (4 * c ^ 2 / a ^ 2 + c ^ 2 / b ^ 2 + 4 * c ^ 2 / (a * b)) = (4 * c ^ 2 * b ^ 2 + c ^ 2 * a ^ 2 + 4 * c ^ 2 * (a * b)) / (a ^ 2 * b ^ 2) := by
          field_simp
          ring
        rw [h10] at *
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [ h5, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc ]
      linarith
    have h7 : Real.sqrt ((2 * c / a + c / b) ^ 2) ≥ Real.sqrt (3 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith [h2]
    have h8 : Real.sqrt ((2 * c / a + c / b) ^ 2) = (2 * c / a + c / b) := by
      rw [Real.sqrt_sq]
      positivity
    nlinarith [ h8, h7 ]
  linarith [ h1 ]