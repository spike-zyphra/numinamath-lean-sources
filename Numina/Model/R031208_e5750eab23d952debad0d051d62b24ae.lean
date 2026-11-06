import Mathlib

theorem inequalities_43348 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 2 / b + b ^ 3 / c ^ 2 + c ^ 4 / a ^ 3 ≥ -a + 2 * b + 2 * c := by
  have hbne : b ≠ 0 := by linarith
  have hcne : c ≠ 0 := by linarith
  have hane : a ≠ 0 := by linarith

  have h1 : a ^ 2 / b + b ^ 3 / c ^ 2 + c ^ 4 / a ^ 3 - (-a + 2 * b + 2 * c) ≥ 0 := by
    have h2 : a ^ 2 / b + b ^ 3 / c ^ 2 + c ^ 4 / a ^ 3 - (-a + 2 * b + 2 * c) =
        (a^5 * c ^ 2 + b ^ 4 * a ^ 3 + c ^ 6 * b + a^4 * b * c ^ 2 - 2 * b ^ 2 * c^2 * a^3 - 2 * c^3 * b * a^3) / (b * c^2 * a^3) := by
      field_simp
      ring
    rw [h2]
    have h3 : 0 < b * c^2 * a^3 := by
      positivity
    have h4 : a ^ 5 * c ^ 2 + b ^ 4 * a ^ 3 + c ^ 6 * b + a^4 * b * c^2 - 2 * b ^ 2 * c^2 * a^3 - 2 * c^3 * b * a^3 ≥ 0 := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2), 
              sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
              sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
              sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
              sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
              mul_pos (mul_pos ha hb) ha, 
              mul_pos (mul_pos ha hb) hb, 
              mul_pos (mul_pos ha hb) hc, 
              mul_pos (mul_pos ha hc) hb, 
              mul_pos (mul_pos ha hc) hc, 
              mul_pos (mul_pos hb hc) ha, 
              mul_pos (mul_pos hb hc) hb, 
              mul_pos (mul_pos hb hc) hc, 
              sq_nonneg (a-c), sq_nonneg (a-c), sq_nonneg (a-b)
            ]
    apply div_nonneg 
    linarith [h4]
    positivity 
  linarith [h1]