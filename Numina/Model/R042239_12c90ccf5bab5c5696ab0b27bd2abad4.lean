import Mathlib
theorem algebra_605824 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 3 ≤ (2 * a ^ 2 + 1 / a) / (b + 1 / a + 1) + (2 * b ^ 2 + 1 / b) / (c + 1 / b + 1) + (2 * c ^ 2 + 1 / c) / (a + 1 / c + 1) := by
  -- First, we need to rewrite the reciprocals using `abc = 1`
  have h3 : 1 / a = b * c := by
    field_simp
    nlinarith [habc]
  have h4 : 1 / b = a * c := by
    field_simp
    nlinarith [habc]
  have h5 : 1 / c = a * b := by
    field_simp
    nlinarith [habc]
  rw [h3, h4, h5]
  have h9 : (2 * a ^ 2 + b * c) / (b + b * c + 1) + (2 * b ^ 2 + a * c) / (c + a * c + 1) + (2 * c ^ 2 + a * b) / (a + a * b + 1) ≥ 3 := by
    have h9' : (2 * a ^ 2 + b * c) / (b + b * c + 1) + (2 * b ^ 2 + a * c) / (c + a * c + 1) + (2 * c ^ 2 + a * b) / (a + a * b + 1) - 3 ≥ 0 := by
      have h21 : ( (2 * a ^ 2 + b * c) / (b + b * c + 1) + (2 * b ^ 2 + a * c) / (c + a * c + 1) + (2 * c ^ 2 + a * b) / (a + a * b + 1) - 3 ) = 
          ( (2 * a ^ 2 + b * c) * ( (c + a * c + 1) * (a + a * b + 1) ) + (2 * b ^ 2 + a * c) * ( (b + b * c + 1) * (a + a * b + 1) ) + (2 * c ^ 2 + a * b) * ( (b + b * c + 1) * (c + a * c + 1) ) - 3 * ( (b + b * c + 1) * (c + a * c + 1) * (a + a * b + 1) ) ) / ( (b + b * c + 1) * (c + a * c + 1) * (a + a * b + 1) ) := by
        field_simp
        ring
      rw [h21] at *
      have h30 : (b + b * c + 1) > 0 := by positivity
      have h31 : (c + a * c + 1) > 0 := by positivity
      have h32 : (a + a * b + 1) > 0 := by positivity
      have h33 : (b + b * c + 1) * (c + a * c + 1) * (a + a * b + 1) > 0 := by positivity
      have h34 : ( (2 * a ^ 2 + b * c) * ( (c + a * c + 1) * (a + a * b + 1) ) + (2 * b ^ 2 + a * c) * ( (b + b * c + 1) * (a + a * b + 1) ) + (2 * c ^ 2 + a * b) * ( (b + b * c + 1) * (c + a * c + 1) ) - 3 * ( (b + b * c + 1) * (c + a * c + 1) * (a + a * b + 1) ) ) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
            mul_pos (mul_pos ha hb) hc
          ]
      have h39 : ( (2 * a ^ 2 + b * c) * ( (c + a * c + 1) * (a + a * b + 1) ) + (2 * b ^ 2 + a * c) * ( (b + b * c + 1) * (a + a * b + 1) ) + (2 * c ^ 2 + a * b) * ( (b + b * c + 1) * (c + a * c + 1) ) - 3 * ( (b + b * c + 1) * (c + a * c + 1) * (a + a * b + 1) ) ) / ( (b + b * c + 1) * (c + a * c + 1) * (a + a * b + 1) ) ≥ 0 := by
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith
  linarith