import Mathlib

theorem inequalities_317101
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (habc : a * b + b * c + c * a = 1 / 3) :
    3 ≥ 1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) +
        1 / (c ^ 2 - a * b + 1) := by

  have h1 : a ^ 2 - b * c + 1 > 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), habc, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]

  have h2 : b ^ 2 - c * a + 1 > 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), habc, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]

  have h3 : c ^ 2 - a * b + 1 > 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), habc, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]

  have h5 : 3 ≥ 1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1) := by
    have hx1 : 0 < (a ^ 2 - b * c + 1) := h1
    have hx2 : 0 < (b ^ 2 - c * a + 1) := h2
    have hx3 : 0 < (c ^ 2 - a * b + 1) := h3
    have h6 : ( 1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1) ) - 3 ≤ 0 := by
      have h7 : ( 1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1) ) - 3 =
          ( ( (b ^ 2 - c * a + 1) * (c ^ 2 - a * b + 1) + (a ^ 2 - b * c + 1) * (c ^ 2 - a * b + 1) + (a ^ 2 - b * c + 1) * (b ^ 2 - c * a + 1 ) ) - 3 * ( (a ^ 2 - b * c + 1) * (b ^ 2 - c * a + 1) * (c ^ 2 - a * b + 1) ) ) / ( (a ^ 2 - b * c + 1) * (b ^ 2 - c * a + 1) * (c ^ 2 - a * b + 1) ) := by
        field_simp
        <;> ring 
      rw [h7] at *
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Numerator is less than or equal to 0.
        have h8 : ( (b ^ 2 - c * a + 1) * (c ^ 2 - a * b + 1) + (a ^ 2 - b * c + 1) * (c ^ 2 - a * b + 1) + (a ^ 2 - b * c + 1) * (b ^ 2 - c * a + 1 ) ) - 3 * ( (a ^ 2 - b * c + 1) * (b ^ 2 - c * a + 1) * (c ^ 2 - a * b + 1 ) ) ≤ 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha, 
                mul_nonneg (show 0 ≤ a * b from by nlinarith) (show 0 ≤ b * c from by nlinarith), 
                  mul_nonneg (show 0 ≤ a * b from by nlinarith) (show 0 ≤ c * a from by nlinarith), 
                    mul_nonneg (show 0 ≤ b * c from by nlinarith) (show 0 ≤ c * a from by nlinarith), 
                      sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a), 
                        mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b * c by nlinarith)
          ]
        linarith
      · -- Denominator is greater than or equal to 0.
        positivity
    linarith
  exact h5