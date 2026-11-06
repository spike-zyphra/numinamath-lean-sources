import Mathlib

theorem inequalities_28091 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    (a ^ 2 + 6) / (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * a - 1) +
    (b ^ 2 + 6) / (2 * b ^ 2 + 2 * a ^ 2 + 2 * c ^ 2 + 2 * b - 1) +
    (c ^ 2 + 6) / (2 * c ^ 2 + 2 * a ^ 2 + 2 * b ^ 2 + 2 * c - 1) ≤ 3 := by

  have h1 : 0 < 2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * a - 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]

  have h2 : 0 < 2 * b ^ 2 + 2 * a ^ 2 + 2 * c ^ 2 + 2 * b - 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]

  have h3 : 0 < 2 * c ^ 2 + 2 * a ^ 2 + 2 * b ^ 2 + 2 * c - 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]

  have h4 : (a ^ 2 + 6) / (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * a - 1) ≤ 1 := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]

  have h5 : (b ^ 2 + 6) / (2 * b ^ 2 + 2 * a ^ 2 + 2 * c ^ 2 + 2 * b - 1) ≤ 1 := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]

  have h6 : (c ^ 2 + 6) / (2 * c ^ 2 + 2 * a ^ 2 + 2 * b ^ 2 + 2 * c - 1) ≤ 1 := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]

  linarith