import Mathlib

theorem inequalities_301712 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + 2 * b) * (b + 2 * c) = 9) :
    Real.sqrt ((a ^ 2 + b ^ 2) / 2) +
    2 * ((b ^ 3 + c ^ 3) / 2) ^ ((1 : ℝ) / 3) ≥ 3 := by

  have h1 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ (a + b) / 2 := by
    have h2 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
      nlinarith [sq_nonneg (a - b)]
    have h3 : (a + b) / 2 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
      have h4 : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
        linarith [h2]
      have h5 : (a + b) / 2 ≥ 0 := by
        nlinarith
      have h6 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ Real.sqrt (((a + b) / 2) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [h2]
      have h7 : Real.sqrt (((a + b) / 2) ^ 2) = (a + b) / 2 := by
        rw [Real.sqrt_sq (by
          nlinarith
        )
        ]
      linarith [h6, h7]
    linarith

  have h2 : ((b ^ 3 + c ^ 3) / 2) ^ ((1 : ℝ) / 3) ≥ (b + c) / 2 := by
    have h4 : ( (b ^ 3 + c ^ 3) / 2 ) ≥ ( (b + c) / 2 ) ^ 3 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg ((b + c) / 2 - b), sq_nonneg ((b + c) / 2 - c), sq_nonneg (b - c), mul_pos hb hc]
    have h5 : ((b ^ 3 + c ^ 3) / 2) ^ ((1 : ℝ) / 3) ≥ ( ( (b + c) / 2 ) ^ 3 ) ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_le_rpow
      all_goals nlinarith [sq_nonneg (b - c), sq_nonneg ((b + c) / 2 - b), sq_nonneg ((b + c) / 2 - c), sq_nonneg (b - c), mul_pos hb hc]
    have h6 : ( ( (b + c) / 2 ) ^ 3 ) ^ ((1 : ℝ) / 3) = (b + c) / 2 := by
      rw [show ( ( (b + c) / 2 ) ^ 3 ) ^ ((1 : ℝ) / 3) = (b + c) / 2 by
        have h8 : ( ( (b + c) / 2 ) ^ 3 ) ^ ((1 : ℝ) / 3) = (b + c) / 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals nlinarith 
        linarith [h8]
      ]
    linarith [h4, h5, h6]

  have h3 : a + 3 * b + 2 * c ≥ 6 := by
    nlinarith [sq_nonneg (a + 2 * b - 3), sq_nonneg (b + 2 * c - 3), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]

  have h5 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) + 2 * ((b ^ 3 + c ^ 3) / 2) ^ ((1 : ℝ) / 3) ≥ (a + 3 * b + 2 * c) / 2 := by
    linarith [h1, h2]

  linarith [h3, h5]