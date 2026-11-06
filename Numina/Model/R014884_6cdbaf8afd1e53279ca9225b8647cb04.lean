import Mathlib

theorem inequalities_597592 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + 2 * b) * (b + 2 * c) = 9) :
    Real.sqrt ((a ^ 2 + b ^ 2) / 2) + 2 * ((b ^ 3 + c ^ 3) / 2) ^ ((1 : ℝ) / 3) ≥ 3 := by
  have h2 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ (a + b) / 2 := by
    have h3 : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
      linarith [sq_nonneg (a - b)]
    have h4 : (a + b) / 2 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith
  have h3 : ((b ^ 3 + c ^ 3) / 2 : ℝ) ^ ((1 : ℝ) / 3) ≥ (b + c) / 2 := by
    have h4 : (b ^ 3 + c ^ 3) / 2 ≥ ((b + c) / 2) ^ 3 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), mul_pos hb hc, sq_nonneg (b^2 - c^2)]
    have h5 : ((b ^ 3 + c ^ 3) / 2 : ℝ) ≥ 0 := by
      have hb' : 0 < b := hb
      have hc' : 0 < c := hc
      nlinarith [sq_nonneg (b^2), sq_nonneg (c^2), mul_pos hb hc]
    have h6 : (( (b + c) / 2 ) ^ 3 : ℝ) ≥ 0 := by
      have h4' : (b + c) / 2 ≥ 0 := by linarith
      positivity
    have h7 : ((b ^ 3 + c ^ 3) / 2 : ℝ) ^ ((1 : ℝ) / 3) ≥ (( (b + c) / 2 ) ^ 3) ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_le_rpow
      all_goals
        all_goals
          try linarith [hb, hc, h4, h5, h6]
          try positivity
    have h8 : (( (b + c) / 2 ) ^ 3) ^ ((1 : ℝ) / 3) = (b + c) / 2 := by
      have h8' : (( (b + c) / 2 ) ^ 3) ^ ((1 : ℝ) / 3) = (b + c) / 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          all_goals
            try linarith [hb, hc]
            try nlinarith
      linarith [h8']
    linarith [h7, h8]
  have h8 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) + 2 * ((b ^ 3 + c ^ 3) / 2) ^ ((1 : ℝ) / 3) ≥ (a + b) / 2 + (b + c) := by
    linarith [h2, h3]
  have h7 : a + 3 * b + 2 * c ≥ 6 := by
    nlinarith [sq_nonneg (a + 2 * b - 3), sq_nonneg (b + 2 * c - 3), mul_pos ha hb, 
          mul_pos hb hc, h, mul_pos ha hc
        ]
  linarith [h8, h7]