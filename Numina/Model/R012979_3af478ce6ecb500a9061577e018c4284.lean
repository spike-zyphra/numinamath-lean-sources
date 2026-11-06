import Mathlib


open Real


theorem inequalities_66429 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c * d = 1) :
    (1 + a) * (1 + b) * (1 + c) * (1 + d) ≥ 16 := by
  have h1 : 1 + a ≥ 2 * Real.sqrt a := by
    have h2 : 1 + a - 2 * Real.sqrt a ≥ 0 := by
      have h3 : 1 + a - 2 * Real.sqrt a = (1 - Real.sqrt a) ^ 2 := by
        nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ a by positivity)]
      rw [h3]
      apply sq_nonneg
      all_goals linarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ a by positivity)]
    nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ a by positivity)]
  have h2 : 1 + b ≥ 2 * Real.sqrt b := by
    have h2 : 1 + b - 2 * Real.sqrt b ≥ 0 := by
      have h3 : 1 + b - 2 * Real.sqrt b = (1 - Real.sqrt b) ^ 2 := by
        nlinarith [Real.sqrt_nonneg b, Real.sq_sqrt (show 0 ≤ b by positivity)]
      rw [h3]
      apply sq_nonneg
      all_goals linarith [Real.sqrt_nonneg b, Real.sq_sqrt (show 0 ≤ b by positivity)]
    nlinarith [Real.sqrt_nonneg b, Real.sq_sqrt (show 0 ≤ b by positivity)]
  have h3 : 1 + c ≥ 2 * Real.sqrt c := by
    have h2 : 1 + c - 2 * Real.sqrt c ≥ 0 := by
      have h3 : 1 + c - 2 * Real.sqrt c = (1 - Real.sqrt c) ^ 2 := by
        nlinarith [Real.sqrt_nonneg c, Real.sq_sqrt (show 0 ≤ c by positivity)]
      rw [h3]
      apply sq_nonneg
      all_goals linarith [Real.sqrt_nonneg c, Real.sq_sqrt (show 0 ≤ c by positivity)]
    nlinarith [Real.sqrt_nonneg c, Real.sq_sqrt (show 0 ≤ c by positivity)]
  have h4 : 1 + d ≥ 2 * Real.sqrt d := by
    have h2 : 1 + d - 2 * Real.sqrt d ≥ 0 := by
      have h3 : 1 + d - 2 * Real.sqrt d = (1 - Real.sqrt d) ^ 2 := by
        nlinarith [Real.sqrt_nonneg d, Real.sq_sqrt (show 0 ≤ d by positivity)]
      rw [h3]
      apply sq_nonneg
      all_goals linarith [Real.sqrt_nonneg d, Real.sq_sqrt (show 0 ≤ d by positivity)]
    nlinarith [Real.sqrt_nonneg d, Real.sq_sqrt (show 0 ≤ d by positivity)]
  have h5 : (1 + a) * (1 + b) * (1 + c) * (1 + d) ≥ (2 * Real.sqrt a) * (2 * Real.sqrt b) * (2 * Real.sqrt c) * (2 * Real.sqrt d) := by
    apply mul_le_mul
    apply mul_le_mul
    apply mul_le_mul
    all_goals
      try { nlinarith [h1, h2, h3, h4] }
      try { positivity }
      try { nlinarith }
    all_goals positivity
  have h6 : (2 * Real.sqrt a) * (2 * Real.sqrt b) * (2 * Real.sqrt c) * (2 * Real.sqrt d) = 16 * Real.sqrt (a * b * c * d) := by
    calc 
      (2 * Real.sqrt a) * (2 * Real.sqrt b) * (2 * Real.sqrt c) * (2 * Real.sqrt d)
          = (2 ^ 4) * (Real.sqrt a * Real.sqrt b * Real.sqrt c * Real.sqrt d) := by ring_nf 
      _ = (16:ℝ) * ( ( Real.sqrt a * Real.sqrt b ) * ( Real.sqrt c * Real.sqrt d ) ) := by ring_nf 
      _ = 16 * ( Real.sqrt (a * b) * Real.sqrt (c * d ) ) := by 
        have h7 : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := by 
          rw [← Real.sqrt_mul (by positivity)]
        have h8 : Real.sqrt c * Real.sqrt d = Real.sqrt (c * d) := by 
          rw [← Real.sqrt_mul (by positivity)]
        rw [h7, h8]
        all_goals ring_nf
        all_goals nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), Real.sq_sqrt (show 0 ≤ a * b by positivity), Real.sq_sqrt (show 0 ≤ c * d by positivity)]
      _ = 16 * Real.sqrt ((a * b) * (c * d ) ) := by
        have h9 : Real.sqrt (a * b) * Real.sqrt (c * d) = Real.sqrt ((a * b) * (c * d)) := by 
          rw [← Real.sqrt_mul (by positivity)]
        rw [h9]
        all_goals ring_nf
        all_goals nlinarith [Real.sqrt_nonneg ((a * b) * (c * d ) ), Real.sqrt_nonneg (a * b * c * d ), Real.sq_sqrt (show 0 ≤ (a * b) * (c * d) by positivity), Real.sq_sqrt (show 0 ≤ a * b * c * d by positivity) ]
      _ = 16 * Real.sqrt (a * b * c * d) := by
        ring_nf
        all_goals nlinarith [Real.sq_sqrt (show 0 ≤ a * b * c * d by positivity) ]
  have h7 : Real.sqrt (a * b * c * d) = 1 := by
    have h8 : a * b * c * d = (1 : ℝ) := by
      nlinarith [h]
    rw [h8]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> nlinarith
  have h8 : (2 * Real.sqrt a) * (2 * Real.sqrt b) * (2 * Real.sqrt c) * (2 * Real.sqrt d) = (16:ℝ) := by
    rw [h6, h7]
    all_goals norm_num
  linarith