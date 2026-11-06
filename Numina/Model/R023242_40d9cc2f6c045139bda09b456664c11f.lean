import Mathlib

theorem algebra_313616 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    (7 * a + 1) ^ ((1 : ℝ) / 3) + (7 * b + 1) ^ ((1 : ℝ) / 3) +
    (7 * c + 1) ^ ((1 : ℝ) / 3) + (7 * d + 1) ^ ((1 : ℝ) / 3) > 5 := by
  have h1 : (7 * a + 1 : ℝ) ^ ((1 : ℝ) / 3) > 1 + a := by 
    have h2 : (1 + a) ^ 3 < (7 * a + 1 : ℝ) := by
      nlinarith [sq_pos_of_pos ha, sq_nonneg (a ^ 2), sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (a * d), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
        ]
    have h3 : (1 + a : ℝ) < (7 * a + 1 : ℝ) ^ ((1 : ℝ) / 3) := by
      have h4 : ((1 + a : ℝ) ) ^ 3 < (7 * a + 1 : ℝ) := by linarith [h2]
      have h6 : (1 + a : ℝ) = ((1 + a : ℝ) ^ 3) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          nlinarith
      have h7 : ((1 + a : ℝ) ^ 3) ^ ((1 : ℝ) / 3) < (7 * a + 1 : ℝ) ^ ((1 : ℝ) / 3) := by
        apply Real.rpow_lt_rpow
        · -- Show 0 ≤ (1 + a : ℝ) ^ 3
          positivity
        · -- Show (1 + a : ℝ) ^ 3 < (7 * a + 1 : ℝ)
          linarith [h4]
        · -- Show (1 : ℝ) / 3 > 0
          norm_num
      nlinarith [h6, h7]
    linarith
  have h1b : (7 * b + 1 : ℝ) ^ ((1 : ℝ) / 3) > 1 + b := by 
    have h2 : (1 + b) ^ 3 < (7 * b + 1 : ℝ) := by
      nlinarith [sq_pos_of_pos hb, sq_nonneg (b ^ 2), sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (b * d), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
        ]
    have h3 : (1 + b : ℝ) < (7 * b + 1 : ℝ) ^ ((1 : ℝ) / 3) := by
      have h4 : ((1 + b : ℝ) ) ^ 3 < (7 * b + 1 : ℝ) := by linarith [h2]
      have h6 : (1 + b : ℝ) = ((1 + b : ℝ) ^ 3) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          nlinarith
      have h7 : ((1 + b : ℝ) ^ 3) ^ ((1 : ℝ) / 3) < (7 * b + 1 : ℝ) ^ ((1 : ℝ) / 3) := by
        apply Real.rpow_lt_rpow
        · -- Show 0 ≤ (1 + b : ℝ) ^ 3
          positivity
        · -- Show (1 + b : ℝ) ^ 3 < (7 * b + 1 : ℝ)
          linarith [h4]
        · -- Show (1 : ℝ) / 3 > 0
          norm_num
      nlinarith [h6, h7]
    linarith
  have h1c : (7 * c + 1 : ℝ) ^ ((1 : ℝ) / 3) > 1 + c := by 
    have h2 : (1 + c) ^ 3 < (7 * c + 1 : ℝ) := by
      nlinarith [sq_pos_of_pos hc, sq_nonneg (c ^ 2), sq_nonneg (a * c), sq_nonneg (b * c), sq_nonneg (c * d), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
        ]
    have h3 : (1 + c : ℝ) < (7 * c + 1 : ℝ) ^ ((1 : ℝ) / 3) := by
      have h4 : ((1 + c : ℝ) ) ^ 3 < (7 * c + 1 : ℝ) := by linarith [h2]
      have h6 : (1 + c : ℝ) = ((1 + c : ℝ) ^ 3) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          nlinarith
      have h7 : ((1 + c : ℝ) ^ 3) ^ ((1 : ℝ) / 3) < (7 * c + 1 : ℝ) ^ ((1 : ℝ) / 3) := by
        apply Real.rpow_lt_rpow
        · -- Show 0 ≤ (1 + c : ℝ) ^ 3
          positivity
        · -- Show (1 + c : ℝ) ^ 3 < (7 * c + 1 : ℝ)
          linarith [h4]
        · -- Show (1 : ℝ) / 3 > 0
          norm_num
      nlinarith [h6, h7]
    linarith
  have h1d : (7 * d + 1 : ℝ) ^ ((1 : ℝ) / 3) > 1 + d := by 
    have h2 : (1 + d) ^ 3 < (7 * d + 1 : ℝ) := by
      nlinarith [sq_pos_of_pos hd, sq_nonneg (d ^ 2), sq_nonneg (a * d), sq_nonneg (b * d), sq_nonneg (c * d), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
        ]
    have h3 : (1 + d : ℝ) < (7 * d + 1 : ℝ) ^ ((1 : ℝ) / 3) := by
      have h4 : ((1 + d : ℝ) ) ^ 3 < (7 * d + 1 : ℝ) := by linarith [h2]
      have h6 : (1 + d : ℝ) = ((1 + d : ℝ) ^ 3) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          nlinarith
      have h7 : ((1 + d : ℝ) ^ 3) ^ ((1 : ℝ) / 3) < (7 * d + 1 : ℝ) ^ ((1 : ℝ) / 3) := by
        apply Real.rpow_lt_rpow
        · -- Show 0 ≤ (1 + d : ℝ) ^ 3
          positivity
        · -- Show (1 + d : ℝ) ^ 3 < (7 * d + 1 : ℝ)
          linarith [h4]
        · -- Show (1 : ℝ) / 3 > 0
          norm_num
      nlinarith [h6, h7]
    linarith
  have h10 : (7 * a + 1 : ℝ) ^ ((1 : ℝ) / 3) + (7 * b + 1 : ℝ) ^ ((1 : ℝ) / 3) + (7 * c + 1 : ℝ) ^ ((1 : ℝ) / 3) + (7 * d + 1 : ℝ) ^ ((1 : ℝ) / 3) > 5 := by
    have h11 : (7 * a + 1 : ℝ) ^ ((1 : ℝ) / 3) + (7 * b + 1 : ℝ) ^ ((1 : ℝ) / 3) + (7 * c + 1 : ℝ) ^ ((1 : ℝ) / 3) + (7 * d + 1 : ℝ) ^ ((1 : ℝ) / 3) > (1 + a : ℝ) + (1 + b : ℝ) + (1 + c : ℝ) + (1 + d : ℝ) := by
      linarith [h1, h1b, h1c, h1d]
    have h18 : (1 + a : ℝ) + (1 + b : ℝ) + (1 + c : ℝ) + (1 + d : ℝ) = 4 + (a + b + c + d : ℝ) := by
      linarith
    have h19 : 4 + (a + b + c + d : ℝ) = 5 := by
      linarith [h]
    linarith [h11, h18, h19]
  linarith