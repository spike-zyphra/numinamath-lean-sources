import Mathlib

theorem inequalities_57180 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * Real.sqrt (b * c + c * a + a * b) ≤
    Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3) := by
  have h1 : 0 < b * c + c * a + a * b := by
    positivity
  have h2 : 0 < (b + c) * (c + a) * (a + b) := by
    positivity

  have h14 : (b * c + c * a + a * b) ^ 3 ≤ (27 / 64) * ( (b + c) * (c + a) * (a + b) ) ^ 2 := by
    have h31 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b) + b * (b - c) + c * (c - a)), 
        sq_nonneg (a * (a - c) + c * (c - b) + b * (b - a)), 
        sq_nonneg ((a + b - c) * (a - b + c) * (a + b + c)), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
        mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
        mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith), 
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos (show 0 < a by linarith) (show 0 < b * c by nlinarith)
      ]
  have h3 : (2 * Real.sqrt (b * c + c * a + a * b) ) ^ 6 ≤ (Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3) ) ^ 6 := by
    have h7 : (2 * Real.sqrt (b * c + c * a + a * b) ) ^ 6 = 64 * ( (b * c + c * a + a * b) ) ^ 3 := by
      calc
        (2 * Real.sqrt (b * c + c * a + a * b) ) ^ 6
          = 64 * ( Real.sqrt (b * c + c * a + a * b) ) ^ 6 := by
            ring_nf
        _ = 64 * ( ( Real.sqrt (b * c + c * a + a * b) ) ^ 2 ) ^ 3 := by
          ring_nf
        _ = 64 * ( ( b * c + c * a + a * b ) ) ^ 3 := by
          rw [Real.sq_sqrt (by positivity)]
    have h8 : ( Real.sqrt 3 * ((b + c) * (c + a) * (a + b) ) ^ ((1 : ℝ) / 3) ) ^ 6
      = 27 * ( (b + c) * (c + a) * (a + b) ) ^ 2 := by
      calc
        ( Real.sqrt 3 * ((b + c) * (c + a) * (a + b) ) ^ ((1 : ℝ) / 3) ) ^ 6
          = ( Real.sqrt 3 ) ^ 6 * ( ( (b + c) * (c + a) * (a + b) ) ^ ((1 : ℝ) / 3) ) ^ 6 := by 
            ring_nf
        _ = ( 3 ) ^ 3 * ( ( (b + c) * (c + a) * (a + b) ) ^ ((1 : ℝ) / 3) ) ^ 6 := by 
          have h9 : ( Real.sqrt 3 ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
          have h10 : ( Real.sqrt 3 ) ^ 6 = ( ( Real.sqrt 3 ) ^ 2 ) ^ 3 := by ring_nf
          rw [h10, h9]
        _ = (3) ^ 3 * ( ( (b + c) * (c + a) * (a + b) ) ^ 2 ) := by
          have h14 : ( ( (b + c) * (c + a) * (a + b) ) ^ ((1 : ℝ) / 3) ) ^ 6 = ( (b + c) * (c + a) * (a + b) ) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals positivity
          rw [h14]
        _ = 27 * ( (b + c) * (c + a) * (a + b) ) ^ 2 := by 
          ring_nf
    have h15 : 64 * ( (b * c + c * a + a * b) ) ^ 3 ≤ 27 * ( (b + c) * (c + a) * (a + b) ) ^ 2 := by
      nlinarith [h14, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    linarith [h7, h8, h15]
  have h4 : 0 ≤ Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3) := by positivity
  have h5 : 0 ≤ 2 * Real.sqrt (b * c + c * a + a * b) := by positivity
  have h7 : (2 * Real.sqrt (b * c + c * a + a * b) ) ^ 6 ≤ (Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3) ) ^ 6 := h3
  have h8 : 2 * Real.sqrt (b * c + c * a + a * b) ≤ Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3) := by
    by_contra h
    push_neg at h
    have h9 : (2 * Real.sqrt (b * c + c * a + a * b) ) ^ 6 > (Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3) ) ^ 6 := by
      have h10 : 2 * Real.sqrt (b * c + c * a + a * b) > Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3) := h
      have h10' : (2 * Real.sqrt (b * c + c * a + a * b) ) ^ 6 > (Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3)  ) ^ 6 := by
        apply pow_lt_pow_left
        all_goals nlinarith [h10, h4, h5]
      linarith
    linarith
  exact h8