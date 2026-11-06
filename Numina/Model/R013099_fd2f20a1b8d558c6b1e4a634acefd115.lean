import Mathlib

theorem inequalities_197325 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a + b + c + d) / 4 ≥ (a * b * c * d) ^ ((1 : ℝ) / 4) := by 
  have h1 : (a * b * c * d) ^ ((1 : ℝ) / 4) ≤ (a + b + c + d) / 4 := by 
    have h21 : (a * b * c * d) ^ ((1 : ℝ) / 4) = ((a * b * c * d) ) ^ (1 / 4 : ℝ) := by
      norm_num 
      all_goals linarith 
    rw [h21] 
    have h41 : ((a * b * c * d: ℝ) ) ^ (1 / 4 : ℝ) ≤ (a + b + c + d) / 4 := by
      have h31 : (a * b * c * d : ℝ) ≤ ((a + b + c + d) / 4) ^ 4 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
                  mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
                  sq_nonneg (a + b - c - d), sq_nonneg (a - b + c - d), sq_nonneg (a - b - c + d), 
                  sq_nonneg (a * b - c * d), sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c)]
      -- For positive reals, (x)^(1/4) is the fourth root. To establish the theorem, 
      -- we can relate this to powers:
      have h32 : (a * b * c * d : ℝ) ^ (1 / 4 : ℝ) ≤ (( (a + b + c + d) / 4 ) ^ 4) ^ (1 / 4 : ℝ) := by
        apply Real.rpow_le_rpow
        · nlinarith [h31, mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt ha) (le_of_lt hb)) (le_of_lt hc)) (le_of_lt hd)]
        all_goals nlinarith 
      have h42 : (( (a + b + c + d) / 4 ) ^ 4) ^ (1 / 4 : ℝ) = ( (a + b + c + d) / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num 
        all_goals try positivity 
      linarith 
      all_goals try nlinarith 
    linarith 
  linarith