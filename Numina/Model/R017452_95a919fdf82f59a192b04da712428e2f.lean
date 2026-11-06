import Mathlib

theorem inequalities_597824
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    3 * (a + b + c) ≥ 8 * (a * b * c) ^ ((1 : ℝ) / 3) +
      ((a ^ 3 + b ^ 3 + c ^ 3) / 3) ^ ((1 : ℝ) / 3) := by
  have h1 : 0 < (a * b * c : ℝ) := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : 0 < a ^ 3 + b ^ 3 + c ^ 3 := by
    positivity
  have h7 : (a * b * c) ^ ((1 : ℝ) / 3) ≤ (a + b + c) / 3 := by
    have h8 : (a * b * c : ℝ) ≤ (( (a + b + c) / 3 ) ^ 3 ) := by
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a^2 + b^2 + c^2 - a * b - b * c - c * a), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    have h9 : (a * b * c : ℝ) ^ ((1 : ℝ) / 3) ≤ ( ( (a + b + c) / 3 ) ^ 3 ) ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_le_rpow
      · -- Show 0 ≤ (a * b * c : ℝ)
        positivity
      · -- Show (a * b * c : ℝ) ≤ ( (a + b + c) / 3 ) ^ 3
        linarith
      · -- Show 0 ≤ ( (a + b + c) / 3 ) ^ 3
        positivity
    have h10 : ( ( (a + b + c) / 3 ) ^ 3 ) ^ ((1 : ℝ) / 3) = ( (a + b + c) / 3 : ℝ ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        positivity
    nlinarith
  have h10 : ((a ^ 3 + b ^ 3 + c ^ 3) / 3) ^ ((1 : ℝ) / 3) ≥ (a + b + c) / 3 := by
    have h11 : ((a ^ 3 + b ^ 3 + c ^ 3) / 3) ≥ ((a + b + c) / 3) ^ 3 := by
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a^2 + b^2 + c^2 - a * b - b * c - c * a), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    have h12 : ((a ^ 3 + b ^ 3 + c ^ 3) / 3) ^ ((1 : ℝ) / 3) ≥ (( (a + b + c) / 3 ) ^ 3 ) ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_le_rpow
      · -- Show 0 ≤ ( (a ^ 3 + b ^ 3 + c ^ 3) / 3 : ℝ )
        positivity
      · -- Show ( (a ^ 3 + b ^ 3 + c ^ 3) / 3 : ℝ ) ≥ ( (a + b + c) / 3 : ℝ ) ^ 3
        linarith
      · -- Show 0 ≤ ( (a + b + c) / 3 : ℝ ) ^ 3
        positivity
    have h13 : (( (a + b + c) / 3 ) ^ 3 ) ^ ((1 : ℝ) / 3) = ( (a + b + c) / 3 : ℝ ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        positivity
    nlinarith
  have h91 : ( (a * b * c) ^ ((1 : ℝ) / 3) ) ^ 3 = a * b * c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals
      positivity
  have h92 : ( ((a ^ 3 + b ^ 3 + c ^ 3) / 3) ^ ((1 : ℝ) / 3) ) ^ 3 = (a ^ 3 + b ^ 3 + c ^ 3) / 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals
      positivity
  nlinarith [sq_nonneg ( (a * b * c) ^ ((1 : ℝ) / 3) - ( (a ^ 3 + b ^ 3 + c ^ 3) / 3) ^ ((1 : ℝ) / 3) ), 
    sq_nonneg (a + b + c - 3 * ( (a * b * c) ^ ((1 : ℝ) / 3) ) ), 
    sq_nonneg ( ( (a ^ 3 + b ^ 3 + c ^ 3) / 3 ) ^ ((1 : ℝ) / 3) - (a + b + c) / 3 ), 
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
    sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)
  ]