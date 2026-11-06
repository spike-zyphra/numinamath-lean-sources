import Mathlib

theorem inequalities_598786 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) +
     (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (a + c) ^ 2) +
     (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (b + a) ^ 2)) ≤ 8 := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals assumption
  have h2 : 0 < 2 * a ^ 2 + (b + c) ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h3 : 0 < 2 * b ^ 2 + (a + c) ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h4 : 0 < 2 * c ^ 2 + (b + a) ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h5 : ((2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) +
     (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (a + c) ^ 2) +
     (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (b + a) ^ 2)) - 8 ≤ 0 := by
    have h6 : ((2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) +
         (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (a + c) ^ 2) +
         (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (b + a) ^ 2)) - 8 =
        (( (2 * a + b + c) ^ 2 * (2 * b ^ 2 + (a + c) ^ 2) * (2 * c ^ 2 + (b + a) ^ 2 ) ) + 
         ( (a + 2 * b + c) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * c ^ 2 + (b + a) ^ 2 ) ) +
         ( (a + b + 2 * c) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (a + c) ^ 2 ) ) - 8 * ( (2 * a ^ 2 + (b + c) ^ 2 ) * ( 2 * b ^ 2 + (a + c) ^ 2 ) * ( 2 * c ^ 2 + (b + a) ^ 2 ) )) / ( (2 * a ^ 2 + (b + c) ^ 2 ) * ( 2 * b ^ 2 + (a + c) ^ 2 ) * ( 2 * c ^ 2 + (b + a) ^ 2 ) ) := by 
      field_simp
      <;> ring
      <;> field_simp
      <;> ring
    rw [h6]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show the numerator is ≤ 0
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (c - a)), 
            sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (c - a)), 
            sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (c - a)), 
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
    · -- Show the denominator is ≥ 0
      positivity
  linarith