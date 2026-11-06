import Mathlib
theorem algebra_604521 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h1 : a + b > c) (h2 : a + c > b) (h3 : b + c > a) :
  ((a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b)) ^ ((1 : ℝ) / 3) >
  (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by

  have h4 : a ^ 2 + b * c > (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3), mul_pos (sub_pos.mpr h3) (sub_pos.mpr h1)]
  have h5 : b ^ 2 + c * a > (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3), mul_pos (sub_pos.mpr h3) (sub_pos.mpr h1)]
  have h6 : c ^ 2 + a * b > (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3), mul_pos (sub_pos.mpr h3) (sub_pos.mpr h1)]

  have h7 : (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b) > ((a ^ 2 + b ^ 2 + c ^ 2) / 2) ^ 3 := by
    have h12 : 0 < (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
    have h9 : (a ^ 2 + b * c) > (a ^ 2 + b ^ 2 + c ^ 2) / 2 := h4
    have h10 : (b ^ 2 + c * a) > (a ^ 2 + b ^ 2 + c ^ 2) / 2 := h5
    have h11 : (c ^ 2 + a * b) > (a ^ 2 + b ^ 2 + c ^ 2) / 2 := h6
    have h14 : (a ^ 2 + b * c) * (b ^ 2 + c * a) > ((a ^ 2 + b ^ 2 + c ^ 2) / 2) ^ 2 := by
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < (a ^ 2 + b ^ 2 + c ^ 2) / 2 by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
      ) (show 0 < (a ^ 2 + b ^ 2 + c ^ 2) / 2 by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
      )]
    have h16 : (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b) > ((a ^ 2 + b ^ 2 + c ^ 2) / 2) ^ 3 := by
      have h17 : (c ^ 2 + a * b) > (a ^ 2 + b ^ 2 + c ^ 2) / 2 := h6
      have h18 : 0 < ((a ^ 2 + b ^ 2 + c ^ 2) / 2 : ℝ) := by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < (a ^ 2 + b * c) * (b ^ 2 + c * a) by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      ) (show 0 < (c ^ 2 + a * b) by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      )]
    linarith

  have h8 : ((a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b)) ^ ((1 : ℝ) / 3) > (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
    have h9 : (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b) > ((a ^ 2 + b ^ 2 + c ^ 2) / 2) ^ 3 := h7
    have h13 : ((a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b)) ≥ 0 := by
      positivity
    have h14 : ((a ^ 2 + b ^ 2 + c ^ 2) / 2) ^ 3 ≥ 0 := by
      positivity
    have h15 : (( (a ^ 2 + b ^ 2 + c ^ 2) / 2 ) ^ 3) ^ ((1 : ℝ) / 3) = (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        positivity
    have h16 : ((a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b)) ^ ((1 : ℝ) / 3) > (( (a ^ 2 + b ^ 2 + c ^ 2) / 2 ) ^ 3) ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_lt_rpow
      all_goals
        try { positivity }
        try { nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc] }
    have h17 : (( (a ^ 2 + b ^ 2 + c ^ 2) / 2 ) ^ 3) ^ ((1 : ℝ) / 3) = (a ^ 2 + b ^ 2 + c ^ 2) / 2 := h15
    linarith

  exact h8