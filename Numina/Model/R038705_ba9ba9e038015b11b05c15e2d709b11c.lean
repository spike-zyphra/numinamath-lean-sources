import Mathlib

theorem inequalities_604040 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
     (a + 2 * b + c)^2 / (2 * b^2 + (a + c)^2) +
     (a + b + 2 * c)^2 / (2 * c^2 + (b + a)^2)) ≤ 8 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : ((2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) +
      (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (a + c) ^ 2) +
      (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (b + a) ^ 2)) - 8 ≤ 0 := by
    have pos1 : 0 < 2 * a ^ 2 + (b + c) ^ 2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
    have pos2 : 0 < 2 * b ^ 2 + (a + c) ^ 2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
    have pos3 : 0 < 2 * c ^ 2 + (b + a) ^ 2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
    have h3 : ((2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) +
        (a + 2 * b + c) ^ 2 / (2 * b ^ 2 + (a + c) ^ 2) +
        (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (b + a) ^ 2)) - 8 =
        (( (2 * a + b + c) ^ 2 * (2 * b ^ 2 + (a + c) ^ 2) * (2 * c ^ 2 + (b + a) ^ 2 ) +
          (a + 2 * b + c) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * c ^ 2 + (b + a) ^ 2 ) +
          (a + b + 2 * c) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (a + c) ^ 2 ) - 8 * (2 * a ^ 2 + (b + c) ^ 2 ) * (2 * b ^ 2 + (a + c) ^ 2 ) * (2 * c ^ 2 + (b + a) ^ 2 )) / ( (2 * a ^ 2 + (b + c) ^ 2 ) * (2 * b ^ 2 + (a + c) ^ 2 ) * (2 * c ^ 2 + (b + a) ^ 2 ) )) := by 
      field_simp 
      ring
    rw [h3]
    have pos4 : 0 < (2 * a ^ 2 + (b + c) ^ 2 ) * (2 * b ^ 2 + (a + c) ^ 2 ) * (2 * c ^ 2 + (b + a) ^ 2 ) := by
      positivity
    have h4 : ( (2 * a + b + c) ^ 2 * (2 * b ^ 2 + (a + c) ^ 2) * (2 * c ^ 2 + (b + a) ^ 2 ) +
        (a + 2 * b + c) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * c ^ 2 + (b + a) ^ 2 ) +
        (a + b + 2 * c) ^ 2 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (a + c) ^ 2 ) - 8 * (2 * a ^ 2 + (b + c) ^ 2 ) * (2 * b ^ 2 + (a + c) ^ 2 ) * (2 * c ^ 2 + (b + a) ^ 2 ) ) ≤ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
                sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
                sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
                mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos ha h1, mul_pos hb h1, mul_pos hc h1
      ]
    apply div_nonpos_of_nonpos_of_nonneg h4 (by positivity)
  linarith