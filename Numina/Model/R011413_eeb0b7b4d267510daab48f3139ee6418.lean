import Mathlib

theorem inequalities_32331 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a * b / (a ^ 5 + b ^ 5 + a * b) +
    b * c / (b ^ 5 + c ^ 5 + b * c) +
    a * c / (c ^ 5 + a ^ 5 + a * c) ≤ 1 := by
  have h1 : a * b / (a ^ 5 + b ^ 5 + a * b) ≤ 1 / (a * b * (a + b) + 1) := by
    have h1 : a ^ 5 + b ^ 5 ≥ a * b * (a + b) * (a * b) := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg (a^3 - b^3),
        sq_nonneg (a^2 * b - a * b^2), pow_pos ha 2, pow_pos hb 2,
        pow_pos ha 3, pow_pos hb 3,
        pow_pos ha 4, pow_pos hb 4,
        pow_pos ha 5, pow_pos hb 5,
        mul_pos ha hb
        ]
    have pos1 : 0 < a ^ 5 + b ^ 5 + a * b := by positivity
    have pos2 : 0 < a * b * (a + b) + 1 := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  have h2 : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ 1 / (b * c * (b + c) + 1) := by
    have h2 : b ^ 5 + c ^ 5 ≥ b * c * (b + c) * (b * c) := by
      nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), sq_nonneg (b^3 - c^3),
        sq_nonneg (b^2 * c - b * c^2), pow_pos hb 2, pow_pos hc 2,
        pow_pos hb 3, pow_pos hc 3,
        pow_pos hb 4, pow_pos hc 4,
        pow_pos hb 5, pow_pos hc 5,
        mul_pos hb hc
        ]
    have pos1 : 0 < b ^ 5 + c ^ 5 + b * c := by positivity
    have pos2 : 0 < b * c * (b + c) + 1 := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  have h3 : a * c / (c ^ 5 + a ^ 5 + a * c) ≤ 1 / (c * a * (c + a) + 1) := by
    have h3 : c ^ 5 + a ^ 5 ≥ c * a * (c + a) * (c * a) := by
      nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), sq_nonneg (c * (c - a)), sq_nonneg (a * (c - a)), sq_nonneg (c^3 - a^3),
        sq_nonneg (c^2 * a - c * a^2), pow_pos hc 2, pow_pos ha 2,
        pow_pos hc 3, pow_pos ha 3,
        pow_pos hc 4, pow_pos ha 4,
        pow_pos hc 5, pow_pos ha 5,
        mul_pos hc ha
        ]
    have pos1 : 0 < c ^ 5 + a ^ 5 + a * c := by positivity
    have pos2 : 0 < c * a * (c + a) + 1 := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  have h4 : 1 / (a * b * (a + b) + 1) + 1 / (b * c * (b + c) + 1) + 1 / (c * a * (c + a) + 1) = 1 := by
    have habc' : c = 1 / (a * b) := by
      field_simp [(show 0 < a * b by positivity)]
      nlinarith
    rw [habc']
    field_simp [(show 0 < a * b * (a + b) + 1 by positivity), (show 0 < b * (1 / (a * b)) * (b + (1 / (a * b))) + 1 by positivity), (show 0 < (1 / (a * b)) * a * ((1 / (a * b)) + a) + 1 by positivity)]
    <;> nlinarith [mul_pos ha hb, mul_pos ha (show 0 < (1 / (a * b) : ℝ) by positivity), mul_pos hb (show 0 < (1 / (a * b) : ℝ) by positivity)]
  linarith [h1, h2, h3, h4]