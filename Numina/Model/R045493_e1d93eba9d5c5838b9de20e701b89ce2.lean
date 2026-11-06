import Mathlib

theorem inequalities_56824
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d) :
    ((a + b + c)^2 / (a^2 + b^2 + c^2) +
     (b + c + d)^3 / (b^3 + c^3 + d^3) +
     (c + d + a)^4 / (c^4 + d^4 + a^4) +
     (d + a + b)^5 / (d^5 + a^5 + b^5)) ≤ 120 := by
  have h1 : (a + b + c)^2 ≤ 3 * (a^2 + b^2 + c^2) := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h2 : (b + c + d)^3 ≤ 9 * (b^3 + c^3 + d^3) := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (b + c + d - 3 * b), sq_nonneg (b + c + d - 3 * c), sq_nonneg (b + c + d - 3 * d),
            sq_nonneg (b^2 - c^2), sq_nonneg (b^2 - d^2), sq_nonneg (c^2 - d^2),
            mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
  have h3 : (c + d + a)^4 ≤ 27 * (c^4 + d^4 + a^4) := by
    nlinarith [sq_nonneg (c^2 - d^2), sq_nonneg (c^2 - a^2), sq_nonneg (d^2 - a^2),
      sq_nonneg (c - d), sq_nonneg (c - a), sq_nonneg (d - a), 
      sq_nonneg (c * (c - d)), sq_nonneg (c * (c - a)), sq_nonneg (d * (d - a)), sq_nonneg (d * (d - c)), sq_nonneg (a * (a - c)), sq_nonneg (a * (a - d)), 
      mul_pos hc hd, mul_pos hc ha, mul_pos hd ha, 
      sq_nonneg (c + d + a - 3 * c), sq_nonneg (c + d + a - 3 * d), sq_nonneg (c + d + a - 3 * a),
      pow_two_nonneg (c^2 - d^2), pow_two_nonneg (c^2 - a^2), pow_two_nonneg (d^2 - a^2),
      pow_two_nonneg (c - d), pow_two_nonneg (c - a), pow_two_nonneg (d - a)
    ]
  have h4 : (d + a + b)^5 ≤ 81 * (d^5 + a^5 + b^5) := by 
    nlinarith [sq_nonneg (d^2 - a^2), sq_nonneg (d^2 - b^2), sq_nonneg (a^2 - b^2),
      sq_nonneg (d - a), sq_nonneg (d - b), sq_nonneg (a - b), 
      sq_nonneg (d * (d - a)), sq_nonneg (d * (d - b)), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - d)), sq_nonneg (b * (b - d)), sq_nonneg (b * (b - a)), 
      mul_pos hd ha, mul_pos hd hb, mul_pos ha hb, 
      sq_nonneg (d + a + b - 3 * d), sq_nonneg (d + a + b - 3 * a), sq_nonneg (d + a + b - 3 * b),
      pow_two_nonneg (d^2 - a^2), pow_two_nonneg (d^2 - b^2), pow_two_nonneg (a^2 - b^2),
      pow_two_nonneg (d - a), pow_two_nonneg (d - b), pow_two_nonneg (a - b)
    ]
  have h5 : (a + b + c)^2 / (a^2 + b^2 + c^2) ≤ 3 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith 
  have h6 : (b + c + d)^3 / (b^3 + c^3 + d^3) ≤ 9 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith 
  have h7 : (c + d + a)^4 / (c^4 + d^4 + a^4) ≤ 27 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith 
  have h8 : (d + a + b)^5 / (d^5 + a^5 + b^5) ≤ 81 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith 
  linarith [h5, h6, h7, h8]