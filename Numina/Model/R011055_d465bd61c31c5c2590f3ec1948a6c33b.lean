import Mathlib

theorem inequalities_220668 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c * d = 1) :
    4 ≤ (a^4 + b^4) / (a^2 + b^2) + (b^4 + c^4) / (b^2 + c^2) +
        (c^4 + d^4) / (c^2 + d^2) + (d^4 + a^4) / (d^2 + a^2) := by

  have h1 : (a^4 + b^4) / (a^2 + b^2) >= (a^2 + b^2) / 2 := by
    have h2 : 0 < a^2 + b^2 := by
      nlinarith [ha, hb]
    apply (le_div_iff₀ h2).mpr
    nlinarith [sq_nonneg (a^2 - b^2)]
  have h2 : (b^4 + c^4) / (b^2 + c^2) >= (b^2 + c^2) / 2 := by
    have h3 : 0 < b^2 + c^2 := by
      nlinarith [hb, hc]
    apply (le_div_iff₀ h3).mpr
    nlinarith [sq_nonneg (b^2 - c^2)]
  have h3 : (c^4 + d^4) / (c^2 + d^2) >= (c^2 + d^2) / 2 := by
    have h4 : 0 < c^2 + d^2 := by
      nlinarith [hc, hd]
    apply (le_div_iff₀ h4).mpr
    nlinarith [sq_nonneg (c^2 - d^2)]
  have h4 : (d^4 + a^4) / (d^2 + a^2) >= (d^2 + a^2) / 2 := by
    have h5 : 0 < d^2 + a^2 := by
      nlinarith [hd, ha]
    apply (le_div_iff₀ h5).mpr
    nlinarith [sq_nonneg (d^2 - a^2)
    ]
  have h5 : (a^4 + b^4) / (a^2 + b^2) + (b^4 + c^4) / (b^2 + c^2) + (c^4 + d^4) / (c^2 + d^2) + (d^4 + a^4) / (d^2 + a^2) >= (a^2 + b^2) / 2 + (b^2 + c^2) / 2 + (c^2 + d^2) / 2 + (d^2 + a^2) / 2 := by
    linarith [h1, h2, h3, h4]
  have h5' : (a^2 + b^2) / 2 + (b^2 + c^2) / 2 + (c^2 + d^2) / 2 + (d^2 + a^2) / 2 = a^2 + b^2 + c^2 + d^2 := by
    linarith
  have h6 : a^2 + b^2 + c^2 + d^2 >= 4 := by
    nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (c^2 - 1), sq_nonneg (d^2 - 1),
      sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (a * d - 1), sq_nonneg (b * c - 1), sq_nonneg (b * d - 1), sq_nonneg (c * d - 1),
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
    ]
  linarith [h5, h5', h6]