import Mathlib

theorem inequalities_324425 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) +
    (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) ≥
    a^2 + b^2 + c^2 + d^2 := by

  have h1 : 0 < a + b + c := by linarith
  have h2 : 0 < b + c + d := by linarith
  have h3 : 0 < c + d + a := by linarith
  have h4 : 0 < d + a + b := by linarith

  have h5 : (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a ^ 2 + b ^ 2 + c ^ 2) / 3 * (a + b + c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
  have h6 : (b ^ 3 + c ^ 3 + d ^ 3) ≥ (b ^ 2 + c ^ 2 + d ^ 2) / 3 * (b + c + d) := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
        sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - d^2), sq_nonneg (b^2 - d^2),
        mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
      ]
  have h7 : (c ^ 3 + d ^ 3 + a ^ 3) ≥ (c ^ 2 + d ^ 2 + a ^ 2) / 3 * (c + d + a) := by
    nlinarith [sq_nonneg (c - d), sq_nonneg (c - a), sq_nonneg (d - a),
        sq_nonneg (c^2 - d^2), sq_nonneg (d^2 - a^2), sq_nonneg (c^2 - a^2),
        mul_pos hc hd, mul_pos hc ha, mul_pos hd ha
      ]
  have h8 : (d ^ 3 + a ^ 3 + b ^ 3) ≥ (d ^ 2 + a ^ 2 + b ^ 2) / 3 * (d + a + b) := by
    nlinarith [sq_nonneg (d - a), sq_nonneg (d - b), sq_nonneg (a - b),
        sq_nonneg (d^2 - a^2), sq_nonneg (a^2 - b^2), sq_nonneg (d^2 - b^2),
        mul_pos hd ha, mul_pos ha hb, mul_pos hd hb
      ]

  have h9 : (a^3 + b^3 + c^3) / (a + b + c) ≥ (a ^ 2 + b ^ 2 + c ^ 2) / 3 := by
    apply (le_div_iff₀ h1).mpr
    linarith [h5]

  have h10 : (b^3 + c^3 + d^3) / (b + c + d) ≥ (b ^ 2 + c ^ 2 + d ^ 2) / 3 := by
    apply (le_div_iff₀ h2).mpr
    linarith [h6]

  have h11 : (c^3 + d^3 + a^3) / (c + d + a) ≥ (c ^ 2 + d ^ 2 + a ^ 2) / 3 := by
    apply (le_div_iff₀ h3).mpr
    linarith [h7]

  have h12 : (d^3 + a^3 + b^3) / (d + a + b) ≥ (d ^ 2 + a ^ 2 + b ^ 2) / 3 := by
    apply (le_div_iff₀ h4).mpr
    linarith [h8]

  have h13 : (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) +
      (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) ≥
      (a ^ 2 + b ^ 2 + c ^ 2) / 3 + (b ^ 2 + c ^ 2 + d ^ 2) / 3 + (c ^ 2 + d ^ 2 + a ^ 2) / 3 + (d ^ 2 + a ^ 2 + b ^ 2) / 3 := by
    linarith [h9, h10, h11, h12]

  have h14 : (a ^ 2 + b ^ 2 + c ^ 2) / 3 + (b ^ 2 + c ^ 2 + d ^ 2) / 3 + (c ^ 2 + d ^ 2 + a ^ 2) / 3 + (d ^ 2 + a ^ 2 + b ^ 2) / 3 = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
    ring

  linarith [h13, h14]