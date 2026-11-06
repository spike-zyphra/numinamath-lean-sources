import Mathlib

theorem inequalities_135831 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = a * b * c) :
    (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) +
    (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) +
    (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) ≥ 1 := by

  have h1 : (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) ≥ (a + b) / (2 * a * b) := by
    have hb1 : 0 < b := hb
    have ha1 : 0 < a := ha
    have h2 : 0 < a * b := mul_pos ha hb
    have h3 : 0 < a ^ 3 + b ^ 3 := by
      positivity
    have h4 : 0 < 2 * a * b := by
      nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 - b^2), sq_nonneg (a^3 - b^3),
      sq_nonneg (a * b), sq_nonneg (a), sq_nonneg (b),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]

  have h2 : (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) ≥ (b + c) / (2 * b * c) := by
    have hb1 : 0 < b := hb
    have hc1 : 0 < c := hc
    have h2 : 0 < b * c := mul_pos hb hc
    have h3 : 0 < b ^ 3 + c ^ 3 := by
      positivity
    have h4 : 0 < 2 * b * c := by
      nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (b^2 - c^2), sq_nonneg (b^3 - c^3),
      sq_nonneg (b * c), sq_nonneg (b), sq_nonneg (c),
      mul_pos hb hc, mul_pos hb ha, mul_pos ha hc
    ]

  have h3 : (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) ≥ (c + a) / (2 * c * a) := by
    have hc1 : 0 < c := hc
    have ha1 : 0 < a := ha
    have h2 : 0 < c * a := mul_pos hc ha
    have h3 : 0 < c ^ 3 + a ^ 3 := by
      positivity
    have h4 : 0 < 2 * c * a := by
      nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (c - a), sq_nonneg (c^2 - a^2), sq_nonneg (c^3 - a^3),
      sq_nonneg (c * a), sq_nonneg (c), sq_nonneg (a),
      mul_pos hc ha, mul_pos hc hb, mul_pos ha hb
    ]

  have h4 : (a + b) / (2 * a * b) + (b + c) / (2 * b * c) + (c + a) / (2 * c * a) = 1 := by
    field_simp
    nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  linarith [h1, h2, h3, h4]