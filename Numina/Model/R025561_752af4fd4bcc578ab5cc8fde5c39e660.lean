import Mathlib

theorem inequalities_33532 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    a^12 + b^12 + c^12 + 8 * (a * b + b * c + c * a) ≥ 27 := by

  have h1 : a ^ 12 + b ^ 12 + c ^ 12 + 8 * (a * b + b * c + c * a) - 27 ≥ 0 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a^3 - b^3), sq_nonneg (b^3 - c^3), sq_nonneg (c^3 - a^3),
      sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (c^2 - 1),
      sq_nonneg (a^3 - 1), sq_nonneg (b^3 - 1), sq_nonneg (c^3 - 1),
      sq_nonneg (a^4 - 1), sq_nonneg (b^4 - 1), sq_nonneg (c^4 - 1),
      sq_nonneg (a^6 - 1), sq_nonneg (b^6 - 1), sq_nonneg (c^6 - 1)
    ]
  linarith