import Mathlib

theorem inequalities_220827 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    a / (a + 5) + b / (b + 5) + c / (c + 5) ≤ 1 / 2 := by

  have h1 : a / (a + 5) ≤ (5 * a + 1) / 36 := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1)]
  
  have h2 : b / (b + 5) ≤ (5 * b + 1) / 36 := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b - 1)]
  
  have h3 : c / (c + 5) ≤ (5 * c + 1) / 36 := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (c - 1)]

  have h4 : a / (a + 5) + b / (b + 5) + c / (c + 5) ≤ (5 * a + 1) / 36 + (5 * b + 1) / 36 + (5 * c + 1) / 36 := by 
    linarith [h1, h2, h3]

  have h5 : (5 * a + 1) / 36 + (5 * b + 1) / 36 + (5 * c + 1) / 36 ≤ 1 / 2 := by
    have h6 : a + b + c ≤ 3 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          h]

    linarith

  linarith [h4, h5]