import Mathlib

theorem inequalities_202916 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    4 < 1 / a + 1 / b + 1 / c := by

  have h1 : 0 < a * b * c := by
    positivity

  have h2 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
    field_simp
    ring

  have h3 : b * c + a * c + a * b > 4 * a * b * c := by
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
      mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith),
      mul_pos ha (show 0 < a * b by nlinarith), 
      mul_pos ha (show 0 < a * c by nlinarith), 
      mul_pos ha (show 0 < b * c by nlinarith), 
      mul_pos hb (show 0 < a * b by nlinarith), 
      mul_pos hb (show 0 < b * c by nlinarith), 
      mul_pos hc (show 0 < a * c by nlinarith), 
      mul_pos hc (show 0 < b * c by nlinarith)
    ]

  have h4 : (b * c + a * c + a * b) / (a * b * c) > 4 := by
    have h5 : b * c + a * c + a * b > 4 * (a * b * c) := by 
      nlinarith [h, h3, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h6 : a * b * c > 0 := h1
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith

  linarith [h2, h4]