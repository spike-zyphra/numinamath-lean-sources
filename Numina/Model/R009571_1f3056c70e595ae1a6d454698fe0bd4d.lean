import Mathlib
theorem algebra_607145 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (9 * b * c + 1) + b / (9 * c * a + 1) + c / (9 * a * b + 1) ≥
    (a + b + c) / (1 + (a + b + c)^2) := by
  have h1 : a / (9 * b * c + 1) + b / (9 * c * a + 1) + c / (9 * a * b + 1) - (a + b + c) / (1 + (a + b + c)^2) ≥ 0 := by 
    have h2 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      exact ha
      exact hb
      exact hc
    have h3 : 0 < (9 * b * c + 1) * (9 * c * a + 1) * (9 * a * b + 1) * (1 + (a + b + c)^2) := by 
      positivity 
    have h4 : a / (9 * b * c + 1) + b / (9 * c * a + 1) + c / (9 * a * b + 1) - (a + b + c) / (1 + (a + b + c)^2) =
        (a * (9 * c * a + 1) * (9 * a * b + 1) * (1 + (a + b + c)^2) +
        b * (9 * b * c + 1) * (9 * a * b + 1) * (1 + (a + b + c)^2) +
        c * (9 * b * c + 1) * (9 * c * a + 1) * (1 + (a + b + c)^2) -
        (a + b + c) * (9 * b * c + 1) * (9 * c * a + 1) * (9 * a * b + 1))
        / ((9 * b * c + 1) * (9 * c * a + 1) * (9 * a * b + 1) * (1 + (a + b + c)^2)) := by 
      field_simp 
      ring 
    rw [h4]
    apply div_nonneg 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        sq_nonneg (a * b * (a - b)), sq_nonneg (b * c * (b - c)), sq_nonneg (c * a * (c - a)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc 
        ]
    positivity 
  linarith