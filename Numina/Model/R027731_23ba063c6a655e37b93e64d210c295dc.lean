import Mathlib

theorem inequalities_8543 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a / b + b / c + c / a ≥ a + b + c := by

  have h1 : 0 < a * b * c := by
    positivity

  have h2 : a / b + b / c + c / a - (a + b + c) ≥ 0 := by

    have h3 : a / b + b / c + c / a - (a + b + c) =
        (a ^ 2 * c + a * b ^ 2 + b * c ^ 2 - (a + b + c) * (a * b * c)) / (a * b * c) := by
      field_simp
      ring
    rw [h3]

    have h4 : a ^ 2 * c + a * b ^ 2 + b * c ^ 2 - (a + b + c) * (a * b * c) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
    
    have h5 : a * b * c > 0 := by
      positivity

    apply div_nonneg
    . linarith [h4]
    . positivity

  linarith