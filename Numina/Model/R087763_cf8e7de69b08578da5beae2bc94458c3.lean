import Mathlib

theorem inequalities_82754 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b * c) + b / (c * a) + c / (a * b) ≥ 2 / a + 2 / b - 2 / c := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h2 : a / (b * c) + b / (c * a) + c / (a * b) - (2 / a + 2 / b - 2 / c) ≥ 0 := by
    have h3 : a / (b * c) + b / (c * a) + c / (a * b) - (2 / a + 2 / b - 2 / c) = 
      (a^2 + b^2 + c^2 - (2 * b * c + 2 * a * c - 2 * a * b)) / (a * b * c) := by
      field_simp [show 0 < b by linarith, show 0 < a by linarith, show 0 < c by linarith]
      ring
    rw [h3]
    
    have h4 : a^2 + b^2 + c^2 - (2 * b * c + 2 * a * c - 2 * a * b) ≥ 0 := by 
      nlinarith [sq_nonneg (a + b - c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]

    have h5 : a * b * c > 0 := by
      apply mul_pos
      apply mul_pos
      exact ha
      exact hb
      exact hc

    apply div_nonneg 
    · linarith
    linarith

  linarith