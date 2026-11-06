import Mathlib

theorem inequalities_90003 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≥ 1 / a + 1 / b + 1 / c) :
    a + b + c ≥ 3 / (a * b * c) := by
  have pos1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h1 : (a + b + c) * (a * b * c) ≥ a * b + a * c + b * c := by 
    have h3 : (a + b + c) * (a * b * c) ≥ (1 / a + 1 / b + 1 / c) * (a * b * c) := by
      have h4 : (1 / a + 1 / b + 1 / c) ≤ (a + b + c) := by linarith
      have h5 : 0 < a * b * c := pos1
      nlinarith [h4, h5]
    have h5 : (1 / a + 1 / b + 1 / c) * (a * b * c) = a * b + a * c + b * c := by 
      field_simp
      <;> ring
    nlinarith [h3, h5]

  have h2 : (a + b + c) * (a * b * c) ≥ 3 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]

  have h3 : a + b + c ≥ 3 / (a * b * c) := by
    have h4 : (a + b + c) * (a * b * c) ≥ 3 := h2
    have pos1' : 0 < a * b * c := pos1
    have h5 : (a + b + c) ≥ 3 / (a * b * c) := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    linarith

  exact h3