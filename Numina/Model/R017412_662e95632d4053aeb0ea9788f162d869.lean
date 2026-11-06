import Mathlib

theorem inequalities_196766 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b = 1) :
    (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by

  have h1 : 0 < a * b := by
    nlinarith

  have h2 : a + 1 / a + b + 1 / b ≥ 5 := by
    have h3 : a + b = 1 := h
    have h4 : a * b ≤ 1 / 4 := by
      nlinarith [sq_nonneg (a - 1 / 2)]
    have h5 : a * b > 0 := h1
    have h6 : 1 / (a * b) ≥ 4 := by
      have h7 : a * b ≤ 1 / 4 := h4
      have h8 : a * b > 0 := h5
      have h9 : 1 / (a * b) ≥ 1 / (1 / 4) := by
        apply one_div_le_one_div_of_le
        all_goals
          nlinarith
      have h10 : 1 / (1 / 4 : ℝ) = 4 := by
        field_simp
      linarith [h9, h10]
    have h7 : a + 1 / a + b + 1 / b = 1 + 1 / (a * b) := by
      field_simp
      <;> nlinarith [h3]
    linarith [h7, h6]

  have h3 : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ ( (a + 1 / a + (b + 1 / b) ) ) ^ 2 / 2 := by
    linarith [sq_nonneg ( (a + 1 / a) - (b + 1 / b) ) ]

  have h4 : ( (a + 1 / a + (b + 1 / b) ) ) ^ 2 / 2 ≥ 25 / 2 := by
    have h5 : a + 1 / a + b + 1 / b ≥ 5 := h2
    nlinarith [sq_nonneg (a + 1 / a + b + 1 / b - 5)]

  linarith [h3, h4]