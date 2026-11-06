import Mathlib

theorem inequalities_320881 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : 1 / (a ^ 2 + 2) + 1 / (b ^ 2 + 2) = 1 / 3) :
    1 ≤ 1 / a + 1 / b := by
  have h1 : a ^ 2 + 2 > 0 := by nlinarith [sq_pos_of_pos ha]
  have h2 : b ^ 2 + 2 > 0 := by nlinarith [sq_pos_of_pos hb]
  have h3 : 3 * (a ^ 2 + b ^ 2 + 4) = (a ^ 2 + 2) * (b ^ 2 + 2) := by
    field_simp at h ⊢
    nlinarith
  have h3_eq : a ^ 2 * b ^ 2 - a ^ 2 - b ^ 2 - 8 = 0 := by
    nlinarith
  have h7 : 0 < a * b := mul_pos ha hb
  have h8 : a + b - a * b ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 4), sq_nonneg (a - 2), sq_nonneg (b - 2),
      mul_pos ha hb, sq_nonneg (a * b - (a + b))
    ]
  have h9 : (1 / a + 1 / b) - 1 ≥ 0 := by
    have h10 : (1 / a + 1 / b) - 1 = (a + b - a * b) / (a * b) := by
      field_simp
      <;> ring
    rw [h10] at *
    apply div_nonneg
    linarith
    positivity
  linarith