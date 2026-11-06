import Mathlib

theorem inequalities_317234 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) ≥ 1 := by
  have h1 : 0 < 1 + 2 * a := by nlinarith
  have h2 : 0 < 1 + 2 * b := by nlinarith
  have h3 : 0 < 1 + 2 * c := by nlinarith
  have h7 : (1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) ≥ (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc
      ]
  have h8 : 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1 ≥ 0 := by
    have h9 : 0 < (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) := by positivity
    have h10 : (1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1) = 
      ((1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) - (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) / 
      ((1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) := by 
      field_simp [h1, h2, h3]
      <;> ring
    rw [h10]
    apply div_nonneg 
    linarith [h7]
    positivity
  linarith