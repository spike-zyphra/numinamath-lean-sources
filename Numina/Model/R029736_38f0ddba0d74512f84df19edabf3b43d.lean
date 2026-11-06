import Mathlib

open Real

theorem inequalities_600274
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a^2 / (1 + a^2) + b^2 / (1 + b^2) + c^2 / (1 + c^2) = 1) :
    a * b * c ≤ sqrt 2 / 4 := by
  have h1 : 0 < 1 + a^2 := by nlinarith
  have h2 : 0 < 1 + b^2 := by nlinarith
  have h3 : 0 < 1 + c^2 := by nlinarith
  have h4 : a^2 * (1 + b^2) * (1 + c^2) + b^2 * (1 + a^2) * (1 + c^2) + c^2 * (1 + a^2) * (1 + b^2) = (1 + a^2) * (1 + b^2) * (1 + c^2) := by
    have eq1 : a^2 / (1 + a^2) + b^2 / (1 + b^2) + c^2 / (1 + c^2) = 1 := h
    field_simp at eq1 ⊢
    nlinarith
  have h5 : (a * b * c) ^ 2 ≤ 1 / 8 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a^2 * b^2 - 1 / 4), sq_nonneg (b^2 * c^2 - 1 / 4), sq_nonneg (c^2 * a^2 - 1 / 4), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
  have h6 : a * b * c ≤ Real.sqrt (1 / 8) := by
    have h8 : (a * b * c) ^ 2 ≥ 0 := by nlinarith
    have h9 : a * b * c ≥ 0 := by positivity
    have h10 : Real.sqrt ((a * b * c) ^ 2) = a * b * c := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg h9]
    have h11 : (a * b * c) ^ 2 ≤ (1 / 8 : ℝ) := by nlinarith [h5]
    have h12 : Real.sqrt ((a * b * c) ^ 2) ≤ Real.sqrt (1 / 8 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith [h11]
    nlinarith [h10, h12, Real.sqrt_nonneg (1 / 8)]
  have h9 : Real.sqrt (1 / 8) = Real.sqrt 2 / 4 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
  linarith [h6, h9]