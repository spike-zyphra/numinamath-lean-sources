import Mathlib

theorem algebra_308171 {x : ℝ} (hx : x ≠ 0) (h : x - 1/x = Real.sqrt 5) :
    (x^10 + x^6 + x^4 + 1) / (x^10 + x^8 + x^2 + 1) = 42/47 := by
  have h1 : x ^ 2 - x * Real.sqrt 5 - 1 = 0 := by
    have h2 : x ≠ 0 := hx
    have eq1 : x - 1 / x = Real.sqrt 5 := h
    field_simp at eq1
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h2 : x ^ 2 + 1 / x ^ 2 = 7 := by
    have h3 : x - 1 / x = Real.sqrt 5 := h
    have h4 : (x - 1 / x) ^ 2 = (Real.sqrt 5 : ℝ) ^ 2 := by rw [h3]
    rw [Real.sq_sqrt (by norm_num)] at h4
    field_simp at h4 ⊢
    nlinarith
  have h3 : x ^ 4 + 1 / x ^ 4 = 47 := by
    have h4 : x ^ 2 + 1 / x ^ 2 = 7 := h2
    have h5 : (x ^ 2 + 1 / x ^ 2) ^ 2 = (7 : ℝ) ^ 2 := by rw [h4]
    field_simp at h5 ⊢
    nlinarith
  have h4 : x ^ 6 + 1 / x ^ 6 = 322 := by
    have h5 : x ^ 2 + 1 / x ^ 2 = 7 := h2
    have h6 : x ^ 4 + 1 / x ^ 4 = 47 := h3
    calc
      x ^ 6 + 1 / x ^ 6
        = (x ^ 2 + 1 / x ^ 2) * (x ^ 4 + 1 / x ^ 4) - (x ^ 2 + 1 / x ^ 2) := by field_simp; ring
      _ = (7 : ℝ) * (47 : ℝ) - (7 : ℝ) := by rw [h5, h6]
      _ = (322 : ℝ) := by norm_num
  have h5 : x ^ 2 + 1 / x ^ 2 = 7 := h2
  have h6 : x ^ 4 + 1 / x ^ 4 = 47 := h3
  have h7 : x ^ 6 + 1 / x ^ 6 = 322 := h4
  have h9 : x ^ 8 + 1 / x ^ 8 = (47 : ℝ) ^ 2 - 2 := by
    have h9 : x ^ 8 + 1 / x ^ 8 = (x ^ 4 + 1 / x ^ 4) ^ 2 - 2 := by
      field_simp
      <;> ring
    rw [h9, h3]
    all_goals norm_num
  have hx3 : x ^ 10 + x ^ 6 + x ^ 4 + 1 = 42 * (x ^ 10 + x ^ 8 + x ^ 2 + 1) / 47 := by
    field_simp at h5 h6 h7 h9
    field_simp at *
    nlinarith [sq_pos_of_ne_zero (show x^2 ≠ 0 by
      intro h'
      have : x = 0 := by nlinarith
      tauto
    ), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  rw [hx3]
  <;> field_simp at *
  <;> nlinarith [sq_pos_of_ne_zero (show x^2 ≠ 0 by
    intro h'
    have : x = 0 := by nlinarith
    tauto
  ), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]