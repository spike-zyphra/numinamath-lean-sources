import Mathlib

open Real

theorem other_155122 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 2 * (a + b) = a * b) (h2 : a + b + c = a * b * c) :
    c ≤ 8 / 15 := by
  have ha1 : 0 < a * b := by
    nlinarith
  have h3 : a * b * c - c = a + b := by
    linarith
  have h4 : c = (a + b) / (a * b - 1) := by
    have h5 : a * b - 1 ≠ 0 := by
      by_contra h
      have h6 : a * b * c - c = a + b := by
        linarith
      have h7 : a * b = 1 := by
        linarith
      have h8 : c = 0 := by
        nlinarith
      linarith
    field_simp [h5]
    linarith
  have h5 : a * b = 2 * (a + b) := by
    linarith
  have h6 : (a * b) ≤ ((a + b) / 2) ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  have h7 : a + b ≥ 8 := by
    nlinarith [h6, h5]
  have h22 : a * b - 1 = 2 * (a + b) - 1 := by
    have h21' : a * b = 2 * (a + b) := by
      linarith
    linarith [h21']
  have h23 : c = (a + b) / (2 * (a + b) - 1) := by
    rw [h4]
    rw [h22]
  have h10 : (a + b) / (2 * (a + b) - 1) ≤ (8 / 15) := by
    have h11 : a + b ≥ 8 := h7
    have h12 : 2 * (a + b) - 1 > 0 := by
      nlinarith [sq_nonneg (a - b), h5, mul_pos ha hb]
    have h13 : (a + b) / (2 * (a + b) - 1) ≤ (8 / 15) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h11]
    linarith
  linarith [h23, h10]