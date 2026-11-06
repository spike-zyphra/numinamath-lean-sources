import Mathlib

theorem inequalities_123638 (a b c d e : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hd : 1 < d) (he : 1 < e) :
    20 ≤ a ^ 2 / (c - 1) + b ^ 2 / (d - 1) + c ^ 2 / (e - 1) + d ^ 2 / (a - 1) + e ^ 2 / (b - 1) := by
  have h1 : 0 < c - 1 := by linarith
  have h2 : 0 < d - 1 := by linarith
  have h3 : 0 < e - 1 := by linarith
  have h4 : 0 < a - 1 := by linarith
  have h5 : 0 < b - 1 := by linarith

  have h6 : a ^ 2 / (c - 1) + 4 * (c - 1) ≥ 4 * a := by
    have h7 : 0 < c - 1 := h1
    have h8 : a ^ 2 / (c - 1) + 4 * (c - 1) - 4 * a ≥ 0 := by
      have h9 : a ^ 2 / (c - 1) + 4 * (c - 1) - 4 * a = (a ^ 2 - 4 * a * (c - 1) + 4 * (c - 1) ^ 2) / (c - 1) := by
        field_simp
        ring
      rw [h9] at *
      apply div_nonneg
      nlinarith [sq_nonneg (a - 2 * (c - 1))]
      all_goals linarith
    linarith

  have h7 : b ^ 2 / (d - 1) + 4 * (d - 1) ≥ 4 * b := by
    have h8 : 0 < d - 1 := h2
    have h9 : b ^ 2 / (d - 1) + 4 * (d - 1) - 4 * b ≥ 0 := by
      have h10 : b ^ 2 / (d - 1) + 4 * (d - 1) - 4 * b = (b ^ 2 - 4 * b * (d - 1) + 4 * (d - 1) ^ 2) / (d - 1) := by
        field_simp
        ring
      rw [h10] at *
      apply div_nonneg
      nlinarith [sq_nonneg (b - 2 * (d - 1))]
      all_goals linarith
    linarith

  have h8 : c ^ 2 / (e - 1) + 4 * (e - 1) ≥ 4 * c := by
    have h9 : 0 < e - 1 := h3
    have h10 : c ^ 2 / (e - 1) + 4 * (e - 1) - 4 * c ≥ 0 := by
      have h11 : c ^ 2 / (e - 1) + 4 * (e - 1) - 4 * c = (c ^ 2 - 4 * c * (e - 1) + 4 * (e - 1) ^ 2) / (e - 1) := by
        field_simp
        ring
      rw [h11] at *
      apply div_nonneg
      nlinarith [sq_nonneg (c - 2 * (e - 1))]
      all_goals linarith
    linarith

  have h9 : d ^ 2 / (a - 1) + 4 * (a - 1) ≥ 4 * d := by
    have h10 : 0 < a - 1 := h4
    have h11 : d ^ 2 / (a - 1) + 4 * (a - 1) - 4 * d ≥ 0 := by
      have h12 : d ^ 2 / (a - 1) + 4 * (a - 1) - 4 * d = (d ^ 2 - 4 * d * (a - 1) + 4 * (a - 1) ^ 2) / (a - 1) := by
        field_simp
        ring
      rw [h12] at *
      apply div_nonneg
      nlinarith [sq_nonneg (d - 2 * (a - 1))]
      all_goals linarith
    linarith

  have h10 : e ^ 2 / (b - 1) + 4 * (b - 1) ≥ 4 * e := by
    have h11 : 0 < b - 1 := h5
    have h12 : e ^ 2 / (b - 1) + 4 * (b - 1) - 4 * e ≥ 0 := by
      have h13 : e ^ 2 / (b - 1) + 4 * (b - 1) - 4 * e = (e ^ 2 - 4 * e * (b - 1) + 4 * (b - 1) ^ 2) / (b - 1) := by
        field_simp
        ring
      rw [h13] at *
      apply div_nonneg
      nlinarith [sq_nonneg (e - 2 * (b - 1))]
      all_goals linarith
    linarith

  have h11 : a ^ 2 / (c - 1) + b ^ 2 / (d - 1) + c ^ 2 / (e - 1) + d ^ 2 / (a - 1) + e ^ 2 / (b - 1) ≥ 20 := by
    have h12 : a ^ 2 / (c - 1) + b ^ 2 / (d - 1) + c ^ 2 / (e - 1) + d ^ 2 / (a - 1) + e ^ 2 / (b - 1) + 4 * ((c - 1) + (d - 1) + (e - 1) + (a - 1) + (b - 1)) ≥ 4 * (a + b + c + d + e) := by
      linarith [h6, h7, h8, h9, h10]
    nlinarith

  nlinarith