import Mathlib

theorem inequalities_603885 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    1 / (1 + a ^ 3) + 1 / (1 + b ^ 3) + 1 / (1 + c ^ 3) + 1 / (1 + d ^ 3) ≤ 256 / 65 := by

  have ha1 : a < 1 := by
    nlinarith [hb, hc, hd]

  have hb1 : b < 1 := by
    nlinarith [ha, hc, hd]

  have hc1 : c < 1 := by
    nlinarith [ha, hb, hd]

  have hd1 : d < 1 := by
    nlinarith [ha, hb, hc]

  have h2 : 1 / (1 + a ^ 3) ≤ 64 / 65 - 768 / 4225 * (a - 1 / 4) := by
    have h3 : 0 < (1 + a ^ 3 : ℝ) := by
      positivity
    have h4 : 1 / (1 + a^3) - (64 / 65 - 768 / 4225 * (a - 1 / 4)) ≤ 0 := by
      have h5 : 1 / (1 + a^3) - (64 / 65 - 768 / 4225 * (a - 1 / 4)) =
          (65 * 4225 * (1) - 64 * 4225 * (1 + a^3) + 768 * 65 * (a - 1/4) * (1 + a^3)) / (65 * 4225 * (1 + a^3) ) := by
        field_simp
        ring
      rw [h5]
      have h6 : 65 * 4225 * (1 + a ^ 3) > 0 := by positivity
      have h7 : 65 * 4225 * (1) - 64 * 4225 * (1 + a ^ 3) + 768 * 65 * (a - 1 / 4) * (1 + a ^ 3) ≤ 0 := by
        nlinarith [sq_nonneg (a - 1 / 4), sq_nonneg (a ^ 2 - 1 / 16), sq_nonneg (a - 1 / 2), sq_nonneg (a * (a - 1 / 4)), sq_nonneg ((a ^ 2) - a / 2), mul_pos ha (show 0 < 1 - a by linarith), sq_nonneg (a ^ 2 - 1 / 4), sq_nonneg (a ^ 3 - (1 / 4) ^ 3)]
      apply div_nonpos_of_nonpos_of_nonneg h7 (show (0 : ℝ) ≤ 65 * 4225 * (1 + a ^ 3) by positivity)
    linarith

  have h3 : 1 / (1 + b ^ 3) ≤ 64 / 65 - 768 / 4225 * (b - 1 / 4) := by
    have h3 : 0 < (1 + b ^ 3 : ℝ) := by
      positivity
    have h4 : 1 / (1 + b^3) - (64 / 65 - 768 / 4225 * (b - 1 / 4)) ≤ 0 := by
      have h5 : 1 / (1 + b^3) - (64 / 65 - 768 / 4225 * (b - 1 / 4)) =
          (65 * 4225 * (1) - 64 * 4225 * (1 + b^3) + 768 * 65 * (b - 1/4) * (1 + b^3)) / (65 * 4225 * (1 + b^3) ) := by
        field_simp
        ring
      rw [h5]
      have h6 : 65 * 4225 * (1 + b ^ 3) > 0 := by positivity
      have h7 : 65 * 4225 * (1) - 64 * 4225 * (1 + b ^ 3) + 768 * 65 * (b - 1 / 4) * (1 + b ^ 3) ≤ 0 := by
        nlinarith [sq_nonneg (b - 1 / 4), sq_nonneg (b ^ 2 - 1 / 16), sq_nonneg (b - 1 / 2), sq_nonneg (b * (b - 1 / 4)), sq_nonneg ((b ^ 2) - b / 2), mul_pos hb (show 0 < 1 - b by linarith), sq_nonneg (b ^ 2 - 1 / 4), sq_nonneg (b ^ 3 - (1 / 4) ^ 3)]
      apply div_nonpos_of_nonpos_of_nonneg h7 (show (0 : ℝ) ≤ 65 * 4225 * (1 + b ^ 3) by positivity)
    linarith

  have h4 : 1 / (1 + c ^ 3) ≤ 64 / 65 - 768 / 4225 * (c - 1 / 4) := by
    have h3 : 0 < (1 + c ^ 3 : ℝ) := by
      positivity
    have h4 : 1 / (1 + c^3) - (64 / 65 - 768 / 4225 * (c - 1 / 4)) ≤ 0 := by
      have h5 : 1 / (1 + c^3) - (64 / 65 - 768 / 4225 * (c - 1 / 4)) =
          (65 * 4225 * (1) - 64 * 4225 * (1 + c^3) + 768 * 65 * (c - 1/4) * (1 + c^3)) / (65 * 4225 * (1 + c^3) ) := by
        field_simp
        ring
      rw [h5]
      have h6 : 65 * 4225 * (1 + c ^ 3) > 0 := by positivity
      have h7 : 65 * 4225 * (1) - 64 * 4225 * (1 + c ^ 3) + 768 * 65 * (c - 1 / 4) * (1 + c ^ 3) ≤ 0 := by
        nlinarith [sq_nonneg (c - 1 / 4), sq_nonneg (c ^ 2 - 1 / 16), sq_nonneg (c - 1 / 2), sq_nonneg (c * (c - 1 / 4)), sq_nonneg ((c ^ 2) - c / 2), mul_pos hc (show 0 < 1 - c by linarith), sq_nonneg (c ^ 2 - 1 / 4), sq_nonneg (c ^ 3 - (1 / 4) ^ 3)]
      apply div_nonpos_of_nonpos_of_nonneg h7 (show (0 : ℝ) ≤ 65 * 4225 * (1 + c ^ 3) by positivity)
    linarith

  have h5 : 1 / (1 + d ^ 3) ≤ 64 / 65 - 768 / 4225 * (d - 1 / 4) := by
    have h3 : 0 < (1 + d ^ 3 : ℝ) := by
      positivity
    have h4 : 1 / (1 + d^3) - (64 / 65 - 768 / 4225 * (d - 1 / 4)) ≤ 0 := by
      have h5 : 1 / (1 + d^3) - (64 / 65 - 768 / 4225 * (d - 1 / 4)) =
          (65 * 4225 * (1) - 64 * 4225 * (1 + d^3) + 768 * 65 * (d - 1/4) * (1 + d^3)) / (65 * 4225 * (1 + d^3) ) := by
        field_simp
        ring
      rw [h5]
      have h6 : 65 * 4225 * (1 + d ^ 3) > 0 := by positivity
      have h7 : 65 * 4225 * (1) - 64 * 4225 * (1 + d ^ 3) + 768 * 65 * (d - 1 / 4) * (1 + d ^ 3) ≤ 0 := by
        nlinarith [sq_nonneg (d - 1 / 4), sq_nonneg (d ^ 2 - 1 / 16), sq_nonneg (d - 1 / 2), sq_nonneg (d * (d - 1 / 4)), sq_nonneg ((d ^ 2) - d / 2), mul_pos hd (show 0 < 1 - d by linarith), sq_nonneg (d ^ 2 - 1 / 4), sq_nonneg (d ^ 3 - (1 / 4) ^ 3)]
      apply div_nonpos_of_nonpos_of_nonneg h7 (show (0 : ℝ) ≤ 65 * 4225 * (1 + d ^ 3) by positivity)
    linarith

  have h7 : 1 / (1 + a ^ 3) + 1 / (1 + b ^ 3) + 1 / (1 + c ^ 3) + 1 / (1 + d ^ 3) ≤ 256 / 65 := by
    nlinarith [h2, h3, h4, h5, show (a - 1 / 4 + b - 1 / 4 + c - 1 / 4 + d - 1 / 4) = 0 by
      nlinarith
    ]
  linarith