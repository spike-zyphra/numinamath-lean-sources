import Mathlib

open Real Set

theorem inequalities_3241 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h1 : a ^ 5 + b ^ 5 ≤ 1) (h2 : c ^ 5 + d ^ 5 ≤ 1) :
    a ^ 2 * c ^ 3 + b ^ 2 * d ^ 3 ≤ 1 := by

  have h3 : a ^ 2 * c ^ 3 ≤ (2 / 5) * a ^ 5 + (3 / 5) * c ^ 5 := by
    have h3 : 0 ≤ (2 / 5 : ℝ) * a ^ 5 + (3 / 5 : ℝ) * c ^ 5 - a ^ 2 * c ^ 3 := by
      have h4 : (2 / 5 : ℝ) * a ^ 5 + (3 / 5 : ℝ) * c ^ 5 - a ^ 2 * c ^ 3 =
          (1 / 5 : ℝ) * ( (a ^ 5) * 2 + (c ^ 5) * 3 - 5 * (a ^ 2 * c ^ 3) ) := by
        ring_nf
      rw [h4]
      have h5 : (a ^ 5) * 2 + (c ^ 5) * 3 - 5 * (a ^ 2 * c ^ 3) ≥ 0 := by
        have h3 : a ^ 5 ≥ 0 := by positivity
        have h4 : c ^ 5 ≥ 0 := by positivity
        have h5 : a ^ 2 * c ^ 3 ≥ 0 := by positivity
        nlinarith [sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a * c - c ^ 2), sq_nonneg (a * c ^ 2 - a ^ 2 * c), 
          sq_nonneg (a - c), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a * c ^ 2 - a ^ 2 * c), 
          sq_nonneg (a ^ 2 - a * c), sq_nonneg (c ^ 2 - a * c), 
          sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a ^ 2 * c - a * c ^ 2), 
          mul_nonneg ha hc, 
          mul_nonneg (show (0 : ℝ) ≤ a ^ 2 by positivity) (show (0 : ℝ) ≤ c ^ 2 by positivity), 
          mul_nonneg (show (0 : ℝ) ≤ a ^ 2 by positivity) hc, 
          mul_nonneg ha (show (0 : ℝ) ≤ c ^ 2 by positivity), 
          sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a * c - a ^ 2), sq_nonneg (a * c - c ^ 2)]
      have h6 : (1 / 5 : ℝ) * ((a ^ 5) * 2 + (c ^ 5) * 3 - 5 * (a ^ 2 * c ^ 3)) ≥ 0 := by
        apply mul_nonneg
        norm_num
        linarith
      linarith
    linarith

  have h4 : b ^ 2 * d ^ 3 ≤ (2 / 5) * b ^ 5 + (3 / 5) * d ^ 5 := by
    have h4 : 0 ≤ (2 / 5 : ℝ) * b ^ 5 + (3 / 5 : ℝ) * d ^ 5 - b ^ 2 * d ^ 3 := by
      have h5 : (2 / 5 : ℝ) * b ^ 5 + (3 / 5 : ℝ) * d ^ 5 - b ^ 2 * d ^ 3 =
          (1 / 5 : ℝ) * ( (b ^ 5) * 2 + (d ^ 5) * 3 - 5 * (b ^ 2 * d ^ 3) ) := by
        ring_nf
      rw [h5]
      have h5 : (b ^ 5) * 2 + (d ^ 5) * 3 - 5 * (b ^ 2 * d ^ 3) ≥ 0 := by
        have h3 : b ^ 5 ≥ 0 := by positivity
        have h4 : d ^ 5 ≥ 0 := by positivity
        have h5 : b ^ 2 * d ^ 3 ≥ 0 := by positivity
        nlinarith [sq_nonneg (b ^ 2 - d ^ 2), sq_nonneg (b * d - d ^ 2), sq_nonneg (b * d ^ 2 - b ^ 2 * d), 
          sq_nonneg (b - d), sq_nonneg (b ^ 2 - d ^ 2), sq_nonneg (b * d ^ 2 - b ^ 2 * d), 
          sq_nonneg (b ^ 2 - b * d), sq_nonneg (d ^ 2 - b * d), 
          sq_nonneg (b ^ 2 - d ^ 2), sq_nonneg (b ^ 2 * d - b * d ^ 2), 
          mul_nonneg hb hd, 
          mul_nonneg (show (0 : ℝ) ≤ b ^ 2 by positivity) (show (0 : ℝ) ≤ d ^ 2 by positivity), 
          mul_nonneg (show (0 : ℝ) ≤ b ^ 2 by positivity) hd, 
          mul_nonneg hb (show (0 : ℝ) ≤ d ^ 2 by positivity), 
          sq_nonneg (b ^ 2 - d ^ 2), sq_nonneg (b * d - b ^ 2), sq_nonneg (b * d - d ^ 2)]
      have h6 : (1 / 5 : ℝ) * ((b ^ 5) * 2 + (d ^ 5) * 3 - 5 * (b ^ 2 * d ^ 3)) ≥ 0 := by
        apply mul_nonneg
        norm_num
        linarith
      linarith
    linarith

  have h5 : a ^ 2 * c ^ 3 + b ^ 2 * d ^ 3 ≤ (2 / 5) * a ^ 5 + (3 / 5) * c ^ 5 + (2 / 5) * b ^ 5 + (3 / 5) * d ^ 5 := by
    linarith [h3, h4]

  have h6 : (2 / 5) * a ^ 5 + (3 / 5) * c ^ 5 + (2 / 5) * b ^ 5 + (3 / 5) * d ^ 5 ≤ 1 := by
    nlinarith [h1, h2]

  linarith [h5, h6]