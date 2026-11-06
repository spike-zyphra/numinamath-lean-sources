import Mathlib

theorem algebra_251935 (x p : ℝ) (hx : x^2 - p ≥ 0) (hxp : x^2 - 1 ≥ 0)
    (h : Real.sqrt (x^2 - p) + 2 * Real.sqrt (x^2 - 1) = x) :
    x = (4 - p) / Real.sqrt (8 * (2 - p)) := by

  have h1 : 0 ≤ x := by
    have h2 : Real.sqrt (x^2 - p) ≥ 0 := Real.sqrt_nonneg (x^2 - p)
    have h3 : Real.sqrt (x^2 - 1) ≥ 0 := Real.sqrt_nonneg (x^2 - 1)
    nlinarith [sq_nonneg x, h2, h3, h]

  have h2 : Real.sqrt (x^2 - p) = x - 2 * Real.sqrt (x^2 - 1) := by linarith

  have h3 : (Real.sqrt (x^2 - p)) ^ 2 = (x - 2 * Real.sqrt (x^2 - 1)) ^ 2 := by
    rw [h2]

  have h4 : (Real.sqrt (x^2 - p)) ^ 2 = x^2 - p := by
    rw [Real.sq_sqrt]
    linarith

  have h5 : (x - 2 * Real.sqrt (x^2 - 1)) ^ 2 = x^2 - 4 * x * Real.sqrt (x^2 - 1) + 4 * (x^2 - 1) := by
    nlinarith [Real.sqrt_nonneg (x^2 - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x^2 - 1 by linarith)]

  rw [h4, h5] at h3

  have h6 : 4 * x * Real.sqrt (x^2 - 1) = 4 * x^2 + p - 4 := by
    nlinarith [Real.sqrt_nonneg (x^2 - 1)]

  have h7 : (4 * x * Real.sqrt (x^2 - 1)) ^ 2 = (4 * x^2 + p - 4) ^ 2 := by
    rw [h6]

  have h8 : (4 * x * Real.sqrt (x^2 - 1)) ^ 2 = 16 * x^2 * (x^2 - 1) := by
    calc
      (4 * x * Real.sqrt (x^2 - 1)) ^ 2
        = 16 * x^2 * (Real.sqrt (x^2 - 1) ^ 2) := by
          ring_nf
      _ = 16 * x^2 * (x^2 - 1) := by
        rw [Real.sq_sqrt (by linarith)]

  have h9 : (4 * x^2 + p - 4) ^ 2 = 16 * x^4 + 8 * x^2 * (p - 4) + (p - 4) ^ 2 := by
    ring

  rw [h8, h9] at h7

  have h10 : (8 * p - 16) * x^2 + (p - 4) ^ 2 = 0 := by
    nlinarith

  have hp1 : 2 - p > 0 := by
    nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (p - 4), sq_nonneg (x * Real.sqrt (x^2 - 1)), sq_nonneg (4 - p), sq_nonneg (x^2 - 4), sq_nonneg (x^2 - p), Real.sqrt_nonneg (x^2 - 1), Real.sqrt_nonneg (x^2 - p)]

  have h14 : x^2 = (4 - p) ^ 2 / (8 * (2 - p)) := by
    have h15 : (p - 4) ^ 2 = 8 * (2 - p) * x^2 := by
      nlinarith
    have h16 : (p - 4) ^ 2 = (4 - p) ^ 2 := by
      ring
    rw [h16] at h15
    have hp2 : (2 - p) ≠ 0 := by
      linarith
    field_simp at *
    nlinarith

  have h18 : x = Real.sqrt (x^2) := by
    rw [Real.sqrt_sq (show 0 ≤ x by linarith [h1])]

  have h19 : Real.sqrt (x^2) = (4 - p) / Real.sqrt (8 * (2 - p)) := by
    have h20 : x^2 = (4 - p) ^ 2 / (8 * (2 - p)) := h14
    have h21 : Real.sqrt (x^2) = Real.sqrt ((4 - p) ^ 2 / (8 * (2 - p))) := by
      rw [h20]
    rw [h21]
    have h22 : Real.sqrt ((4 - p) ^ 2 / (8 * (2 - p))) = Real.sqrt ((4 - p) ^ 2) / Real.sqrt (8 * (2 - p)) := by
      rw [Real.sqrt_div (by
        have hp2 : 8 * (2 - p) > 0 := by nlinarith
        positivity
      )]
    rw [h22]
    have h23 : Real.sqrt ((4 - p) ^ 2) = (4 - p : ℝ) := by
      rw [Real.sqrt_sq (show (0 : ℝ) ≤ 4 - p by nlinarith [hp1]
      )]
    rw [h23]

  rw [h18, h19]