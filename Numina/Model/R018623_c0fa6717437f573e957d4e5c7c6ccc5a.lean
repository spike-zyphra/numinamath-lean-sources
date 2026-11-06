import Mathlib

open Real

theorem inequalities_112241 (x : ℝ) :
    (sqrt (x^2 + 1) + 2^x) / (sqrt (x^2 + 1) + 2^(x + 1)) +
    (sqrt (x^2 + 2) + 3^(2 * x)) / (sqrt (x^2 + 2) + 3^(2 * x + 1)) +
    (sqrt (x^2 + 3) + 6^(3 * x)) / (sqrt (x^2 + 3) + 6^(3 * x + 1)) > 1 := by

  have h1 : (2 : ℝ) ^ (x + 1 : ℝ) = (2 : ℝ) * (2 : ℝ) ^ x := by
    rw [Real.rpow_add]
    ring_nf
    all_goals norm_num

  have h3 : (3 : ℝ) ^ (2 * x + 1 : ℝ) = (3 : ℝ) * (3 : ℝ) ^ (2 * x : ℝ) := by
    rw [show 2 * x + 1 = (2 * x : ℝ) + (1 : ℝ) by ring]
    rw [Real.rpow_add]
    ring_nf
    all_goals norm_num

  have h4 : (6 : ℝ) ^ (3 * x + 1 : ℝ) = (6 : ℝ) * (6 : ℝ) ^ (3 * x : ℝ) := by
    rw [show 3 * x + 1 = (3 * x : ℝ) + (1 : ℝ) by ring]
    rw [Real.rpow_add]
    ring_nf
    all_goals norm_num

  rw [h1] at *
  rw [h3] at *
  rw [h4] at *

  have h5 : sqrt (x^2 + 1) ≥ 0 := by positivity
  have h6 : sqrt (x^2 + 2) ≥ 0 := by positivity
  have h7 : sqrt (x^2 + 3) ≥ 0 := by positivity

  have h8 : sqrt (x^2 + 1) + (2 * (2 : ℝ) ^ x) > 0 := by
    have h9 : sqrt (x^2 + 1) > 0 := by
      have h10 : x^2 + 1 > 0 := by
        nlinarith [sq_nonneg x]
      have h11 : sqrt (x^2 + 1) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      linarith
    have h12 : (2 * (2 : ℝ) ^ x) > 0 := by
      have h13 : (2 : ℝ) ^ x > 0 := by positivity
      nlinarith
    linarith [h9, h12]

  have h9 : sqrt (x^2 + 2) + (3 * (3 : ℝ) ^ (2 * x) ) > 0 := by
    have h10 : sqrt (x^2 + 2) > 0 := by
      have h11 : x^2 + 2 > 0 := by
        nlinarith [sq_nonneg x]
      have h12 : sqrt (x^2 + 2) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      linarith
    have h11 : (3 * (3 : ℝ) ^ (2 * x) ) > 0 := by
      have h12 : (3 : ℝ) ^ (2 * x) > 0 := by positivity
      nlinarith
    linarith [h10, h11]

  have h10 : sqrt (x^2 + 3) + (6 * (6 : ℝ) ^ (3 * x) ) > 0 := by
    have h11 : sqrt (x^2 + 3) > 0 := by
      have h12 : x^2 + 3 > 0 := by
        nlinarith [sq_nonneg x]
      have h13 : sqrt (x^2 + 3) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      linarith
    have h12 : (6 * (6 : ℝ) ^ (3 * x) ) > 0 := by
      have h13 : (6 : ℝ) ^ (3 * x) > 0 := by positivity
      nlinarith
    linarith [h11, h12]

  have h11 : (sqrt (x^2 + 1) + (2 : ℝ) ^ x) / (sqrt (x^2 + 1) + (2 * (2 : ℝ) ^ x)) > 1 / 2 := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith [Real.sqrt_nonneg (x^2 + 1), Real.sq_sqrt (show 0 ≤ x^2 + 1 by nlinarith), Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) x]

  have h12 : (sqrt (x^2 + 2) + (3 : ℝ) ^ (2 * x)) / (sqrt (x^2 + 2) + (3 * (3 : ℝ) ^ (2 * x)) ) > 1 / 3 := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith [Real.sqrt_nonneg (x^2 + 2), Real.sq_sqrt (show 0 ≤ x^2 + 2 by nlinarith), Real.rpow_pos_of_pos (show (0 : ℝ) < 3 by norm_num) (2 * x)]

  have h13 : (sqrt (x^2 + 3) + (6 : ℝ) ^ (3 * x)) / (sqrt (x^2 + 3) + (6 * (6 : ℝ) ^ (3 * x)) ) > 1 / 6 := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith [Real.sqrt_nonneg (x^2 + 3), Real.sq_sqrt (show 0 ≤ x^2 + 3 by nlinarith), Real.rpow_pos_of_pos (show (0 : ℝ) < 6 by norm_num) (3 * x)]

  linarith [h11, h12, h13]