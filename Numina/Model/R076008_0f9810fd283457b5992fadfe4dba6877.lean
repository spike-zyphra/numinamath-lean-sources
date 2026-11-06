import Mathlib

open Real

theorem inequalities_117757 (a : ℝ) :
    (∀ x y : ℝ, x > 0 → y > 0 → sqrt x + sqrt y ≤ a * sqrt (x + y)) ↔
    a ≥ sqrt 2 := by
  constructor
  · -- Assume the inequality holds for all positive x, y, prove a ≥ sqrt(2)
    intro h
    have h11 := h 1 1 (by norm_num) (by norm_num)
    have h2 : sqrt 1 = 1 := Real.sqrt_one
    have h3 : sqrt (1 + 1 : ℝ) = sqrt 2 := by
      norm_num
    rw [h2, h3] at h11
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (1 : ℝ) by norm_num), h11]
  · -- Assume a ≥ sqrt(2), prove the inequality holds for all positive x, y
    intro ha x y hx hy
    have h1 : (sqrt x + sqrt y) ^ 2 ≤ 2 * (x + y) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith),
        Real.sqrt_nonneg x, Real.sqrt_nonneg y,
        sq_nonneg (sqrt x - sqrt y)]
    have h3 : sqrt x + sqrt y ≤ sqrt 2 * sqrt (x + y) := by
      have h4 : (sqrt x + sqrt y) ^ 2 ≤ 2 * (x + y) := h1
      have h5 : (sqrt x + sqrt y) ^ 2 ≤ (sqrt 2 * sqrt (x + y)) ^ 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (x + y : ℝ) by linarith), Real.sqrt_nonneg 2, Real.sqrt_nonneg (x + y)]
      nlinarith [mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (x + y)), Real.sqrt_nonneg (sqrt x + sqrt y), Real.sqrt_nonneg (sqrt 2 * sqrt (x + y)), h5, Real.sq_sqrt (show 0 ≤ (x + y : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    have h2 : sqrt 2 * sqrt (x + y) ≤ a * sqrt (x + y) := by
      have h3 : 0 ≤ (x + y : ℝ) := by linarith
      have h4 : sqrt (x + y) ≥ 0 := Real.sqrt_nonneg (x + y)
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), ha, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (x + y : ℝ) by linarith)]
    linarith [h3, h2, Real.sqrt_pos.mpr (show (0 : ℝ) < (x + y : ℝ) by nlinarith), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]