import Mathlib

open Real

theorem inequalities_317410 (a : ℝ) :
    (∀ x y : ℝ, x > 0 → y > 0 → sqrt x + sqrt y ≤ a * sqrt (x + y)) ↔
    a ≥ sqrt 2 := by
  constructor
  · -- Assume that ∀ x > 0, y > 0, sqrt x + sqrt y ≤ a * sqrt (x + y)
    intro h
    have h1 := h 1 1 (by norm_num) (by norm_num)
    have h2 : sqrt (1 : ℝ) = (1 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : sqrt (1 + (1 : ℝ)) = sqrt 2 := by
      norm_num
    rw [h2] at h1
    rw [h3] at h1
    have h4 : (2 : ℝ) ≤ a * sqrt 2 := by
      nlinarith [h1]
    have h5 : a ≥ sqrt 2 := by
      nlinarith [h4, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    linarith
  · -- Assume a ≥ sqrt 2, need to prove ∀ x y : ℝ, x > 0 → y > 0 → sqrt x + sqrt y ≤ a * sqrt (x + y)
    intro ha x y hx hy
    have h1 : sqrt x + sqrt y ≤ Real.sqrt 2 * Real.sqrt (x + y) := by
      have h2 : (sqrt x + sqrt y) ^ 2 ≤ (Real.sqrt 2 * Real.sqrt (x + y)) ^ 2 := by
        have h3 : (sqrt x + sqrt y) ^ 2 = (sqrt x) ^ 2 + (sqrt y) ^ 2 + 2 * (sqrt x * sqrt y) := by
          ring
        have h4 : (Real.sqrt 2 * Real.sqrt (x + y)) ^ 2 = (Real.sqrt 2) ^ 2 * (Real.sqrt (x + y)) ^ 2 := by
          ring
        rw [h3, h4]
        have h5 : (sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
        have h6 : (sqrt y) ^ 2 = y := Real.sq_sqrt (by linarith)
        have h7 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
        have h8 : (Real.sqrt (x + y)) ^ 2 = x + y := Real.sq_sqrt (show (0 : ℝ) ≤ x + y by linarith)
        rw [h5, h6, h7, h8]
        nlinarith [sq_nonneg (sqrt x - sqrt y), Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg (x + y), Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (y : ℝ) by linarith), sq_nonneg (x - y), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
      have h9 : sqrt x + sqrt y ≥ 0 := by
        have h10 : sqrt x ≥ 0 := Real.sqrt_nonneg x
        have h11 : sqrt y ≥ 0 := Real.sqrt_nonneg y
        linarith
      have h10 : Real.sqrt 2 * Real.sqrt (x + y) ≥ 0 := by
        have h11 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
        have h12 : Real.sqrt (x + y) ≥ 0 := Real.sqrt_nonneg (x + y)
        nlinarith
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (x + y), h2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (x + y : ℝ) by linarith), sq_nonneg (sqrt x + sqrt y - Real.sqrt 2 * Real.sqrt (x + y))]
    have h2 : Real.sqrt 2 * Real.sqrt (x + y) ≤ a * Real.sqrt (x + y) := by
      have h3 : a ≥ Real.sqrt 2 := by linarith
      have h4 : Real.sqrt (x + y) ≥ 0 := Real.sqrt_nonneg (x + y)
      nlinarith [h3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    linarith [h1, h2]