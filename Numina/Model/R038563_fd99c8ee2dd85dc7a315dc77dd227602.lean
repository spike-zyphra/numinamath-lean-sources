import Mathlib

open Real

theorem inequalities_254387 (a : ℝ) (ha : 0 < a) :
    (∀ x y : ℝ, 0 < x → 0 < y → sqrt x + sqrt y ≤ a * sqrt (x + y)) ↔
    a ≥ sqrt 2 := by
  constructor
  · -- First implication: ∀ x y > 0, sqrt x + sqrt y ≤ a sqrt (x+y) → a ≥ sqrt 2
    intro h
    have h1 := h 1 1 (by norm_num) (by norm_num)
    have h2 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
    have h3 : sqrt (1 + 1 : ℝ) = sqrt (2 : ℝ) := by norm_num
    rw [h2] at h1
    rw [h3] at h1
    have h4 : 2 ≤ a * sqrt (2 : ℝ) := by
      nlinarith
    by_contra h'
    push_neg at h'
    have h5 : sqrt (2 : ℝ) > 0 := by positivity
    have h6 : a * sqrt (2 : ℝ) < (sqrt (2 : ℝ)) * sqrt (2 : ℝ) := by
      nlinarith [h', Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), h5]
    have h7 : (sqrt (2 : ℝ)) * sqrt (2 : ℝ) = (2 : ℝ) := by
      calc
        (sqrt (2 : ℝ)) * sqrt (2 : ℝ) = (sqrt (2 : ℝ)) ^ 2 := by ring
        _ = (2 : ℝ) := by
          rw [Real.sq_sqrt]
          norm_num
    have h8 : a * sqrt (2 : ℝ) < (2 : ℝ) := by
      linarith [h6, h7]
    linarith [h4, h8]
  · -- Second implication: a ≥ sqrt 2 → ∀ x y > 0, sqrt x + sqrt y ≤ a sqrt (x+y)
    intro ha x y hx hy
    have h1 : sqrt x + sqrt y ≥ 0 := by positivity
    have h4 : sqrt (x + y) ≥ 0 := by positivity
    have h2 : (sqrt x + sqrt y) ^ 2 ≤ 2 * (x + y) := by
      have h3 : (sqrt x + sqrt y) ^ 2 = (x) + (y) + 2 * (sqrt x * sqrt y) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
      have h8 : (x : ℝ) + (y : ℝ) + 2 * (sqrt x * sqrt y) ≤ 2 * (x + y) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), sq_nonneg (sqrt x - sqrt y), Real.sqrt_nonneg x, Real.sqrt_nonneg y, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
      rw [h3]
      all_goals nlinarith
    have h5 : sqrt x + sqrt y ≤ sqrt (2) * sqrt (x + y) := by
      have h11 : (sqrt (2) * sqrt (x + y)) ^ 2 = 2 * (x + y) := by
        calc
          (sqrt (2) * sqrt (x + y)) ^ 2 = (sqrt (2 : ℝ)) ^ 2 * (sqrt (x + y : ℝ)) ^ 2 := by ring
          _ = (2 : ℝ) * (x + y) := by
            have h12 : (sqrt (2 : ℝ)) ^ 2 = (2 : ℝ) := by
              rw [Real.sq_sqrt]
              norm_num
            have h13 : (sqrt (x + y : ℝ)) ^ 2 = (x + y : ℝ) := by
              rw [Real.sq_sqrt]
              linarith
            rw [h12, h13]
      have h7 : (sqrt x + sqrt y) ^ 2 ≤ (sqrt (2) * sqrt (x + y)) ^ 2 := by
        nlinarith [h2, h11]
      have h8 : sqrt x + sqrt y ≥ 0 := by positivity
      have h9 : sqrt (2) * sqrt (x + y) ≥ 0 := by positivity
      nlinarith [h7, Real.sq_sqrt (show (0 : ℝ) ≤ (x) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (y) by linarith), h8, h9, Real.sqrt_nonneg (2), Real.sqrt_nonneg (x + y)]
    have h6 : sqrt (2) ≤ a := by
      nlinarith [Real.sqrt_nonneg 2, ha, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h7 : sqrt (2) * sqrt (x + y) ≤ a * sqrt (x + y) := by
      have h8 : sqrt (x + y) ≥ 0 := by positivity
      nlinarith [h6, h8]
    linarith [h5, h7]